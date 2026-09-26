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
- An A/B or rung row names the model id each arm resolved to, read from the
  subagent transcript, not the variant's alias (the 40b CARRIER "opus" arm
  ran on Opus 4.8 — `notes/harness/incidents.md` 2026-09-26).
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
| 2026-07-17 | Phase34 Layer-BB chapter extension (`ed707a77`) | fable | pre-build recon REFUTED an R0-era route claim before any Lean built on it | The phase note's Layer-BB route ("the landed standard-basis witness vectors are ±T of coordinate-point pairs") rode from R0 through five clean slices unchecked — no gate reads route prose. The commissioned chapter-extension recon checked it against the JJ p. 581 entry table + the minor formula and refuted it (pure-moment basis vectors are not T-images), rerouting via the Whiteley change-of-coordinates remark. Second firing of the Phase-32 pre-build-recon guard; the coordinator's prompt had flagged the claim as unverified, which routed it to a check instead of a transcription. |
| 2026-07-17 | Phase34 Layer-BB first Lean slice (killed; landed `b6454b02` on resume) | sonnet | killed by an API stream error pre-work; same-agent resume landed clean | The dispatch died on "Stream idle timeout - no chunks received" before writing anything (tree clean, HEAD unmoved) — a new kill *cause* for the rescue-§3 shape (previously session/usage limits + user interrupts). Same-agent SendMessage resume with a fresh task statement landed the full slice clean; rung-pinned variant, no F5 drift. No salvage needed since nothing stranded. |
| 2026-07-18 | Phase34 BH witness-trio continuation (`43d5764f`) | sonnet | nested-Agent spawn attempt, blocked by hook, self-reported | Mid-task the agent tried to spawn an Explore subagent for mathlib research; the `block-nested-agent.sh` PreToolUse hook denied it mechanically and the agent did the research itself (`grep`/`lean_run_code`), landing clean. Zero tree impact; logged because the agent's own core forbids nested spawns and the hook (not the prose) is what held — same lesson as the sorry-commit hook: discipline that must survive long contexts belongs in hooks. |
| 2026-09-25 | Phase39 L0c-i pre-close chapter pass (`e316891f`; repaired in L0c-ii) | fable | gate-invisible deletion-hygiene miss caught in coordinator verification | L0c-i deleted three `fmlnote:` labels (`…pencil-conditional-bare`, `…pencil-nondegenerate-hub`, `…-nonhub`), folding their content into the `sec:pencil-nondegenerate` preamble; `blueprint/lint.sh` was green because it reads only `.tex`. The first label survived in a live Lean docstring (`pencil_conjecture_of_arms`, `Molecule/Pencil/Arms.lean`), its PROVISIONAL paragraph stale too. Caught by the coordinator's tree-wide grep of the deleted names, not by any gate; repaired in L0c-ii. The `hygiene` sweep covers every file kind — F12's shape, one level over. |
| 2026-09-25 | Phase40a Slice 1 floor weakening (`f648a6ac`; repaired in `deb1c82b`) | sonnet | 3 gate-invisible defects caught in coordinator diff-read | (1) Judged `lem:cycle-realization` "needs no change" from its generic statement; its proof still pinned the old `m ≤ d = k+1`. (2) Dropped the adjacent-pair `\uses` edge with no replacement; the new lemma was named only in `\texttt`. (3) Phase note claimed a `push_neg`→`push Not` fix to the recon hunk, which already read `push Not`. All folded into the next slice's prompt. Lesson: a restate check reads the node's proof body, not only its statement. |
| 2026-09-25 | Phase40a Slice 4 spike (landed via `2ec9fce2`) | opus ∥ fable | playbook deviation: user-requested top-rung A/B | Same read-only spike prompt to recon-opus and recon-fable, run in parallel. Both returned the same sorry-free general-(n,k) five-conjunct proof; the coordinator re-elaborated both (standard axioms). Cost: opus 172k tok/55 tools/12 min; fable 191k/41/13 min. Unique catches: opus, the landed generic form's total `hends` forces `E(G)=β` (load-bearing for BRIDGE); fable, B2's missing pin, the spanning form as a corollary, and a linter positive control. Parity at lower cost. One data point; the user chose a single opus for the 40a close. |
| 2026-09-26 | Phase40b CARRIER design-open (folded into the 40b open commit) | opus (resolved `claude-opus-4-8`) ∥ fable | playbook deviation: user-requested top-rung A/B design recon | Read-only CARRIER design recons, same prompt to recon-opus and recon-fable in parallel. Both converged on the β-headroom decision (`hcard` additive-successor `_of_card` triple, L0 untouched, not type-changing). Opus adopted as session top rung per the user's cost rule: opus ~242K tok/46 tools/19min vs fable ~336K/44/25min. Fable's uncurried-coords / single-`X0Attains`-def / new-chapter / lint-gate details folded into this open commit. Two MOTIVES questions recorded in `notes/Phase40b.md`: the exact `hcard` constant (6· vs 3·), and the headroom root-cause (split-off `e₀∉E(G)` vs BRIDGE consuming SPINE2's `hfresh`). |
| 2026-09-26 | Phase40b C2 `U`-open (f7a9ca1a → fix 8e672144) | sonnet → opus | gate-invisible defect caught in verification; shape deviation | All gates green, but the three existence lemmas took `(closedNbhd v).ncard = 3`, restricting them to 2-regular graphs, and the notes/blueprint called that "weaker than" the standing "at least three" (direction reversed). Cause: the coordinator prompt echoed the hand-off's "three members" without "at least" (F19). Caught by reading the landed statement; opus corrective generalized to `3 ≤ ncard` (a 3-subset) and swept the prose. Lesson: spell out quantifier direction in a scope-to-fit fallback hypothesis. |
| 2026-09-26 | Phase40c FLAT design recon (adopted in `55f7a0cb`) | opus ∥ fable | playbook deviation: user-requested top-rung A/B | Same compiler-checked read-only prompt, in parallel; both witnesses re-run by the coordinator (exit 0, no sorry). Opus: the complete route (exact (MC-4)(a), exact grade-1 motion equality, (MC-5)(i) proved) at 411k tok/130 tools/45 min. Fable: cone side, inequality half only, both surjections unspiked, (i) unproved, at 626k/82/87 min. Fable-only catches: pin-debt site precision, a `--cited-by` consumer map. Third A/B, and the first with a quality gap: opus ahead at lower cost. |
| 2026-09-26 | Phase40c FLAT build (`598f20ce`) | opus (recon resumed) | playbook deviation: a sorry-free spike landed as one build commit; F6-family auto-background, self-recovered | User-endorsed: with the recon's spike complete, FLAT's five-slice plan was pure overhead, so the recon agent was resumed to land the open and the whole build in two commits (F43). Its first `lake build` (a 34-module rebuild after a `Deficiency.lean` edit, ~30 min) passed the 600 s tool ceiling and auto-backgrounded; it waited with a timed foreground until-loop, started no second build, and self-reported. 627k tok/225 tools/61 min; full diff read, build + `lake lint` re-run clean. |

**Phase 39 (PENCIL) rows, 2026-07-24 → 09-17: 150 pruned at the phase close
(2026-09-25); the full rows are in git history at `e316891f`.** Profile, by
the exception column's own wording (a row can match several classes): 26 gate-
invisible defects caught in coordinator verification (aggregator orphans ×2,
an unsatisfiable carried hypothesis, a citation overclaim; twelve rows naming
a stale status surface — F17); 60 rows naming a coordinator-authored defect or
premise (F14, F19, F22, F38); 16 refuted predictions, pins or landed clauses
(F9, F10 and the research-arc F26–F38); 11 kills or resumes (spend limits, the
64k output cap, an API timeout — every one recovered by a same-agent resume,
rescue §3); 9 F6-family gate-mechanics instances (auto-background, Monitor
park, shell `timeout`/`| tail`, concurrent builds); 6 rung / trailer /
substitution drifts (F5); 6 playbook deviations (three user-adjudicated
parallel fan-outs, two rung substitutions — one user-adjudicated, one forced
by availability — and one declined resume). Every recurring class has a
Finding below; the one-off shapes (a subjectless commit message, a `git stash
-u` under live sibling drafts, a keepalive cron left armed) live only in the
pruned rows.



## Findings

(Distill recurring lessons here — one entry per lesson, rows cite it.
At phase close, promote stable entries into the coordinator command's
*Dispatch playbook* / CLAUDE.md and prune.)

**Phase-39 close grooming (2026-09-25).** The phase's 150 rows are pruned to
git history (profile under *Log*). Findings whose rule now lives in a manual
are stubbed below with the pointer, the F2–F4 shape: F5–F15, F17–F21, F26–F28,
F30, F39, F41, F42 — seven of them (F8, F9, F12, F14, F19, F41, F42) promoted
into the `/coordinate-phase` *Dispatch playbook* at this close. Kept in full:
F1 (a conditional promotion), F40 (an open tooling item, `check-roadmap-
cells.py`), and the research-arc findings F16, F22–F25, F29, F31–F38, whose
promotion target is `HARNESS.md`, which changes only in `/harness-review`
(due).

- **F1 — re-derive inventories at build time.** A recon's size/anchor
  estimate made before reading a file is a scheduling input, not a
  per-slice contract; mandating that each slice re-derive its own
  inventory (tree-wide grep, letter granularity) is what caught the
  Phase-29 undercount before anything broke. Flagged in
  `notes/Phase29.md` for promotion to `notes/CLAUDE.md` if a third
  `*-design.md` compression hits the same trap.
- **F2 — pinned exemplar = the prose S=1.** Promoted to the playbook
  (*Raising S* + the shaping-block list) 2026-07-09; pruned at the
  Phase-34 close (details in git history).
- **F3 — verification-mandate cost signature.** Promoted to the
  playbook (the cost-outlier bullet's benign-shape carve-out)
  2026-07-09; pruned at the Phase-34 close (details in git history).
- **F4 — continuation dispatch (same-arc resume).** Promoted to the
  playbook (step-3 *Continuation dispatch* note) 2026-07-10; pruned at
  the Phase-34 close (details in git history).
- **F5 — SendMessage-resume runs at the session model, not the dispatched
  rung.** Promoted: the command's *Pick the rung* (typed variants; resumes
  rung-stable) and steps 2/5, `notes/coordinate-phase-rescue.md` §3,
  `HARNESS.md` *Reproducibility*. Pruned at the Phase-39 close (the
  controlled-probe matrix is in git history at `e316891f`).
- **F6 — harness auto-backgrounding strands gate runs.** Promoted: both agent
  cores (foreground gates with the Bash `timeout` parameter; no
  `run_in_background`/Monitor; no shell `timeout` or pipe), rescue §2, the
  command's step-3 reminder line, `HARNESS.md` *Reproducibility*. Pruned at
  the Phase-39 close (instances in git history).
- **F7 — the internals tactic-golf phase runs clean at low rungs (Phase 36
  AUTOMATE).** Promoted: the tactic lessons to `TACTICS-GOLF.md` §7; the
  AUTOMATE-Z template ran as Phase 37. Pruned at the Phase-39 close.
- **F8 — a chart/WF-style predicate's conjuncts are unverified until something
  INSTANTIATES them (Phase 39 W5).** Promoted to the command's step-4
  satisfiability bullet (a new conditioning / well-formedness predicate is
  unverified until something instantiates it at the common graph shapes) at
  the Phase-39 close; pruned (details in git history).
- **F9 — a design pass's per-arm obligation verdicts ("free", "vacuous",
  "mirrors landed X") are unverified until a builder confronts them; prompt
  the confrontation explicitly (Phase 39 W5).** Promoted to the playbook
  (*Rate the task*: an arm re-derivation against a conditioned motive is P ≥
  2; the derivation guard's re-derive-and-return-the-refutation line) at the
  Phase-39 close; pruned.
- **F10 — diff a design PIN against the phase's OWN recorded Blockers at
  pin/dispatch time (Phase 39 W5-L6 habitat arc).** Promoted to the command's
  step-2 derivation guard (its third face: a design PIN vs the phase's
  recorded *Blockers*). Pruned at the Phase-39 close.
- **F11 — in an informal-research arc, the corrective mechanism is the NEXT
  pass, not coordinator scrutiny (Phase 39 kernel-(K) arc).** Promoted to
  `RESEARCH-ARC.md` §4 (*A driver per headline sentence*). Pruned at the
  Phase-39 close (the incident record is in git history).
- **F12 — when a return flags a stale claim in a named cell, grep the whole
  file: the same claim usually also sits in the body prose that the cell
  summarizes (Phase 39 fan-out landing).** Promoted to `RESEARCH-ARC.md` §6
  and, at the Phase-39 close, to the playbook's `hygiene` shaping block (every
  file kind, Lean docstrings included; a summary's correction is presumptively
  a body paragraph's too). Pruned.
- **F13 — a guard is not verified by existing; a sampler defect that *implies*
  the measured quantity is invisible to every downstream check (Phase 39,
  2026-08-06).** Promoted to `HARNESS.md` *Evidence* (blind axes; a guard
  needs its own adversarial test). Pruned at the Phase-39 close.
- **F14 — coordinator premises are as unverified as a subagent's, and the
  cheap check is measurement (Phase 39, 2026-08-06).** Promoted to the
  playbook's shaping-block paragraph (mark a coordinator hypothesis as a
  hypothesis; a truncated search is *at least N*, not an enumeration) at the
  Phase-39 close; pruned.
- **F15 — the 600 s foreground ceiling has no carve-out in the foreground-
  gates mandate, and a subagent's background job dies with its turn (Phase 39,
  2026-08-06).** Promoted to `HARNESS.md` *Reproducibility* and
  `notes/scripts/README.md` (start the over-ceiling invocation first; collect
  it before the turn ends). Pruned at the Phase-39 close.
- **F16 — a present check is not a guard: test whether it CAN fire (Phase
  39, 2026-08-06).** Auditing the `meet_line` call sites, a neighbouring
  `rank([hat(M0), hat(M0+Md), hat(pt b)]) == 2` assert was read as the guard
  covering an unguarded call — but at `Md = 0`, precisely the input in
  question, its second entry equals its first, so it passes **vacuously** and
  can never fire there. This is F13 one level down: F13 is a guard that fires
  on the wrong condition; this is a check that cannot fire at all on the
  input it appears to cover, and it was mistaken for a guard **inside the
  commit repairing the first instance**. The mechanical version of the check:
  substitute the degenerate value into the assert by hand and ask whether
  anything is still constrained. Corollary, and the reason this one was
  caught: a coordinator's site list is a starting point the builder
  re-derives, not a checklist it executes.
- **F17 — a document's own header is a status surface, and it is exactly what
  a section-scoped edit does not re-read (Phase 39, 2026-08-13…15).** Promoted
  to `CLAUDE.md` *Before each commit* (the note's `**Status:**` header is a
  surface), `notes/phasenote.py --surfaces`, `notes/check-phase-note.py` and
  `HARNESS.md`. Pruned at the Phase-39 close.

- **F18 — a parallel fan-out surfaces findings no single agent can see (Phase
  39, 2026-08-19).** Promoted to `RESEARCH-ARC.md` *Candidates* (budget a
  cross-return pass; choose directions in different sections). Pruned at the
  Phase-39 close.

- **F19 — coordinator-authored artifacts need the same verification tier as
  subagent returns (Phase 39, 2026-08-19).** Promoted to `RESEARCH-ARC.md`
  and, at the Phase-39 close, to the playbook's *Verification tiers* (the
  coordinator's own artifacts get the same tier; a coordinator commit runs the
  F17 sweep). Pruned.

- **F20 — label reservations prevent collisions, not duplication; two checks
  are missing (Phase 39, 2026-08-19).** Promoted to `RESEARCH-ARC.md`
  *Candidates* (the two missing duplication checks: against landed Lean,
  across concurrent siblings). Pruned at the Phase-39 close.

- **F21 — a mechanical cap catches overflow, not purposeless compliance (Phase
  39, 2026-08-19).** Promoted to `RESEARCH-ARC.md` §7 and `notes/check-gapmap-
  cells.py`'s docstring (a cap bounds growth, not purpose; recompute with a
  target; verify labels by a scripted set-diff). Pruned at the Phase-39 close.

- **F22 — a fan-out multiplies the coordinator's spec errors, and
  inherited clauses are the main vector (Phase 39, 2026-08-19).** Four of
  the eighth fan-out's five directions corrected a defective clause in
  their own spec — five clauses in all, and not one of them a
  mathematical mistake by the direction: every one was the coordinator
  asserting more than the source supported. **Three were inherited** —
  transcribed verbatim from a *landed* hand-off (AGLU's "is it
  fully-good?", BALB's "min-cost flow, hence polynomial", ZNEQ's
  "equivalently the Schubert non-jump") and therefore already
  twice-read, which is precisely why they survived a re-read. **Two were
  written at prep.** The lesson is not "read the hand-off harder": a
  landed hand-off clause carries the authority of a landed result and
  gets copied with it. The lesson is that **a hand-off's
  forward-looking clauses are conjectures, not results** — so a spec
  should quote them *as* the previous direction's recommendation rather
  than restate them as fact, letting the reader attack the clause
  instead of inheriting it. Pair this with the seventh fan-out's row
  (three coordinator premises refuted): across two waves **eight**
  coordinator premises have been refuted by the directions they primed,
  and **none** by a gate.

- **F23 — an unescaped pipe silently downgrades the gap-map cap gate,
  so a passing run proves nothing (Phase 39, 2026-08-19).**
  `check-gapmap-cells.py` falls back to capping columns 3+4 *combined*
  when a row's pipe count does not resolve to four columns — a
  deliberate, documented choice (it will not guess a split point). What
  is not documented is the consequence, which bit **twice in two
  landings**: writing `|W|`-style cardinality notation unescaped inside
  the row makes the gate pass on the *combined* cap while the status
  cell alone sits 31, then 121, words over its own. Escaping restored
  `split` parsing and exposed both overruns. **Check the parse mode, not
  just the exit code** — if a row parses as `combined`, its per-cell
  caps are not being enforced at all. Cheap standing fix for a
  successor: have the script *warn* when a row it was asked to check
  parses as `combined`.

- **F24 — a dispatch's criticism of coordinator work needs the same
  verification as its mathematics (Phase 39, 2026-08-19).** OSCHU
  returned a confident, specific, numbered claim that a sibling landing
  had skipped a mandated recompute. Checked against the commit it was
  wrong: the recompute had over-delivered (34 % off the pre-existing
  content), and the figure OSCHU quoted was the cell's *end* state after
  the sibling's own content went in. Two lessons, pointing opposite
  ways. **For the coordinator:** apply the reasoning-scrutiny tier to a
  dispatch's *process* claims too, not only its theorems — taking this
  one at face value would have produced a corrective commit repairing
  nothing. **Against the coordinator:** the misreading was *invited*,
  because one obligation was written two ways in one spec — "recompute …
  before adding its own content" for one section, a bare word-count for
  the other. State a repeated obligation **identically** at every site,
  or the weaker wording becomes the one a careful reader enforces.

- **F25 — the verification-bar sentence is itself a headline claim, and it
  is the one F11 is most likely to miss.** GHWIT (2026-08-26) shipped a
  correct, four-times-checked refutation whose *description of its own
  checking* was wrong: "four independent exact models" plus a pinned
  `max|R|` figure, against a driver implementing three — its own docstring
  saying so. Every gate passed, the mathematics was sound, and the three
  shipped models already met the project's (GR-83)/(GR-113) bar, so nothing
  failed except the sentence claiming more. The mechanism is specific and
  repeatable: a model written as a **scratchpad probe**, run, believed, then
  written up from memory of the *session* rather than a re-read of the
  *deliverable* — which is also how the draft's own "probes promoted"
  paragraph came to assert five promotions where three had happened. The
  agent's diagnosis is the rule: **write that sentence by re-reading the
  driver, never by recalling the session.** Coordinator-side the catch is
  cheap and mechanical — grep the driver for the claimed model count and for
  any figure the prose pins, before accepting a refutation. F11 says every
  headline claim needs a driver testing that sentence; this is the reminder
  that *"we checked it N ways"* is one of them, and on a refutation it is
  the load-bearing one.

- **F26 — a residual can be *correct* and still be the wrong target; check
  what the consumer actually consumes before spending a direction on it.**
  Promoted to `HARNESS.md` *Evidence* (open the consumer before dispatching at
  a residual). Pruned at the Phase-39 close.

- **F27 — one draw is a lower bound, not a measurement, whenever the statistic
  is semicontinuous.** Promoted to `HARNESS.md` *Evidence* (one draw of a
  semicontinuous statistic is a bound; an exhibited certificate is a proof).
  Pruned at the Phase-39 close.

- **F28 — a listed fence is not an acted-on fence.** Promoted to `HARNESS.md`
  *Evidence* (name the listed axis the direction is to OPEN). Pruned at the
  Phase-39 close.
- **F29 — *"where I expect to be wrong"* names the REGION reliably
  and the INSTANCE never.** Across this round's three specs the field
  pointed at the right region 3 of 3 — GOWNHALF's *"the partition,
  not the attribution"* **was** the answer; BWHOLEH's *"a fence, not
  a theorem"* was the right class; GTRIFREE's *"the quantifier is a
  statement about two drivers"* was the right suspect. It named the
  right instance **0 of 3**: BWHOLEH's two named literals both turned
  out inert (un-fencing `xy` changes nothing, all twelve pairs kill),
  and GTRIFREE's predicted *third move family* was never needed. So
  the field's value is **locating where to look**, and its named
  candidates should be written as *"start here, expect to discard"*
  rather than as the expected answer — the same discipline §7 already
  imposes on the MECHANISM field, now earned by a second field.

- **F30 — a PREFIX is not a SAMPLE, and the generator's emission ORDER is a
  population fence.** Promoted to `HARNESS.md` *Evidence* (a prefix is not a
  sample; sweep exhaustively or aim where the mechanism predicts, and say
  which). Pruned at the Phase-39 close.
- **F31 — a TELL must sample a quantity whose SEMICONTINUITY runs the
  way the verdict needs.** The tell check had three parts — not
  already satisfied, satisfiable at all, could the verdict differ
  inside the region. This round shows a fourth, and it decided two of
  three specs. BGOODEMPTY: the tell sampled `dim(ρ̄₁+ρ̄₂)`, which is
  **lower** semicontinuous, while the verdict needed an **upper**
  bound — so it *could not have settled the question* however it came
  out, and the direction said so. GCOLTRANS: the tell was posed at
  whole-shape existence, where a hit would have **refuted (GR-15)**
  rather than answering the question asked; it fired only once
  re-pointed at the shared datum. Both passed all three existing
  checks. **Add the fourth: name the quantity the tell measures and
  the direction the verdict needs it to move; if a draw can only
  bound it the wrong way, the tell is a pointer and must be labelled
  one.** Note this is the same family as the two unsatisfiable tells
  of 2026-09-10, now recurring with a diagnosable cause rather than
  as a pair of one-offs.
- **F32 — for a predicate built as a DIFFERENCE of two semicontinuous
  quantities, NEITHER verdict is cap-free**, and a landed `100 %` can
  be capped in the direction that would destroy it. F31 says a tell
  must sample a quantity whose semicontinuity runs the way the verdict
  needs. GSECOND (2026-09-12) shows the sharper form on the corpus's
  own transport predicate: the weak lift is `cg ⊆ pg`, an inclusion
  between two sets that are **both lower bounds** (deeper draws only
  add GOOD colourings to each side), so raising the draw count can
  **break a holding triple** as well as repair a failing one. The
  coordinator's spec asserted the one-way reading — *"the failure side
  is capped and the success side is not"* — which is true of a single
  colouring's GOOD verdict and **false of the predicate built from
  it**, and (GR-232)(ii)'s headline `15 304/15 304 = 100 %` is a
  HOLDING figure. Three controls found 0 movement at a 200-shape
  prefix, so it does not bite here; the reading was still wrong.
  Operationally: before quoting a cap direction, write the predicate
  out and ask which way EACH of its arguments moves — a cap inherited
  from a component is not a cap on the composite.
- **F33 — a driver's own DOCSTRING is an unguarded status surface, and
  the only gate on it is re-running the mode at its documented
  default.** `ledger.py --lint` does not run drivers;
  `check-driver-refs.py` checks that a cited mode EXISTS, never what
  it claims; nothing re-runs a docstring. GSECOND (2026-09-12) ran
  `gcoltrans.py --lift --shapes 400` — the default its own caps block
  and its own `--lift` mode description both describe as showing **0**
  lift failures — and got **125**; the coordinator reproduced it
  independently before the sentence was touched. The companion clause
  was separately wrong in the same two places (for a PREFIX cap the
  capped and full runs ARE bit-identical on the first N shapes, the
  stream being in the same state throughout). This is the same
  gate-invisible class as BGOODEMPTY's drifted defaults (2026-09-12,
  cross-return pass), one level up: there the PROSE was right and the
  driver had drifted, here the DRIVER is right and its own prose is
  wrong. Operationally: when a spec names a driver's documented
  default as a fence, re-run it at that default before quoting it —
  which is what the F26 consumer check produced here as a side effect.
- **F34 — a tell can be ALREADY SATISFIED IN THE LANDED CORPUS without
  anyone having read it that way**, and the standing *"is it already
  satisfied?"* check does not catch that. BPROPCL (2026-09-12) was
  dispatched with a tell — *one chart point where `U ⊄ ρ̄_i`* — and the
  spec recorded *"not reported anywhere: the corpus has measured
  `c_i(U)` but has not reported the containment as a chart-level
  condition"*. It was reported, twice: (BE-258)(iii)'s `dist = 6`
  column (16 rows at `c(Π_x) ≤ 1`) and (BE-273)(i)'s same 16 rows at
  `c(⟨M⟩) = 0` **are** the tell, and neither clause read them as
  containment. The check as written asks whether the corpus contains
  the **claim**; it must ask whether the corpus contains the
  **answer**, which is a different grep and usually a different
  vocabulary. Operationally: before calling a tell unsatisfied,
  ask what a landed measurement of the tell's quantity would LOOK
  like under a different name, and grep for that.
- **F35 — the anti-duplication fence can PRODUCE a convergence rather
  than merely prevent a collision**, when a fenced direction treats
  the sibling's landed work as an external input to TEST. The
  2026-09-12 round told BSIXTEEN not to attempt BPROPCL's properness
  lemma and BPROPCL not to close a block. BSIXTEEN landed mid-run
  proposing a repair — state the lemma relative to `⟨P₀⟩` — and
  BPROPCL, whose own headline through six steps was *"the two
  residues are NOT one question"*, **tested the proposal instead of
  arguing against it**: asserted at 1 281/1 281, which refutes the
  sibling sentence in its own frame and confirms it in the new one.
  Two directions fenced off each other's lemma converged on one from
  opposite ends of the same axis. **The mechanism is the concurrency
  rule** — diff against `HEAD`, never against the dispatch baseline —
  so that rule earns its keep as a discovery device and not only as a
  hazard control. F20 says reservations prevent naming collisions and
  not duplicated derivation; this is the other half: a PROSE fence
  plus a live `HEAD` can turn the overlap into a joint result.

- **F36 — a landed workbook can be INVISIBLE to the ledger, and every
  gate stays green.** `ledger.py`'s opener regex requires the `> `
  blockquote marker; a direction that writes its clause blocks as plain
  paragraphs produces a file with **zero** indexed claims, and because
  `--lint` reads the same index, the landing gate certifies nothing.
  BSIXTEEN (111) shipped 29 such openers and the defect survived a
  landing, a cross-return pass and a strategy pass before `--brief`
  returned empty on the lane §8 ranked first. **The check is one call** —
  `ledger.py --list | grep <FILE>` at landing, against the file's own
  opener count — and it belongs in the landing sweep, not in a cleanup
  round. Corollary: a direction's draft must be linted **while the
  coordinator can still see it**, since a green `--lint` on an unindexed
  file is vacuous.
- **F37 — a spec that QUOTES a tally manufactures agreement between
  independent returns.** `RESEARCH-ARC.md` §2 says never have a direction
  re-derive a shared monotone counter; the sharper form is that **citing
  the counter is the same hazard as asking for one**. Three concurrent
  directions, each handed *"record: 0 of 6"* and asked to score its own
  mechanism against it, each refuted its mechanism and each wrote
  *"0 of 7"* — three copies of a wrong value that **agree with each
  other**, which is precisely the signal a coordinator is otherwise
  entitled to trust, and which no per-return check can see because each
  draft is internally consistent. Two things were wrong: §7's figure is a
  **fixed unselected sample** whose value depends on not being
  incremented, and three refutations move the arc tally by three. **Fix:**
  cite a tally as a fixed, dated value with *"do not increment — the
  coordinator updates this at the cross-return pass"*, or omit the number
  and ask only for the direction's own verdict. Recorded after the
  coordinator propagated the same error into two coordinator-authored
  surfaces.

- **F38 — the errors cluster in ONE spec, not across the round.** Two
  consecutive rounds now show the same shape: the coordinator's mistakes are not
  spread evenly but concentrated in whichever entry was written last or fastest
  (round five: bar *(p)*'s premise; round six: **four** in rank 3 alone, three of
  them refutable with no computation). The operative lesson is not *"check
  harder"* but *"the last spec written is the one to re-read"* — and in both
  rounds the refuting evidence was **in an artifact the coordinator had already
  run or already cited**: `bgplaw.py`'s own in-band print, `bsixteen.py`'s
  dispatch table, `bsixteen.py:637`'s second `forced` call site. **A generated
  list, a single grep, or a definition read without its use sites is evidence
  about syntax, never about dispatch.**
- **F39 — a committed driver whose landed figure cannot be re-run from the
  command line is not reproducible** Promoted to `HARNESS.md`
  *Reproducibility* (every cap a landed figure varies is a CLI argument).
  Pruned at the Phase-39 close.

- **F40 — a status surface with no script behind it drifts on a per-landing
  cadence, and prose rules do not hold it.** Two instances in one session:
  `notes/Phase39.md` blew its 580-line cap (618, with a 17-line *Decisions
  made* entry) on one landing, and the ROADMAP Phase-39 Status cell grew
  623 -> 1325 chars over three. Both surfaces had a written rule forbidding
  exactly the growth, and both had been repaired by hand before — the note at
  `35e9ce6e`, the cell at doc-round slice 7. The note's cap now holds because
  `check-phase-note.py` exists; the cell's does not, because nothing reads it.
  The asymmetry IS the finding, and it is the same one
  `check-gapmap-cells.py`'s own source records ("two prose-only repairs were
  abandoned in favour of this mechanical cap"). **Actionable:** the four
  maintained "next concrete task" surfaces (the note's `**Status:**` header,
  *Current state*, *Hand-off*, the ROADMAP row) are one artifact class with one
  gate covering one member; a `check-roadmap-cells.py` on the Status table's
  per-cell char count is the cheap missing half. Until it exists, the
  coordinator re-thins the cell at verification — a landing agent updating "its"
  row will not, because appending one clause always looks proportionate from
  inside a single slice.

- **F41 — a coordinator spike raises S, and its every wrong turn is a defect
  the dispatch would otherwise have absorbed; but its ABSENCES are not
  verified.** Promoted to the playbook *Raising S* (spike discipline:
  positives to the `route` block, absences only as "check before hand-
  rolling"; search by bare declaration name) at the Phase-39 close; pruned.

- **F42 — a spike whose conclusion is about a CONSUMER must reproduce the
  consumer's file kind, or it measures the wrong thing twice.** Promoted to
  the playbook *Raising S* (a spike about a consumer reproduces the consumer's
  file kind; run both cases) at the Phase-39 close; pruned.

- **F43 — a complete sorry-free recon spike IS the build; slice it only if it is not.**
  Promoted to the playbook (step 3 *Resume and land*) at the 2026-09-26 harness
  review, alongside Fable leaving the rung map (*Pick the rung*); the evidence is
  the Phase 40c rows above and `notes/harness/incidents.md` 2026-09-26.
