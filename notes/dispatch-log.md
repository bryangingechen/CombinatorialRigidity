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
| 2026-07-17 | Phase34 Layer-BB chapter extension (`ed707a77`) | fable | pre-build recon REFUTED an R0-era route claim before any Lean built on it | The phase note's Layer-BB route ("the landed standard-basis witness vectors are ±T of coordinate-point pairs") rode from R0 through five clean slices unchecked — no gate reads route prose. The commissioned chapter-extension recon checked it against the JJ p. 581 entry table + the minor formula and refuted it (pure-moment basis vectors are not T-images), rerouting via the Whiteley change-of-coordinates remark. Second firing of the Phase-32 pre-build-recon guard; the coordinator's prompt had flagged the claim as unverified, which routed it to a check instead of a transcription. |
| 2026-07-17 | Phase34 Layer-BB first Lean slice (killed; landed `b6454b02` on resume) | sonnet | killed by an API stream error pre-work; same-agent resume landed clean | The dispatch died on "Stream idle timeout - no chunks received" before writing anything (tree clean, HEAD unmoved) — a new kill *cause* for the rescue-§3 shape (previously session/usage limits + user interrupts). Same-agent SendMessage resume with a fresh task statement landed the full slice clean; rung-pinned variant, no F5 drift. No salvage needed since nothing stranded. |
| 2026-07-18 | Phase34 BH witness-trio continuation (`43d5764f`) | sonnet | nested-Agent spawn attempt, blocked by hook, self-reported | Mid-task the agent tried to spawn an Explore subagent for mathlib research; the `block-nested-agent.sh` PreToolUse hook denied it mechanically and the agent did the research itself (`grep`/`lean_run_code`), landing clean. Zero tree impact; logged because the agent's own core forbids nested spawns and the hook (not the prose) is what held — same lesson as the sorry-commit hook: discipline that must survive long contexts belongs in hooks. |
| 2026-07-24 | Phase39 W1 cycle-wrap coplanar slice (`2c3aade8`, amended to `cd5575d4`) | opus | gate-invisible commit-message defect caught in coordinator mechanics check | The LANDED commit's message had no subject line — the first line was the full opening paragraph, so `git log --oneline` rendered a ~340-char subject. Content/gates clean; coordinator amended message-only (pre-authorized rescue-§1 fixup). Lesson: the phase-builder core's message discipline held for 8 prior commits incl. this agent type; one-off, no pattern yet. Same dispatch also correctly applied the coordinator's m-range correction (hand-off's "only triangle" claim refuted by `exists_cycle_normals`'s own `m ≤ k+2`). |
| 2026-07-24 | Phase39 W3-L1 min-degree-3 dispatch lemma (`bc04ffef`) | sonnet | transient concurrent-build race mid-dispatch, self-reported | The agent's first two full `lake build` calls lacked an explicit `timeout` and auto-backgrounded (the F6 harness path); instead of waiting it re-ran with a timeout, briefly running two concurrent builds — one transient olean write race (`CaseIII/Candidate.olean` "no such file"). A clean single rebuild resolved it; agent self-reported. Coordinator re-ran all gates (touch + full build warning-clean, `lake lint` green). F6's timeout mandate held for the *re-run* but the wrong recovery (re-run instead of wait) created the overlap — the core's "one build at a time" line is the operative rule; watch for recurrence. |
| 2026-07-24 | Phase39 W3-L2 pencil reduction skeleton (`adae37ac`) | sonnet | masked build exit status via shell `timeout`+`tail`, self-reported | Third F6-family manifestation this phase, new path: the agent wrapped its full build as shell-level `timeout 600 lake build \| tail -100`, which auto-backgrounded at the harness default AND masked the true exit status behind `tail`'s exit 0 — `lake lint` then failed on the stale-olean symptom. Correct recovery this time (waited, no concurrent build; one clean unwrapped rebuild, then all gates green). Coordinator re-ran gates (full build warning-clean, `lake lint` green). Lesson: the Bash tool's `timeout` PARAMETER, never a piped shell `timeout … \| tail` — the pipe both hides failure and truncates the warning scan. |
| 2026-07-24 | Phase39 W3-L2a simplicity sibling (`b2e34aae`) | sonnet | pipe-wrapped gate builds recurred DESPITE explicit in-prompt ban, self-reported; recovery correct | Second same-day `\| tail` recurrence — the dispatch prompt explicitly named and banned the exact anti-pattern and the agent still piped its first two gate builds (auto-backgrounded, exit masked). Recovery was right this time: waited for both stray builds (no third concurrent build), then one clean unwrapped rebuild; all gates honestly green, coordinator re-verified. Mitigation escalated from prompt to CORE: `agents-core/phase-builder.md` now bans shell `timeout`/`tail` wraps on gates and mandates wait-then-rerun (this commit). Prompt-level wording demonstrably does not hold — watch whether the core edit does. |
| 2026-07-24 | Phase39 W3-L4 transport slice (`0a9dac92`) | opus | recon-pin defects ×2 caught by the builder's derivation guard | The accepted fable route recon's W3-L4 leaf note mis-pinned two bricks: it named "the landed ProjectiveInvariance transport" (actually ℝ-only, `supportExtensor`-only — inapplicable; the K-level transport had to be built on `GenericLift/HingeGeneric.lean`'s `screwEquivOfLinearEquiv`/`mapSupport`) and called `exists_cut_decomposition_of_not_twoEdgeConnected` minimality-free (it takes `IsMinimalKDof`; only the deficiency lemma is free). The in-prompt derivation guard ("read the landed signatures before writing the statement") caught both pre-build; coordinator re-verified both against the source. Scope-to-fit landed the transport half honestly; L4 remainder retargeted. Lesson: even a top-rung recon's *leaf-list* brick attributions are unverified pins — the per-dispatch derivation guard is the check that fires. |
| 2026-07-24 | Phase39 W5-L4 assembly continuation (`a969a0e4`) | sonnet | unsatisfiable WF-predicate conjunct in landed W5-L2 code, caught 2 slices later; second conjunct gap surfaced as honest blocker | `PencilChartWF`'s `closedNbhd` selector conjunct was unconditional — unsatisfiable at any ≥4-distinct-neighbour body (incl. the design doc's own N4–N6 test graphs). Rode through two landed slices because the by-construction membership theorem only CONSUMES WF, never instantiates it; caught when the D6 assembly first instantiated WF at real graphs. Same-commit fix (relativized to non-hubs; all consumers compile unchanged). The 4th conjunct has an analogous gap (triple-LI at degree-2 non-hubs) that is a genuine open design question, recorded as the hand-off blocker with a numerics-first route. See Findings F8. |
| 2026-07-24 | Phase39 W5-L5 base arm (`58d0bb37`) → recon chain → (b′) restatement (`63e47c8b`) | sonnet→fable | design-premise refutation return, escalated to recon + user adjudication | The sonnet builder, prompted to re-derive the spiked plan against CURRENT definition bodies, refuted the design doc's "parallel classes nondegeneracy-infeasible, hence vacuous" premise with a compiler-checked witness instead of building on it (the L5 bullet had dropped verdict 1's "between two hubs" qualifier). Fable recon confirmed the rank cap (`PencilPair` as landed FALSE at parallel classes), a user-commissioned second recon projected both repairs long-run (key: the two conditionings are logically equivalent graph-by-graph), user adjudicated (b′). See F9. |
| 2026-07-24 | Phase39 W5-L5 cut arm (`6dd9e0e9`) | opus (pinned) → ran fable | rung up-drift on a pinned variant; design-blocked return with honest slice | The `phase-builder-opus` variant's environment identified the model as Fable 5 — first observed pin-not-honored on a FRESH dispatch (F5 covered resumes of base-type dispatches); up-drift, safe direction, trailer correctly named the actual model per the environment-wins rule. Recurred on the next opus-pinned dispatch same session (L5-cut-i, `7c5e5980`) — systematic this session, not a one-off. The task itself returned design-blocked: it confirmed the recon-recorded input gap AND found a new output gap (promotion side), landed route-neutral `.mono` infra + the owed note rebalance, and commissioned the cut-arm route recon rather than forcing a construction. See F9. |
| 2026-07-25 | Phase39 L5-cut-ii transport bookkeeping (`b85a36e5`) | sonnet | neither-return (pipe-wrapped gate + Monitor park, BOTH banned shapes in one dispatch), same-agent resume recovered | 8th parked-on-background instance: the agent piped its gate build (`\| tail`, exit masked) then parked on a Monitor wait — both anti-patterns its core + the in-prompt F6 line explicitly ban, combined. Diff was complete but uncommitted, notes untouched. Coordinator resumed same-agent (rung-pinned sonnet, no F5 drift) with finish-in-foreground instructions; agent self-reported both misses, re-ran all gates plain-foreground, landed clean; coordinator re-verified everything. Core-level bans demonstrably do not fully hold either (cf. the 2026-07-24 `b2e34aae` row) — the coordinator's neither-return resume remains the reliable backstop. |
| 2026-07-25 | Phase39 L5-cut-iii repositioning lemma (`83c1855d`) | opus (pinned, ran fable) | killed mid-dispatch (64k output-token API cap), resumed same-agent; favorable spike route-correction | First output-cap kill in the log (response exceeded 64k output tokens — an oversized single emission, distinct from the org-spend kills); tree was untouched, so the resume re-oriented from scratch with an added keep-emissions-compact instruction and ran to a clean landing. The mandated spike-first fired F9 in the FAVORABLE direction: the recon-pinned point-match mechanism proved unnecessary — the leaf landed match-free, uniform, any-field (no `[Infinite K]`), recorded as a superseding note in the route verdict. Spike-first on risk-carrying leaves validated again. |
| 2026-07-25 | Phase39 L5-cut-iv sub-case 3 (`c99d5fe1`; fixup by coordinator) | sonnet | gate-invisible defect: new file orphaned from the aggregator — "full build green" attestation hollow for it | The slice created `Pencil/Pair2.lean` (Pair.lean at the LoC cap) but never added an aggregator import, so the default-target `lake build`/`lake lint` compiled everything EXCEPT the new file; the agent's targeted build made the file itself green, masking the gap. Caught by the coordinator's step-5 habit of grepping the aggregator for a commit's NEW file (the "new downstream file is rightmost, not leftmost" check); mechanical fixup repointed `…Pencil.Pair` → `…Pencil.Pair2` (job count 2871→2872 confirms inclusion), all gates re-run green. Lesson: a new-file slice's gate attestation is only as good as its import wiring — grep the aggregator on every new-file commit. |
| 2026-07-25 | Phase39 L5-cut-iv dispatch shell (`4de80069`; corrected `562ee76a`) | sonnet | gate-invisible defect: carried hypothesis unsatisfiable as stated, caught by coordinator satisfiability trace, same-agent corrective | The shell carried the sub-case-4 residual as `hcutPendant3` with the ambient `G.Simple`/`PencilNondegFeasible` premises deliberately DROPPED ("already in context" — inverted reasoning: in context at the use site, absent for the discharger). Every gate passed; the coordinator's satisfiability trace against a concrete graph (the net graph — meets every configuration premise, infeasible by the recon's triangle finding, so the unconditioned conclusion is FALSE there) showed the global form the successor must supply is unsatisfiable. Corrective (same agent, coordinator-pinned exact shape) added the two antecedents. The step-4 "deferred-hypothesis satisfiability trace at a CONCRETE object" discipline caught what an explicit in-prompt trace mandate did not — the agent ran a trace and reasoned it backwards. |
| 2026-07-29 | Phase39 W5-L6a ≤3 lemma build (BLOCKED, no commit; refutes `6768bd33` L6a) | opus | design-pass verdict refuted at first contact by computer-verified counterexample (F9) | verdict 4's "2EC+no-proper-rigid ⟹ ≤3 closed-hub-nbhd" (evidence: 2 short-chain attempts) is FALSE — builder returned a theta-graph counterexample (arcs (6,6,6); all 2^19 subsets: 2EC, all-proper-f<0, four deg-3 hubs → closedHubNbhd=4) instead of building. Recon's PROOF-RISK flag + in-prompt flag-don't-force → clean refutation, tree untouched; coordinator reproduced it (script + deficiency-def check) before salvaging. Re-route: dedicated L6a proof-route recon for the true use-site invariant — counterexample is strictly sparse (f(V)=−3), so rigidity/tightness leads. |
| 2026-07-30 | Phase39 W5-L6b bank-authorized spike (no commit; refutes design-doc L6b pin) | opus (recon) | pinned leaf signature refuted by compiler-checked spike — contradicts a RECORDED blocker (F9) | Spike found `hcard ≤ 3 ⟹ PencilNondegFeasible` FALSE: a two-adjacent-hub triangle satisfies `hcard` yet is infeasible by the landed `not_pencilNondegFeasible_of_triangle_two_hubs`. Key: the phase note *Blockers* ALREADY recorded the triangle-hub mechanism refutes any ≤3-closedHubNbhd criterion — the L6b pin (from `6768bd33`, "L6b UNCHANGED" thru 2 later recons) never reconciled with it. Internal plan inconsistency, not new math. Assembly route sound; only the hypothesis wrong. Surfaced NEW untracked obligation L6d (triangle-freeness transfer G⇒G′). Third optimistic-habitat-pin refutation in the L6 arc → coordinator surfacing a habitat-foundations recon before more builds. Lesson: a design pin must be diffed against the phase's OWN recorded Blockers at pin time. |
| 2026-07-30 | Phase39 W5-L7b `escapePoly` build (BLOCKED, no commit; refutes the L7-recon sizing) | sonnet | design-pass sizing refuted at first contact — BLOCKED return, salvaged into a route recon | The L7-recon pin "`escapePoly` is L3-style, buildable" refuted: KT (6.42)'s `M₁` row needs the GLOBAL stress (left null vector of `G′`'s entire rigidity matrix) as a polynomial, and no corank-1-cofactor infra exists in tree — multi-commit new infra with sign/column-choice faithfulness risk, not an L3 mirror. Builder returned BLOCKED, tree untouched; salvaged into the L7b-shape route recon (fable) whose verdict this design pass records: `escapePoly` deleted, (K) re-pinned as the ∃-LI `hK` form the engine's `hLI` slot consumes directly. |
| 2026-07-30 | Phase39 L7b-shape route recon (verdict landed as this design pass) | fable (recon) | recon-verdict defect caught at coordinator acceptance — pin-vs-Blockers (F10 pattern), corrected before any build | The verdict's residue-2 "recommended first attack" (prove habitat ⟹ `hcard ≤ 3`) contradicted the phase's OWN record: the 2026-07-29 theta counterexample (phase-note *Blockers* + design-doc L6a block) is a habitat graph with `closedHubNbhd(center) = 4`. Coordinator caught it at acceptance; the correction pins the verdict's OTHER named route (bare rank-extension leaf, own recon before build). Second pin-vs-Blockers instance this arc — the F10 diff-against-Blockers check fired at verdict-acceptance time, where it belongs. |
| 2026-07-30 | Phase39 W5-L7b build (landed this commit) | sonnet | BLOCKED-then-corrected pinned signature, F9 pattern | Pinned signature (`[Nonempty α]`) failed to elaborate: `hEsc`'s TYPE reads `G.endsOf`, which needs `[Inhabited α]` at statement-elaboration time — a tactic-local `Classical.inhabited_of_nonempty` cannot reach a statement-level occurrence, and this project deliberately keeps `Nonempty→Inhabited` unregistered. Builder returned BLOCKED with a scratch-compile-verified one-token fix instead of self-patching. Coordinator adjudicated the fix; also flagged the identical `hK` pin for the L7c builder. Same shape as the 2026-07-30 L6a-transfer BLOCKED-then-corrected sequence. |
| 2026-07-30 | Phase39 W5-L7c-3 base case (`29b4a34c`; fixup by coordinator) | sonnet | gate-invisible defect recurrence: new file orphaned from the aggregator — attestation hollow for it; cost-outlier dispatch | Second instance of the 2026-07-25 orphaned-new-file pattern: `Pencil/Base.lean` landed with no aggregator import, so the attested default-target `lake build`/`lake lint` never compiled it (the agent's targeted build made it green in isolation). Caught by the coordinator's new-file aggregator grep; module compiles clean standalone; one-line import fixup, gates re-run green, `#print axioms` clean on the headline. The dispatch was also a 533k-token cost outlier with two other self-corrected/flagged misses (transcription half initially skipped, L7c-4 deferral) — the outlier-scrutiny rule validated. |
| 2026-07-30 | Phase39 W5-L7c-6 successor (`6d7f57d5`; prose fixup by coordinator) | sonnet | gate-invisible citation overclaim in the new blueprint fmlnote, caught at coordinator re-read | The added kernels fmlnote claimed (K) "is additionally implied by" KT's Claim 6.12 — false: the L7 recon's central finding is that KT's span proof does not survive the pencil condition (span 6 → 5), which is exactly why (K) is open. Every name/label gate passes on such prose; only the citation/shape re-read catches it. Coordinator reworded to the accurate "pencil analogue, not implied" form; blueprint verify + lint re-run green. The commit's Lean content verified clean and untouched by the fixup. |
| 2026-07-30 | Phase39 (K) literature hunt (`86f194e8`) | opus→fable | rung pin failed on a FRESH dispatch — `recon-opus` ran at the session model (fable) | Not the F5 resume-drift shape: this was a fresh `recon-opus` launch whose environment identified as Fable 5 from the start; the agent caught it and set the trailer to Fable per CLAUDE.md. Upward substitution — verification unaffected, citations spot-checked clean. New failure surface: the rung-pinned variants' `model` frontmatter is not guaranteed on fresh dispatches either; check the return's model self-report on every below-top-rung dispatch and treat a silent upward run as benign but a silent DOWNWARD run as a failed verification. |
| 2026-07-30 | Phase39 W4-L4 identification recon (`f2f518fb`) | fable (recon) | killed mid-dispatch (org spend limit), resumed same-agent | Fourth org-spend-limit kill (cf. the three 2026-07-10/16 rows); hit the L4 recon early — HEAD unmoved, no tracked edits, only its in-progress probe script untracked (plus a `__pycache__` the resume was told not to commit). On limit reset the coordinator resumed same-agent (SendMessage; rung-pinned fable) naming the tree state and the reuse-your-probe-script instruction; the agent re-oriented from the script, completed the full deliverable, landed clean. Kill-early resume clean again; the untracked-artifact inventory in the resume message is the cheap re-orientation aid. |
| 2026-08-02 | Phase39 (SAFE-RES) informal recon (`ec2454ed`; prose fixup `480bcfa2`, same-agent) | opus (recon) | gate-invisible overclaim caught at coordinator scrutiny — workbook internal inconsistency | Step 2 called the branch arithmetic "the *proof* behind" the short-branch probes' emptiness, and the "sharp bound κ≥2" takeaway carried the same hidden conditionality — both follow only from gap (E), which the SAME section's Step 3 lists OPEN; a miniature echo sat in the phase-note entry (coordinator phrase-grep missed it; the agent's own re-read found it). No gate reads informal prose; caught by internal-consistency scrutiny (claims vs the section's own named gaps). Same-agent continuation fixed both files. Lesson: scan each workbook section for claims stronger than its own named gaps. |
| 2026-08-02 | Phase39 (SAFE-RES) recon pool figures (`ec2454ed`; corrected in `4045bd37`) | opus (recon) | gate-invisible numeric transcription error, caught by the NEXT dispatch's re-run | Workbook + phase note recorded the residual pool as "281 inhabitants / 65 (SAFE-RES) refutations"; the unchanged script yields 255/216 (39 refutations) — a transcription error, every other figure reproduces. Surfaced only because the widening recon re-ran the pool as its own input; coordinator re-ran `--prime` and confirmed 255/216. Lesson: coordinator spot re-runs should cover headline FIGURES, not just the `--validate`/`--witness` drivers; a downstream dispatch consuming a prior dispatch's pool re-derives its counts rather than quoting them. |
| 2026-08-02 | Phase39 numerics-infra defect: degenerate placement sampler (caught in `d6d1aa91`) | fable (recon) | latent script defect contaminated MULTIPLE dispatches' recorded figures; caught by an exact-criterion cross-check, not by any re-run | `localtest.py::plane_basis` returns two PARALLEL in-plane directions whenever a normal's third coordinate is 0, so "in-plane" sweeps sampled a line — every recorded escape FAILURE (seed-442 "mispredict", 11/12 tight control, 94/96 pool, the C3 "failure set is exactly the line" gloss, the interim "M2-pencil 12/12" predictor) was this artifact; positive records unaffected (a degenerate sampler can only suppress escapes). Coordinator re-runs had reproduced the figures faithfully — reproduction ≠ correctness when the defect is in the shared harness. Caught only when the fable re-pin derived an exact per-placement criterion and the observations contradicted it. Lessons: samplers need degeneracy guards + a sampled-object rank assert; when a derived criterion and an observation disagree, suspect the OBSERVATION's harness before weakening the criterion. |
| 2026-08-05 | Phase39 (K-slide-comb) recon (`3a8b07a5`) | opus (recon; fable substitute, session rung config) | two gate-invisible defects in the PRIOR pass's "proven pieces", caught by the next dispatch | The fourth pass (`a886bab5`) recorded (a) "4-colorability proven for all-length-3 shapes" as discharging the collapse's colouring premise — but every menu mandates `L_{φu,φw}`, so the premise needs an **acyclic** 4-colouring, about which 3-degeneracy says nothing; and (b) (C2)'s length-4 entry as "(forced)" — an *exhaustiveness* claim its per-entry machine asserts can't test (refuted, 12/12 witnesses). Both rode through last session's coordinator reasoning-scrutiny pass. Lessons: a "proven piece" discharging a premise must be checked against the premise's ACTUAL invariant, not a nearby one; a dictionary entry marked "forced" is an exhaustiveness claim needing its own driver. Third consecutive pass in this arc correcting its predecessor — see F11. |
| 2026-08-05 | Phase39 σ-recon verdict landed (`3df70929`) | opus (recon) → opus (builder) | gate-invisible figure defect caught by the LANDING dispatch | The σ recon's Step-σ4 table reported "63/63" on every row, but its four scratch drivers ran *different* seed pools per script (one covered 34 seeds, another 73), so the uniform figure was an aggregate across inconsistent scopes — no gate reads a recon's own table. Caught when the landing builder consolidated the scratch drivers into one committed `sigma.py`, pinned a single 63-seed pool, and re-ran every check over it; the landed figure is now literally true. Lesson: a read-only recon's headline figure needs a pinned pool before it is quoted, and driver consolidation at landing is where that gets enforced. |
| 2026-08-05 | Phase39 verdict-landing commit (`c09b32bf` → amended `3df70929`) | opus (builder) | wrong trailer from a stale in-definition example — RECURRENCE | Both opus agent definitions illustrated the trailer with `e.g. Claude Opus 4.8` while the dispatched model was Opus 5; the builder wrote the stale name, caught it itself, and amended. Same failure mode CLAUDE.md already records from 2026-07-02 (a stale `Sonnet 4.6` example propagating into a landed trailer) — the instruction was correct ("read your environment block"), the *example* was the hazard. Coordinator fix: both opus variants now carry no version example and an explicit do-not-copy warning naming both incidents. |
| 2026-08-06 | Phase39 fan-out direction B (`d2805253`) | opus (recon) | latent harness defect found BY a dispatch — the documented guard does not guard | `place_pencil_general`'s single-hub-interior sampler degenerates via `localtest.plane_basis` at 32/357 POOL-G frames (~9%), and the degeneracy *implies* the measured quantity (`λᵢ = 0`, 15/15 b-side + 18/18 c-side). `star_span_ranks` — whose own docstring (`flanks.py:201`) calls it the genericity guard against exactly this artifact — does not catch it, and no `IsNondegPencilRealization` conjunct excludes it. Second `plane_basis` contamination (cf. 2026-08-02) and the first where the mitigation failed. Caught only because B happened to measure a quantity the degeneracy forces. Landed as harness-debt item 4; coordinator opened the re-baselining round. See F13. |
| 2026-08-06 | Phase39 fan-out direction A landing (`c9cf5792`) | opus (builder) | mitigation VALIDATED — registry caught a three-way label collision at landing | A's draft minted bare `(R1)`/`(R2)`, which would have collided three ways (Shared dictionary / opening recon / `Pencil-strategy.md` §4.6's six refutations); landed as `(ANH-R1)`/`(ANH-R2)`, and the promoted branch-length result as `(SD-6)` not `(R6)`. `notes/Pencil-labels.md` was created the same day, hours earlier, for precisely this failure mode. Logged as a positive control: the registry is load-bearing, not decorative, and the minting rule fired at the right moment (draft→landing) rather than after the fact. |
| 2026-08-06 | Phase39 harness round S1, first attempt (re-run; landed `c980118a`) | opus (builder) | over-ceiling invocation lost to a turn-end background kill; coordinator re-ran | The slice backgrounded `flanks.py --limit` (762 s, past the harness's 600 s foreground ceiling) and returned to park; a subagent's background job is killed when its turn ends, so it never wrote its `.rc` and left a 0-byte output. Coordinator re-ran it. The rule, validated by the retry and again by S2: **background the over-ceiling invocation FIRST and run the foreground work alongside it**, so the turn never ends while it is in flight. Gap exposed: F6's all-gates-foreground mandate has no carve-out for invocations past the ceiling, and both agent cores are silent on it. See F15. |
| 2026-08-06 | Phase39 harness round S1 dispatch scope-pin (`c980118a`) | opus (builder) | coordinator premise labelled VERIFIED was wrong — truncated grep (F14-class) | The prompt's `scope-pin` block told the builder the only caller-side `UnboundLocalError` catch was `outer.py:239` and that the README's three-site claim was an overcount to correct. There are three (`outer.py:239`, `sigma.py:742`, `sigma.py:841`); the README was right all along. Cause: a `grep ... \| head -20` whose output the coordinator read as exhaustive, then passed in the VERIFIED register. The builder re-derived from source. Lesson: a truncated search is not a verified enumeration -- drop the pipe, or say "at least". See F14. |
| 2026-08-06 | Phase39 harness round S1 addendum, the sixth site (`c980118a`) | opus (builder) | coordinator site list undercounted; build agent caught it — a second instance of F13's own pattern | The coordinator-opened S1 addendum named five unguarded `meet_line` callers; there are six. The missed one, `lambda.py:1110`, was classified already-guarded because a neighbouring `rank([hat(M0), hat(M0+Md), hat(pt b)]) == 2` assert reads like a guard -- at `Md = 0` it compares a row with itself and passes vacuously. A check that cannot fire, mistaken for a guard, inside the commit repairing that very defect class. The builder caught it and folded `lambda.py` into S1's edit list (already inside the closure, so no extra re-baseline). See F16. |
| 2026-08-07 | Phase39 fourth fan-out landings E/J (`cdd23d30`, this commit) | fable (recon) ×2 | reproduce-table drift caught at J's landing — three prior landing commits skipped the README §3 step | Direction J's return flagged "README §3 rows" as a landing item; checking found the invocation table stopped at the SECOND fan-out's drivers — the third fan-out's landings (gridwit/anhr1/outerwide + 2 m2 leaves, all coordinator-authored) and E's own landing (packmm, despite the draft's explicit "enters the reproduce table") never added rows. Reproducibility survived only because the workbook Verification blocks carry the invocations. Repaired in J's landing commit (24 w4 rows + 3 m2 rows). Lesson: the fan-out landing checklist says "commit the new script"; the reproduce-table row is part of that step, not an optional extra — and a return's own coordinator-action list is a checklist to execute, not colour. |
| 2026-08-07 | Phase39 direction CFLANK landing (sixth direction) | opus | gate-invisible overclaim caught in verification: a byte-identity attestation over a driver that prints wall-clock timings can never hold | The draft claimed `--validate` "byte-identical" under `PYTHONHASHSEED` 0/999 — but `cflank.py` prints two elapsed-time annotations, which are non-deterministic, so the claim as stated could never hold. Caught by the coordinator running both seeds and diffing rather than trusting the attestation: every figure matched, only the two timing lines differed. Reworded to "figures identical; timings differ" in the workbook + README. Lesson: before accepting a byte-identity claim, check whether the driver prints any wall-clock output — if so the claim needs the figures-only form. |
| 2026-08-12 | Phase39 GCAP research dispatch (seventh direction; landed this commit) | fable (`recon-fable`) | killed mid-dispatch (monthly spend limit), resumed same-agent — resume-first (rescue §3) | The GCAP research recon (top rung, `recon-fable`) was killed mid-dispatch by a monthly spend limit at ~423k tokens / 94 tool uses / ~2.2h, its untracked driver and draft substantially written but nothing committed (research dispatches commit nothing). On reset the coordinator resumed the same agent (SendMessage; rung-pinned fable, no F5 drift) per rescue §3 resume-first; the untracked driver survived intact, no work lost and no defect introduced. The direction then completed and gated clean at landing (five modes coordinator-re-run, byte-identical). |
| 2026-08-13 | Phase39 GUNIF landing verification → corrective pass (`77840be4` → this commit) | opus (corrective, one rung up) | gate-invisible defects caught in coordinator verification: an incomplete status move inside the canonical gap-map cell, plus draft scaffolding merged by **four** consecutive landings | GUNIF appended its (GR-28)(iv) refutation but left the superseded *true-modulo-named-gap* standing in the same §(K-grid) gap-map cell — the canonical per-gap status home — so one cell asserted both; two other §(K-grid) sites stale too. A sweep then found each draft's closing "Coordinator actions at landing" block merged verbatim by E/TCOL/GCAP/GUNIF, reading as pending to-dos for done work; all four audited before deletion, every action verified performed. No gate covers docs prose. Prophylactic: fan-out landing-checklist item 6, parallel to item 2 (added after four landings skipped the README §3 rows). |
| 2026-08-13 | Phase39 cleanup round D-2, §(K-grid) gap-map cell rewrite (`dc4ecc7b` → this commit) | sonnet (builder) → opus (corrective) | gate-invisible defect caught in coordinator verification: a self-reported preservation table attested "unchanged" for a qualifier the same diff removed | The status-preserving rewrite carried its own 35-row preservation table in the commit message; one row — `(GR-4′)`, "off critical path \| unchanged" — was FALSE: the diff had removed that qualifier (and the "conic confinement is dissolved" parenthetical), substituting a near-opposite routing claim. Caught only by diffing the cell; reading the table would have passed it. Lesson: **a self-reported preservation table is an attestation like any other — the coordinator must diff the artifact, not read the table.** The corrective pass settled the question: both senses hold, the cell carries both. |
| 2026-08-13 | Phase39 GEXIST landing verification (`054744a6`) | fable (direction) → sonnet (landing) | gate-invisible defect caught in the coordinator's driver re-run: a headline figure wrong in 2 of the 3 places the draft stated it | The draft's CL10 first-moment figure read `3.40` in its blockquote and confidence table, `3.23` in its body; the driver prints 3.23. Every other headline figure cross-checked exact (220 038 chunks, 4344 tight, 72 120 pairs, 509, 1526, 43/200, 35/60, 120/120). Refutation unaffected (both > 1) — a figure fix, not mathematics, but it was headed for the canonical workbook. Caught only by re-running all five modes (landing-checklist item 1). The same return's "byte-identical across seeds" claim was also loose: sole divergence is a printed wall-clock second. |
| 2026-08-13 | Phase39 cleanup round — coordinator-supplied premises (`153845d8`; the D-3 prompt) | — (coordinator) | **F14 twice in one session**: two coordinator premises asserted as verified, both false; one caught by a subagent, one by a subagent's successor | (i) A "hard ordering constraint" was *committed* claiming D-2's gap-map rewrite would shift every later line number, forcing D-2 before D-1. False — a markdown table row is ONE physical line; file length was unchanged. Harmless order, unsound reasoning. (ii) The D-3 prompt asserted surviving `→ FRICTION [resolved] *title*` pointers "must be repointed or they dangle"; the builder declined **with evidence** (`TACTICS-QUIRKS.md:25` tells readers to grep both files — the convention is title-based). Lesson: measure before writing a constraint into a durable log. |
| 2026-08-13 | Phase39 ninth direction GEXIST — dispatch shape | fable (fresh launch, not a resume) | playbook deviation, deliberate: continuation-resume declined for verdict independence | The selection recon that picked GEXIST was resumable with intact route context — the playbook's continuation shape, and cheaper. Launched fresh anyway: this direction's honest-MISS is a *valuable* outcome, and the agent that argued for the pick would have been grading its own homework. Outcome: a clean MISS returned, with three new theorems, one self-refuted mechanism, and no reluctance to report the target unproven. Deviation judged correct here; continuation stays right where the *arc* continues, not where a *verdict* is being graded. |
| 2026-08-13 | Phase39 GORIENT landing verification → corrective pass (`90e86ec1` → this commit) | fable (direction) → sonnet (landing, corrective) | gate-invisible defect caught in coordinator verification: the landing checklist's own gap-map update re-created a just-fixed changelog defect | GORIENT's landing checklist item 4 (gap-map update) re-created the D-2 changelog defect (`dc4ecc7b`) in the same §(K-grid) cell just fixed: appended "Since GORIENT..."/"GEXIST left the route in..." narrative rather than a current-state rewrite (1373 → 1811 words), plus a duplicate hot-dart-census figure split across the two cells. Caught in coordinator verification of `90e86ec1`, one landing after the cleanup round closed. Corrected here: recomputed from scratch in D-2's register, 1811 → 1731 — above D-2's 1300-1450 band since GORIENT added four new theorems (GR-36-39). |
| 2026-08-14 | Phase39 eleventh direction GDEV prep (`0a38ffa0` → `a8294191`) | fable (selection recon, resumed to prep) | gate-invisible defect caught in coordinator verification: a compression left stale an accounting line the same commit had just falsified | The prep one-lined the settled *Current state* bullets **around** the "(K) arc — thirty-five dispatches, plus four strategy-only passes (… → 08-13)" paragraph but left the paragraph itself as untouched context, so its own selection recon — the fifth such pass — went uncounted in the commit that made it one. Caught by reading the diff's *context* lines, not its changed ones. Lesson: a compression pass must re-read the **counts adjacent to what it merges**; those are the sentences most likely to sit in context rather than in the diff. |
| 2026-08-15 | Phase39 GDEV landing verification (`0e2bd9b7` → `1124910f`) | fable (direction + landing, same-agent resume) | gate-invisible defect caught in coordinator verification: the note's Status header left contradicting its own Hand-off — **third consecutive landing** with a stale status surface | The landing correctly updated *Current state*, *Hand-off*, *Decisions made*, the gap map, the fan-out spec, the labels and ROADMAP — but not the note's top `**Status:**` block, which still read "GDEV is selected and PREPPED …, not yet dispatched — that dispatch is the next concrete task" while *Hand-off* 200 lines below correctly aimed at the twelfth's prep. That header is the first paragraph a fresh session reads. Cf. GEXIST's landing (ROADMAP cell) and GORIENT's (deleted Hand-off slot). Mitigated by landing-checklist item 7; see F17. |
| 2026-08-18 | Phase39 §(K-grid) gap-map cell fourth recompute + cap gate (`2ab3c630` → this commit) | sonnet (builder) | gate-invisible defect (four-peat): mechanical cap gate added instead of a fifth prose recompute | Fourth regression: §(K-grid)'s status cell went `dc4ecc7b` 1274 → `97c9661c` 1373 → `07f6f9b6` 1729 (repair #2) → `0e2bd9b7` 2066 (GDEV) → `2ab3c630` 2328 (GADM) words, each landing appending a since-direction-X clause instead of recomputing. Two prior prose-only repairs (D-2, repair #2) each regressed within 1-2 landings. This commit recomputes again (2328 → 1768 words, no facts/labels dropped) and adds `notes/check-gapmap-cells.py`, a per-cell word cap adapted from `check-log-rows.py`: a cell every landing appends to needs a mechanical gate, not a fifth recompute. |
| 2026-08-18 | Phase39 fourteenth direction GDESC prep (`this commit`) | opus (prep; the direction itself stays mapped fable) | playbook deviation, deliberate: a top-rung-mapped prep dispatched one rung down by user adjudication | The fourteenth's routing was FIXED by GPSA's landed otherwise-clause, so this prep had no selection to make — only spec authoring. With weekly_scoped at 83% the user adjudicated it to opus and conserved fable for the direction's own dispatch (a crux proof attempt, the spend worth protecting). Cost disclosed in the spec exactly as the twelfth's coordinator-authored prep disclosed its own: no independent top-rung reader of the ranking record — cheap here only because the primary is fixed, not competitively ranked. Outcome judged at GDESC's landing. |
| 2026-08-19 | Phase39 sixth fan-out — five concurrent directions (`46152836` … `6fd91065`) | opus ×5 (directions) → sonnet ×5 (landings) | playbook deviation, user-adjudicated: parallel multi-dispatch against the command's serial loop | User adjudicated a parallel wave. Coordinator shape: each agent wrote only NEW files (draft + driver at pinned paths), edited no tracked file and committed nothing; disjoint label ranges pre-allocated per direction; compute/theory tier split (2 licensed to sweep, 3 derivation-first). Outcome: zero collisions, zero tracked-file edits by any agent, all five drafts accepted on verification, five clean serial landings. Three findings were visible only ACROSS directions — see F18. The last landing correctly REFUSED to write this row (its core forbids editing this log); coordinator-authored. |
| 2026-08-19 | Phase39 seventh fan-out — five concurrent directions (`7fbecfa5` … `8e4a3245`) | opus ×5 (directions) → sonnet ×5 (landings) | playbook deviation, user-adjudicated: second parallel multi-dispatch | User re-elected the multidispatch shape over a coordinator recommendation AGAINST it (92% `weekly_scoped`), then supplied the fact that overturned the recommendation — the scoped limit is fable-only. Sixth fan-out's mechanics repeated verbatim: new files only, nothing committed by any agent, disjoint label ranges, compute/derivation tier split. Zero collisions again; five clean serial landings; **two HITs** (CIRR, AGLU) against the arc's prior total of one. Directions were coordinator-picked — no independent ranking of the losers, disclosed in the prep per the twelfth's precedent. |
| 2026-08-19 | Phase39 24th direction CIRR (`7fbecfa5`; draft repaired pre-landing) | opus (recon) → same-agent resume | gate-invisible defect: a claim duplicating a landed compiler-checked theorem | (CH-8) re-derived `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`), strictly stronger (two hubs, no `hcard`). No gate fires — it is an ADDITION, not a break — and the draft's own prose about `class_shape`'s *two-hub* triangle filter pointed straight at the theorem it duplicated. Caught in the coordinator's reasoning-scrutiny pass; a same-agent resume rewrote it as a pointer, and the duplicate sweep the resume mandated found a SECOND partial duplicate ((CH-6)(i), whose mechanism runs inline in that same landed proof). See F20. |
| 2026-08-19 | Phase39 20th + 21st directions YLOC / BALB (`5fc24035`, `5ba6d299`) | opus ×2 | gate-invisible defect: two concurrent siblings derived the SAME identity | YLOC's (GR-65)(i) and BALB's (GR-67)(i) are one statement (`n − #agree = #differ`), independently derived and independently certified (2 270 294 vs 2 188 534 instances), each blind to the other. Label reservations prevent label COLLISION, not content DUPLICATION: both minted inside their disjoint reserved ranges, so no gate, checker or registry sees it. Coordinator landed (GR-65) as the general form and (GR-67)(i) as its matching-anchored instance, keeping the double certification as corroboration. See F20. |
| 2026-08-19 | Phase39 seventh fan-out — three coordinator premises refuted by the directions they primed | opus ×3 (YLOC / AGLU / ZNEQ) | coordinator-authored spec defect ×3, each caught by the dispatch it misdirected | YLOC's (GR-63) refuted the predicted obstruction LOCATION — (GR-52)'s `2 e_H(S)` is a per-hub-subset count valid at every `S`, so it localizes for free and the break is two links earlier. AGLU's (GR-77) refuted the predicted CONSEQUENCE — 3 774 crossing pairs at `n_hub = 8`, so only the maximal family's uncrossing survives. ZNEQ sharpened an incomplete WORDING — a `Z = ∅` negative splits, and only one branch is the (K-tight) event specced; the other is a PENCIL event. One shared cause: extrapolating a landed result's scope to an unmeasured stratum. See F19. |
| 2026-08-19 | Phase39 §(K-grid) cell FIFTH regression (`5ba6d299` → `4edd2143`) | sonnet (landing) → opus (coordinator) | gate-invisible defect: a recompute that PASSED its mechanical cap and accomplished nothing | Instructed to recompute rather than bump, BALB's landing recomputed the close-it cell to 872 words against a cap of 873 — compliant, gate-green, purposeless: the recompute existed to make room for AGLU, the fourth direction landing into that row. `check-gapmap-cells.py`, added at the fourth regression, catches OVERFLOW but not purposeless compliance. Coordinator redid it (872 → 619). A scripted label-set diff then caught `(GR-47)` missing from both cells — eyeballing would have shipped the hole. See F21. |
| 2026-08-19 | Phase39 seventh-fan-out prep (`13ec1f0e` → `d2348090`) | opus (coordinator) | coordinator-authored artifact defects ×2, F17 class, flagged by a landing agent | The prep re-synced `Phase39.md` and the ROADMAP cell but never re-read the fan-out doc's OWN `**Status:**` header: stale by two whole fan-outs, still describing the file as scoping "three independent research directions" when there were twenty-four, and grown to 2139 words of per-direction changelog (recomputed to 209). The same commit nested the wave's five direction headings at `###` where every prior wave's sit at `##`, so `grep '^## .* direction'` silently omitted 20–24. Caught by ZNEQ's landing, not by the coordinator. See F19. |
| 2026-08-19 | Phase39 eighth fan-out — five concurrent directions (`1f02f73a` … `b83fed26`) | opus ×5 (directions) → opus (coordinator landings) | playbook deviation, user-adjudicated: THIRD consecutive parallel multi-dispatch | Third wave of the shape, and the first whose check-in **moved a standing constraint** — ZNEQ's held-out `σ > 0` disproof hunt was authorized, becoming SIGZ, with the direction-A pivot rule in force and the adjudication moved from before-dispatch to at-return. All five landed; four reservations consumed exactly, SIGZ returning one label. Selection, tiers and reservations coordinator-set again, so the twelfth's no-independent-ranking disclosure applies a third time. No E-clause fired; E3 ARMED throughout. |
| 2026-08-19 | Phase39 eighth fan-out — FIVE defective spec clauses (`1f02f73a`, `280e2e1f`, `5e8cb62c`, `ca862924`) | opus ×4 | coordinator-authored spec defect ×5, every one caught by the dispatch it primed | Four of five directions corrected a clause in their own spec: GTMPL an **empty** case (a binding chunk *is* an obstruction, so a realized AA-glue is never fully-good); GFLOW a wrong **instrument** (min-cost flow — the objective is a parity count); OSCHU an over-strong **restatement** (`dimK ≤ 1` sufficient, not equivalent) *and* a wrong **conditionality** (conditional on (GR-10) — false at directly-certified shapes); SIGZ an over-strong **consequence** ((a₂) free unconditionally — only the counting half closes). **Three inherited** from landed hand-offs, **two** written at prep. See F22. |
| 2026-08-19 | Phase39 §(K-out) + §(K-grid) gap-map cells (`ca862924`, `b83fed26`) | opus (coordinator) | gate-invisible defect ×2: an unescaped pipe SILENTLY DOWNGRADES the cap gate | Twice in two landings, writing cardinality notation **unescaped** inside a gap-map row made `check-gapmap-cells.py` fall back from per-cell to combined-remainder capping — and the combined check **PASSED** while the status cell alone was 31, then 121, words over its own cap. Escaping restored `split` parsing and exposed the real overruns, which were then paid by trimming. **A passing run of this gate is not evidence a cell is within cap unless the row still parses as `split`.** See F23. |
| 2026-08-19 | Phase39 eighth fan-out — both gap-map caps bumped after recompute (`ca862924`, `b83fed26`) | opus (coordinator) | playbook-adjacent: first same-day bump of BOTH capped rows, in the sanctioned order | §(K-out) 800→950 and §(K-grid) 2035→2715, each **after** an honest recompute rather than instead of one: §(K-out)'s pre-existing content went 649→431 (34%) at SIGZ then a further ~65 off at OSCHU; §(K-grid)'s went 1706→1730 while absorbing six new labels, each later landing trimming its own block. The rows absorbed **eleven** and **eighteen** new theorems in one day. Reasons recorded in the script itself, per its docstring. |
| 2026-08-19 | Phase39 28th direction OSCHU — its criticism of a sibling landing, refuted (`ca862924`) | opus | dispatch-authored claim about coordinator work, wrong on verification | OSCHU reported that SIGZ's landing skipped the wave's mandated §(K-out) recompute, reading the cell's end state (666) against the spec's ≤ 560. The recompute **did** happen — pre-existing content 649→431, past target — after which SIGZ's own 235-word block brought the cell to 666. But the misreading was **invited** by the coordinator's asymmetric wording: the §(K-grid) obligation said "recompute … before adding its own content" and the §(K-out) one omitted that clause. Fix is to the spec, not the landing. See F24. |
| 2026-08-25 | Phase39 harness move-down payment (`278a4761`) | sonnet | killed dispatch (API timeout mid-baseline) → resumed, clean | The builder died on a request timeout during the ~8-min `gflow --validate` baseline, BEFORE any edit (tree verified untouched). Resumed via SendMessage on the rung-pinned variant (F5 rung-stable); it re-ran unverifiable baselines, landed the full move-down with byte-identical gates, and honestly disclosed the documented `yloc` three-invocation split. Second clean F4-pattern kill-resume; nothing salvaged because nothing was lost. |
| 2026-08-25 | Phase39 40th direction OQRANK (`090899f1`, `a3f3cb90`) | fable | F6 park on a RESEARCH dispatch + a spend-limit kill; both cured by resume | The dispatch parked its ~40-min census in a background run with a monitor and returned a mid-flight status instead of a verdict — the F6 shape's first appearance on a *research* dispatch. Its prompt carried the foreground mandate in prose, but NOT the validated one-line F6 reminder, which the playbook specifies for build dispatches only. A corrective resume mandated the chunked foreground split (SIGZ precedent); a later spend-limit kill resumed rung-stable. All figures re-verified from foreground runs. **Lesson: put the F6 line on any dispatch with a compute leg, not only builds.** |
| 2026-08-26 | Phase39 gap-map status-cell staleness, repaired at the GBLAW landing (`e8676558`) | fable (coordinator) | gate-invisible defect caught in verification (F17 shape, new surface) | The §(K-grid) row's STATUS cell still read "≤ 12 modulo (GR-R1) … (GR-C2) stays OPEN" three landings after GFLIP/GCHEAP/GPRICE settled both — each landing updated only the close-it cell, so the row contradicted itself internally. No gate reads one cell against the other (`check-gapmap-cells.py` caps size only), and the fresh-session reader hits the status cell first. Caught by the coordinator's landing re-read; repaired in the same commit. **Lesson: a landing that edits a gap-map row edits BOTH cells or states why not — the two-cell row is one more two-copy surface of the F17 family.** |

| 2026-08-26 | Phase39 44th direction GHWIT (`abe0d46a`, `ef0c8907`) | opus | rung substitution — first single direction below top rung; outcome a HIT | Fable conserved at the user's session-config selection (`weekly_scoped` 92 % critical), so the playbook's nearest-available substitute ran: `recon-opus`, against six `recon-fable` predecessors as the calibration baseline. It **refuted (GR-104)(i)**, closing the four-direction GPRICE→GBLAW→GXESC→GHWIT thread negatively. The agent's own read: the win came from a cheap bitset re-implementation making 6.2M exhaustive instances affordable plus a climb on a new objective, not a deeper derivation. **One data point that a compute-shaped research leg is not rung-limited.** |
| 2026-08-26 | Phase39 GHWIT verification-bar overclaim (`ef0c8907`) | opus | gate-invisible defect caught in verification → corrective resume, closed | The draft claimed **four** independent exact models and pinned a `max\|R\|` quadruple; the shipped driver implemented **three** and its own docstring said so, and nothing in the tree produced that figure. Every gate was green — the defect sat in the *verification-bar sentence itself*, the load-bearing claim for a refutation. Root cause the agent named: it wrote the bar from what it had **run** (a scratchpad probe) rather than what it had **shipped**. Resume landed the model as an asserting device. See F25. |
| 2026-08-26 | Phase39 GHWIT — coordinator shaping block refuted by the direction it primed (`ef0c8907`) | opus (coordinator) | coordinator-predicted-obstruction category, SECOND instance | The dispatch's `route` block asserted the clause "reduces to *some maximum has `\|h\| = 2`*", derived by the coordinator from (GR-115)(iii). False: a landed witness has `min \|h\| = 3` across its whole maximum family, and the refuting pair defeats even `\|h\| ≤ 3`. Harmless here — the agent tested rather than assumed it — but it is the second phase instance of `RESEARCH-ARC.md`'s watched candidate (a coordinator prediction refuted by the direction it primed). **Two instances now; promotion-eligible at a third.** |

| 2026-08-26 | Phase39 45th direction GMINM (`e4911af6`, `3ff28b76`) | opus | a landed headline RE-PRICED by the next direction — no defect, a routing error | GHWIT's landing headlined *"per-matching (b′) at the constant 2 is FALSE"*. True, and irrelevant: GMINM found (b′) has THREE inequivalent readings and the ledger consumes the third (`gdev.min_dev` computes a **difference of minima**), so five directions had attacked a statement the consumers never used. Verified against landed source, not docstrings; the separation follows from landed figures alone ((GR-67) parity + W3's odd ledger gap). **No gate could have caught this** — every figure was right. See F26. |
| 2026-08-26 | Phase39 46th direction OGEOM (`7e5d968a`, `aa451646`) | opus | coordinator-verified premise the driver only CITED | (OC-47)(i)'s class-uniform claim ("every cycle and bouquet is dead") rests entirely on girth ≥ 7, which the driver **cites to (Λ4)** rather than asserting. Checked independently against the workbook: it holds, forced by `hnoRigid`. Recorded because the pattern is general — **a premise a driver cites is outside its F11 coverage by construction**, and is exactly where a landed-but-unchecked assumption would hide. Also: `--validate` runs 645 s and does not fit the 600 s foreground budget; the two-invocation split is the recorded gate recipe. |
| 2026-08-26 | Phase39 47th direction BATTAIN (`50e90d6a`, `def76ed2`) | opus | dispatch corrected a LANDED reading, and caught its own methodological trap | (BE-9)'s *"no T2 is producible by this harness"* was too strong: a universal cap **is** producible by argument ((BE-13)), and what blocks T2 is structural (forcing the cone needs a triangle; the habitat is triangle-free by `hnoRigid` — coordinator-verified in `Escape.lean:411–418`, not a docstring). Separately, its first sweep reported three shortfalls from **one seed each**; rank being lower semicontinuous, a one-seed shortfall proves nothing — it found and fixed this before returning. See F27. |
| 2026-08-26 | Phase39 48th direction BZAVOID (`d87693ae`, this commit) | opus | coordinator-predicted-obstruction category, **THIRD instance — promotion now DUE** | The spec's flagged-to-be-tested geometric reading SPLIT: its transversality/dimension-count half is refuted **structurally** (containment needs only `dim Y° ≤ dim Z`, satisfiable at every hubbed graph), its "deform off the canonical point" half **survived and got priced**. The lesson is the flagging, not the geometry: naming a reading as to-be-tested *with its evidence stratum* (F19's own suggested fix) is what made a half-right prediction legible as a split rather than silently inherited. **Third instance**, so RESEARCH-ARC's watched candidate is promotion-eligible; ZSHEAR adds a fourth and the promotion lands with it. |
| 2026-08-26 | Phase39 49th direction ZSHEAR (`d87693ae`, `4c62808a`) | opus | coordinator-offered REPAIR decided negative — **fourth instance, candidate PROMOTED** | The spec offered a graph-indexed product action (`so₃^V`) as the obvious repair once the global shear died, flagged to be tested with the thinness of its evidence stated. Decided **negative in both readings**: not form-preserving off the diagonal, and the carrier-side family that *does* pass §4.6's filter is an existing chart re-labelled. Fourth coordinator prediction refuted by the direction it primed, so `RESEARCH-ARC.md`'s watched candidate is **promoted to *Ready* §7** in this commit. The lesson is unchanged and is about framing: every one of the four was *tested rather than inherited* because the spec named its evidence stratum. |
| 2026-08-26 | Phase39 51st direction ZJACOB (`164075cb`, this commit) | opus | coordinator-predicted deaths refuted **AS DIAGNOSES** — fifth instance, and the first to fault the FRAMING | The spec named two likeliest deaths. Both wrong, and wrong deeper than a bad guess: *(i)* "the cone may not be an LCI of the expected codimension" **mis-locates a conclusion as a checkable hypothesis** (by (JC-2) that condition IS properness plus a codim clause); *(ii)* "needs a hypothesis the pencil stratum violates" — the stratum does not violate it, it **is** it. First live outing of the one-commit-old `RESEARCH-ARC.md` **Ready §7** rule, and it earns the promotion: the spec labelled these *to check first* rather than asserting them, so the direction reported the framing error instead of working around it. |
| 2026-08-26 | Phase39 50th direction BINDUC (`164075cb`, this commit) | opus | a LANDED headline re-scoped by the next direction — second instance this session, and again no gate could see it | BZAVOID's (BE-15)(ii) was landed, verified and reported as closing the falsification arm *"by an argument at every graph, cap-free"*. It closes the **adjacent-pair/triangle** mechanism only: the general rule fires once a closed neighbourhood holds three independent pinned points, needing **no triangle** (`K_{3,3}` forced flat, triangle-free), so forced classes can be coarser and the *triangle-covered ⇒ `def₂ = 0`* step misses them. General mechanism now MEASURED-empty, not proved. Same shape as GMINM (F26): every figure was right, and **the wrong sentence was the one no driver tested** (F11). Corrected in place at four sites. |
| 2026-08-26 | Phase39 coordinator SPEC ERROR, caught by the dispatch it primed (`164075cb`) | opus (coordinator) | coordinator artifact needing a subagent's verification tier — RESEARCH-ARC §7's second half, first logged instance | The BINDUC spec asserted that `minimal_kdof_reduction`'s `hcontract` is *byte-for-byte* the phase's parked carried item. **False.** The principle quantifies over `IsMinimalKDof n 0` with a richer IH; the phase's (`Escape.lean:451`) quantifies over `Loopless` with `V(G').Nonempty` only — same obligation *shape*, phase's **strictly stronger**, so instantiating yields a **sibling**. The trap *conclusion* stood on the independent ground that the principle cannot reach `∀ G`, which is why the error was harmless — but it was a claim I stated as verified from a signature read, and it was wrong. |
| 2026-08-26 | Phase39 52nd direction BTWOCUT (`df0c5dac`, this commit) | opus | coordinator prediction CONFIRMED (first time), and disclosed caps paying off as a targeting mechanism | First coordinator prediction in the arc **CONFIRMED** rather than refuted, after five straight refutations. The spec asked whether BINDUC's general-position obstruction was real, given its own cap (BE-22)(v) disclosed the pieces' moduli were **uncounted**; counted, they run 4–26 against the gauge group's 7/5 and 16/16 splits reach the criterion. **The calibration point:** §7's rule is about *framing*, not accuracy — the labelling that made five wrong predictions legible made this right one checkable. The dispatch still refused to overclaim: no dimension count is an obstruction proof, and (BE-22)(v) stands. |
| 2026-08-27 | Phase39 53rd direction BIMAGE (`bbb84c23` prep, this commit) | opus | **gate-invisible defect: a "follows from landed lemma X" clause X does not support** — caught by the coordinator's acceptance check, not by any gate | The draft twice wrote that the SP recursion's residue is *"the R-node, which (BE-25)(iii) already makes rigid"*, and the shipped **driver printed the same sentence**. (BE-25)(iii) covers the **leaf** R-node only; an internal one is `K₄ + ear(m)`, `δ ∈ {4,5}`. The tell was **internal contradiction**: the same return ranked the R-node as its own open successor (3). Lesson — the playbook's *"open X's actual statement"* rule must also be run against a **prose** clause in a docs-only arc, and the fix has to reach the **driver's printed prose**, which no gate reads. |
| 2026-08-27 | Phase39 53rd direction BIMAGE — driver auto-backgrounded (`bbb84c23`, this commit) | opus | **F6, seventh instance** — self-disclosed by the dispatch and self-corrected | One driver run auto-backgrounded for a missing explicit tool `timeout`; the dispatch re-ran it in the foreground and stated that every quoted figure came from a foreground run. Logged because F6's whole value is the recurrence count: the in-prompt reminder line was present and the park still happened, so the reminder **reduces** the shape without eliminating it. No figure was affected. |
| 2026-08-27 | Phase39 gap-map row recompute at the BIMAGE landing (this commit) | opus (coordinator) | **RESEARCH-ARC §6 recompute-not-bump, and the scripted label set-diff earning its keep** | Appending BIMAGE's clause put the `(K-bare)` row at 1 514/1 600 words — gate-compliant, 86 words of headroom, with three successors queued on the same namespace: exactly the *pointless recompute* §6 names. Folded the KBARE-FALSIFY/BATTAIN clauses instead → **1 402**. The scripted set-diff **refused the first write**, catching five dropped code spans; each was then verified present in the workbook body before being allowlisted, one of them (`137 = 138 − 1`) surviving only in a differently-worded body sentence. By eye, all five would have gone silently. |
| 2026-08-27 | Phase39 54th direction BEARCASE (`cb6c1a4a` prep, this commit) | opus (coordinator) | **a recon's own RANKED-SUCCESSOR statement transcribed verbatim into a hand-off and a spec, and it was FALSE** | BIMAGE's successor (1) demanded `dim(rho_1 cap Z) <= dim Z - c2`. That is unsatisfiable at `delta_1 >= 5` — `dim(A cap Z) >= dim A + dim Z - 6`, `dim Z` cancels — i.e. **one line of Grassmann**. The coordinator copied it into `notes/Phase39.md`'s hand-off item 1 and into the BEARCASE spec unchecked, so the dispatch was **sent to prove a false statement** and had to refute it first. The playbook already says a build agent's hand-off route claim is a recon verdict needing verification; **this extends it to a recon's own successor ranking**, which reads as settled precisely because the direction that wrote it just succeeded. No measurement was affected — the landed driver tests the correct form. |
| 2026-08-27 | Phase39 54th direction BEARCASE — semicontinuity gap (this commit) | opus | **gate-invisible defect in a PROVEN-labelled claim, caught by reasoning scrutiny** | (BE-37)(i) justified the quantifier collapse by *"a difference of lower-semicontinuous rank functions is upper semicontinuous"* — **false in general**. Coordinator witness: `V(t) = <(1,0,0),(0,t,0)>`, `X = <(0,1,0)>` gives `dim(V cap X)` = 1 generically, 0 at `t=0`. True exactly where `dim rho_1` is CONSTANT — the attaining locus, which is where the claim is posed, so all three consequences stand. The missing hypothesis was supplied at landing. Lesson: a **one-line justification** under a PROVEN label is where to spend scrutiny; the conclusion being right is not evidence the reason is. |
| 2026-08-27 | Phase39 gap-map row FULL recompute at the BEARCASE landing (this commit) | opus (coordinator) | RESEARCH-ARC §6 follow-through — the deferred recompute done rather than deferred again | The BIMAGE landing recorded that a seventh landing on this namespace *"needs a fuller recompute first, not another clause"*. Done: the `(K-bare)` status cell rewritten as a **current-state paragraph** instead of six dated *"Since Steps…"* clauses — **1 409 -> 1 130 words while absorbing a full direction**, 470 words of headroom (was 86 two landings ago), reader cost ~3 076 -> ~2 550 tokens. Scripted set-diff again load-bearing: 28 dropped tokens, each verified body-present, and **four restored** as current-state rather than historical (`Y° ⊄ Z(G)`, `Z(G)`, `HasPencilRealization`, `dim Y° ≤ dim Z`). |
| 2026-08-27 | Phase39 55th direction BEARFULL (`e89c7d41` prep, this commit) | opus (coordinator) | **a coordinator ROUTING hypothesis refuted BY A THEOREM — the best outcome shape for a labelled guess** | The spec asked whether an open ear decomposition makes the ear case *itself* the induction step, retiring the internal R-node. It does not: chord-free ⇒ the last ear's interior has degree 2, so **every min-degree-≥3 graph forces a single-edge ear**, putting the chord gap **exactly at the R-nodes it was meant to retire**. RESEARCH-ARC §7 worked as designed — the spec named the provenance as thin (no measurement, no workbook result, 0 grep hits), named both gaps up front, and asked for a verdict not a preference, so the refutation came back as a **theorem plus a usable reformulation** rather than as a muddle. Sixth of the last eight coordinator predictions decided by the direction it primed; third decided negative. |
| 2026-08-27 | Phase39 gap-map integration at the BEARFULL landing (this commit) | opus (coordinator) | **a recompute does not hold if the next landing APPENDS — caught on my own draft** | The first draft of this landing's gap-map edit was a **374-word dated clause** (*"Since Steps BE38–BE42 (BEARFULL, …)"*) — **exactly the changelog shape the BEARCASE recompute had removed from this row two landings earlier** — taking the cell to 1 504/1 600 and spending the whole 470-word headroom in one go. Discarded; the content was **integrated into the existing current-state sentences** instead (the merge-theorem sentence became the short-cycle law; the residue sentence absorbed the 96.2 % result; the routing verdict joined the closed-routes list), landing at 1 402. **Lesson for RESEARCH-ARC §6:** "fold the clause in normally" is licence to *edit sentences*, not to add one. |
| 2026-08-27 | Phase39 note cap: RELOCATION not compression (this commit) | opus (coordinator) | the phase-note gate binding three landings running, with folds recovering only 2–5 lines each | Three consecutive landings compressed *Decisions made* with real deletions; each recovered 2–5 lines and the note stayed at 578–582/580 because it is **forward-weighted and the forward part is what grew** (343 vs 104). A fourth fold would have been theatre, and my own watch-item text describing the problem **pushed the note 2 lines over**. Fixed by **relocating** the `**Status:**` header's *Conventions* and *Canonical homes* paragraphs — **stable reference, not status** — verbatim to `notes/Pencil-structure.md`, leaving a pointer: **572/580 lines, 468/525 words**, nothing deleted and no cap bumped. The reusable question is *"what here is reference rather than status?"*, not *"what can I cut?"*. |

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
- **F2 — pinned exemplar = the prose S=1.** Promoted to the playbook
  (*Raising S* + the shaping-block list) 2026-07-09; pruned at the
  Phase-34 close (details in git history).
- **F3 — verification-mandate cost signature.** Promoted to the
  playbook (the cost-outlier bullet's benign-shape carve-out)
  2026-07-09; pruned at the Phase-34 close (details in git history).
- **F4 — continuation dispatch (same-arc resume).** Promoted to the
  playbook (step-3 *Continuation dispatch* note) 2026-07-10; pruned at
  the Phase-34 close (details in git history).
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
  *Validation 2026-07-17/18 (Phase 34, through close):* with the
  promoted in-prompt line on every build dispatch, all ~18
  build/design dispatches across the phase (incl. the three close-out
  slices) ran gates foreground — zero park instances (one 8th-instance
  concurrent-build wobble early on, self-recovered inline; none
  after). **Finding closed as stable at the Phase-34 close:** the
  layered mitigation (core mandate + per-prompt F6 line) holds;
  further recurrences get a new row citing this entry.
- **F7 — the internals tactic-golf phase runs clean at low rungs
  (Phase 36 AUTOMATE).** A pure tactic-smell sweep phase ran as
  recon(opus, design-settle+pilot) → 4 sonnet sweep slices → opus
  phase-close, **zero exceptions across all 6 dispatches** (no
  escalation / probe / BLOCKED / gate-defect — hence no Log rows). The
  recon-first design-settle (it fixed the annotation policy = ∅, the
  build-neutral gate, and an S/P/B-rated slice decomposition up front)
  drove every downstream slice to a clean S=2 sonnet dispatch — a
  concrete win for *Raising S is the coordinator's cost lever* (already
  in the playbook; no new promotion). The empirical tactic lessons the
  slices produced (the closing-vs-goal-shaping `rw`→`simp only`
  discriminator; the three defeq-fragility shapes — heartbeat timeout,
  max-recursion, structure-projection auto-reduction) live in
  `TACTICS-GOLF.md` §7, not here. Template for the queued **AUTOMATE-Z**
  (the deferred `Molecular/` fragility-zone sweep): keep the strict
  per-file build-neutral gate + real-`lake build` confirm, but that zone
  is opus-minimum and defaults NO-GO.
- **F8 — a chart/WF-style predicate's conjuncts are unverified until
  something INSTANTIATES them (Phase 39 W5).** A well-formedness
  predicate landed with an unsatisfiable conjunct (unconditional
  selector requirement, impossible at any ≥4-distinct-neighbour body)
  and rode through two gate-clean slices, because its only landed
  consumer was a by-construction theorem that *consumes* WF as a
  hypothesis — nothing instantiated it at a concrete graph until the
  re-seeding assembly two slices later (2026-07-24 row). This is the
  known "deferred hypothesis satisfiable?" failure surface
  (coordinator command step-4) at the *predicate-definition* level:
  the satisfiability trace must hit new `WF`/feasibility predicates at
  the COMMON graph shapes (degree-2 vertices, dense bodies, the design
  doc's own test graphs), not just typecheck the headline statements.
  Cheap mitigation validated same-day: when a dispatch lands a new
  conditioning/WF predicate, the coordinator's verification asks "what
  concrete instance satisfies this?" — a one-`lake env lean` witness
  or even a prose trace at K4/C4 would have caught both conjunct gaps
  at W5-L2.
- **F9 — a design pass's per-arm obligation verdicts ("free",
  "vacuous", "mirrors landed X") are unverified until a builder
  confronts them; prompt the confrontation explicitly (Phase 39 W5).**
  Three consecutive W5 leaves each carried a spiked design-pass verdict
  that failed at first contact: L4's WF conjuncts (F8), L5's
  "parallel classes vacuous" (a dropped qualifier turned a hub-scoped
  refutation into a false general claim), and L5's cut arm ("mirrors
  the landed panel sibling" — gapped on both sides of the IH
  consumption, one gap unknown to the recon that sharpened it). What
  worked, twice in one day: an in-prompt line telling the builder to
  *re-derive the spiked plan against the CURRENT definition bodies and
  return the refutation instead of building on it* — both builders
  converted silent wrong-building into compiler-checked refutation
  returns with honest route-neutral slices. This is the derivation
  guard (coordinator step 2) aimed at *arm-obligation verdicts* rather
  than statements; cheap, and it composes with F8's
  what-instance-satisfies-this check. Corollary for rating: an arm
  re-derivation against a conditioned motive is P≥2 even when the
  design doc calls it "small"/"free" — reserve P=1 for arms whose
  vacuity guard is already landed and named.
- **F10 — diff a design PIN against the phase's OWN recorded Blockers
  at pin/dispatch time (Phase 39 W5-L6 habitat arc).** The L6 arc
  produced THREE optimistic-pin refutations, each caught cheaply by a
  recon/spike before any wasted build. The sharpest: the L6b leaf was
  pinned with `hcard : ∀ v, closedHubNbhd ≤ 3` as its ONLY hypothesis,
  which rode "L6b UNCHANGED" through two later recons — while the phase
  note's *Blockers* section ALREADY recorded that the triangle-hub
  mechanism (`not_pencilNondegFeasible_of_triangle_two_hubs`) refutes
  *any* purely-combinatorial `≤3`-closedHubNbhd feasibility criterion.
  The pin contradicted a recorded refutation and was killed at first
  build contact (a bank-authorized spike). No gate reads a pinned
  hypothesis against recorded prose, and F8/step-2's def-body check
  does not cover a pin-vs-Blockers contradiction. **The coordinator
  check that fires in time:** before dispatching a build on a pinned
  leaf, diff its hypotheses/signature against the phase note's
  *Blockers* + the design doc's recorded counterexamples — now folded
  into the step-2 derivation guard. Corollary (validated 3×): on a
  research phase where design pins outrun verification, recon/spike-
  first — including **bank-authorized spikes** (bank the clean sub-
  pieces, revert+map the hard residual) — keeps every refutation
  cheap; the pattern completed W5-L6 (habitat feasibility) with zero
  wasted builds despite three false pins.
- **F11 — in an informal-research arc, the corrective mechanism is the
  NEXT pass, not coordinator scrutiny (Phase 39 kernel-(K) arc).** Three
  consecutive passes each corrected a predecessor's recorded claim: the
  degenerate-sampler contamination (2026-08-02), then two "proven
  pieces" of the tetrahedral collapse (2026-08-05 — an
  acyclic-vs-proper colouring conflation and a "forced" dictionary
  entry). Every one survived a coordinator reasoning-scrutiny pass that
  reproduced the drivers faithfully, because the defects sat in claims
  no driver *tested*: a premise discharged against the wrong invariant,
  an exhaustiveness assertion backed only by per-instance asserts, a
  sampler whose degeneracy suppressed the phenomenon it sampled. The
  coordinator checks that DO fire: (i) re-run headline **figures**, not
  just `--validate` drivers; (ii) for each "proven piece", ask *which
  driver tests THIS sentence* — an untested sentence is a conjecture
  however proven its neighbours; (iii) treat "forced"/"exhaustive"/
  "the only" as their own claim class. Corollary for planning: on such
  an arc, price each pass as including a correction to the last one,
  and prefer commissioning the **next pass** over building on the
  current pass's optimistic residue.
- **F12 — when a return flags a stale claim in a named cell, grep the
  whole file: the same claim usually also sits in the body prose that
  the cell summarizes (Phase 39 fan-out landing).** Direction B's return
  explicitly flagged that directions A/C left a `(T5) frame at
  ℓ = 5,6` route standing in the gap map's `P21` row, which its Step 7
  refutes. The coordinator's landing spec pinned *that row*, and the
  builder fixed it thoroughly — but the identical claim also lived in
  §(K-slide) *Step 5*'s "Division of labor" prose, which the row
  summarizes, and rode onto master asserting a route refuted by a
  section landed in the same commit. Nothing gates this: no build, no
  `checkdecls`, and the flagged cell *was* correct afterwards. The fix
  is the scope-pin, not the builder — pin "every instance in the tree,
  found by grep", exactly as the CLAUDE.md deletion/retirement variant
  requires for deleted decl names. Generalization: a gap-map / status
  table is a *summary* of body prose, so a correction to a summary row
  is presumptively a correction to at least one body paragraph too.
- **F13 — a guard is not verified by existing; a sampler defect that
  *implies* the measured quantity is invisible to every downstream
  check (Phase 39, 2026-08-06).** The 2026-08-02 `plane_basis`
  contamination produced a mitigation — `star_span_ranks`, documented
  in its own docstring as the genericity guard against that artifact.
  It does not catch the coincident-hinge-line degeneracy, which
  *forces* `λᵢ = 0`, i.e. manufactures the phenomenon under
  measurement in ~9% of frames. Nothing gates this: not the build, not
  the conjuncts, not figure invariance (a contaminated figure
  reproduces perfectly). Two lessons. (i) **Classify a figure before
  trusting it:** *rates* are distorted by degenerate frames, while
  *identities* and *pointwise existence witnesses* are conservative
  under them (junk points make an ∀-claim harder, not easier) — this
  is what let §(K-ann) stand while §(K-out)'s rates needed restriction
  to 318 clean frames. (ii) **A guard needs its own adversarial test**,
  i.e. a witness the guard is supposed to reject; a guard that has only
  ever been observed passing is untested. Corollary for the
  coordinator: when a mitigation for a recorded defect turns out
  ineffective, that is the trigger for the deliberate re-baselining
  round, not another caller-side patch.
- **F14 — coordinator premises are as unverified as a subagent's, and
  the cheap check is measurement (Phase 39, 2026-08-06).** Four
  coordinator-supplied premises were refuted in one session, each by a
  measurement rather than an argument: "a directory is a namespace"
  (the collision it would fix was already cross-file, 6 files);
  "compress `Phase39-design.md` per the `Phase22` precedent" (wrong
  precedent — 8 anchors there vs 119 here, so the disposition is
  freeze); "option B and U2 are the same object" (directionally right,
  specifically wrong); and "`Gr(3,6)` is the smallest finite-type
  Grassmannian" (every `Gr(2,n)` is type `A_{n−3}`). All four were
  passed in `route`/`scope-pin` shaping blocks — which the playbook
  restricts to *coordinator-verified information* — so the failure was
  labelling reasoning as verified. Mitigation that worked: every one of
  those prompts also told the agent that refuting the seed was a fully
  successful outcome, and every refutation came back explicitly. **Mark
  coordinator hypotheses as hypotheses in the shaping block**; reserve
  the verified register for things actually opened in source or re-run.
  *Fifth instance, 2026-08-06 (harness round S1), with a mechanical cause
  worth naming on its own:* a `scope-pin` block "corrected" the harness
  README's three-catch-site claim down to one, from a `grep … | head -20`
  read as exhaustive. The README had been right. **A truncated search is not
  a verified enumeration** — when a count is going into the verified
  register, drop the pipe (or the `-m`/`head` cap) and count the full
  output; if you keep the cap, write "at least N", which is what the search
  actually established.
- **F15 — the 600 s foreground ceiling has no carve-out in the
  foreground-gates mandate, and a subagent's background job dies with its
  turn (Phase 39, 2026-08-06).** F6 mandates foreground gates with an
  explicit `timeout` and both cores forbid `run_in_background`/Monitor on
  them. Neither says what to do with an invocation that *cannot* finish
  inside the harness's 600 s ceiling — the numerics harness has four
  (`flanks.py --limit` at 762 s is the worst). S1's first attempt did the
  natural thing: backgrounded it, then ended its turn to park. The job died
  with the turn, never wrote its `.rc`, and left a 0-byte output; the
  coordinator re-ran it. **The shape that works, validated twice (S1's retry
  and S2): start the over-ceiling invocation backgrounded FIRST, run the
  foreground work alongside it, and collect it before the turn ends — never
  background it with nothing left to do.** That is not in tension with F6,
  whose failure mode is *ending a turn while waiting*; this shape never
  waits. Recorded where a numerics dispatch plans its run
  (`notes/scripts/README.md` *Hard rule — figures do not move*); the agent
  cores still say nothing, so a dispatch prompt naming an over-ceiling
  invocation should carry the line.
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
- **F17 — a document's own header is a status surface, and it is exactly
  what a section-scoped edit does not re-read (Phase 39, 2026-08-13…15).**
  Three consecutive direction landings each updated the sections they were
  told to update and left a *different* status surface stale: GEXIST's the
  ROADMAP Status cell, GORIENT's the *Hand-off* next-task slot (deleted
  outright, with the prep text it should have replaced), GDEV's the phase
  note's top `**Status:**` block — which ended up asserting the direction
  was "not yet dispatched" in the very commit that landed it. Each was
  caught only in coordinator verification, each cost a follow-up commit,
  and no gate covers any of them: they are prose, and prose that contradicts
  other prose still builds green. The fix that has repeatedly worked here is
  **a numbered checklist item enumerating the surfaces**, not a prose
  exhortation to be careful — this is the third instance of the
  per-landing-chore shape after the `notes/scripts/README.md` §3 invocation
  rows (four landings skipped) and the scaffolding-block strip (four
  landings merged it), both of which stopped recurring once itemized.
  Mitigations: `notes/Pencil-fanout.md` landing-checklist item 7 (the
  four-surface sweep) and CLAUDE.md's per-commit bullet, which now names the
  status header alongside the sections. Coordinator corollary: verify the
  surfaces a landing did **not** touch — the ones it did are self-reported
  in the return, and a return that lists seven correct updates reads as
  complete precisely when the eighth is missing.

- **F18 — a parallel fan-out surfaces findings no single agent can
  see (Phase 39, 2026-08-19).** Five directions ran concurrently with no
  contact between them, and three results existed only in the
  *comparison* of their returns, not in any one of them: (i) GBAL's
  now-proven input (X) and GLAW's newly-named input (Y) are the
  whole-graph and proper-chunk instances of **one** inequality — and the
  proof does not transfer, which is the next real question; (ii) FRES and
  OCON independently landed on **chart irreducibility** as load-bearing
  and owned by nobody, one via an imprecise landed definition
  ((ANH-9)(ii)), the other as a required input of its own reduction
  ((OC-19)); (iii) LTWO's `outer.py --patterns` cap artifact was the
  *second* instance of the cap-exhaustion hazard recorded for §(K-grid)
  one day earlier, which is what showed the hazard to be harness-wide and
  promoted it to `notes/scripts/README.md` §4. Two coordinator
  corollaries: budget verification time for an explicit **cross-return
  pass**, not only per-return checks — that pass is where the compounding
  value of a fan-out is actually realized; and choose directions in
  **different sections**, which is what made the independence real and
  kept the five drafts collision-free in one working tree.

- **F19 — coordinator-authored artifacts need the same verification
  tier as subagent returns (Phase 39, 2026-08-19).** Four of four
  coordinator contributions this wave needed correction, and three were
  caught by the directions or landings rather than by the coordinator: two
  predicted obstructions refuted (rows above), one incomplete spec
  wording sharpened, and two artifact defects in a single prep commit.
  The playbook's verification tiers are written entirely for *subagent*
  returns; nothing subjects the coordinator's own specs, predictions and
  doc edits to the same reading. Two rules fall out, both cheap: a
  **predicted obstruction written into a spec must name the stratum its
  evidence comes from** — both false premises extrapolated a landed
  result past the stratum where it had actually been measured, which is
  visible on the face of the claim; and a **coordinator commit must run
  the same F17 status-surface sweep it enforces on every landing**, since
  the prep commit that skipped it is the one that went stale.

- **F20 — label reservations prevent collisions, not duplication; two
  checks are missing (Phase 39, 2026-08-19).** Both duplicate defects
  this wave were **additions, not breaks**, so no gate, checker or
  registry could see them. (i) **Against landed Lean:** any claim
  statable in the project's own idiom may already be a green theorem —
  and a zero-hit vocabulary grep makes the audit cheap rather than
  exhaustive (the tree contains no algebraic geometry, so an
  irreducibility claim cannot be duplicated at all, and the real audit
  reduces to the claims about ranks and independence, which is exactly
  where both duplicates sat). (ii) **Across concurrent siblings:** two
  directions in one wave derived one identity in disjoint label ranges;
  this belongs in F18's cross-return pass, which is where a fan-out's
  compounding value is realized. Add both to the fan-out landing
  checklist.

- **F21 — a mechanical cap catches overflow, not purposeless
  compliance (Phase 39, 2026-08-19).** The fifth regression on the
  §(K-grid) gap-map row was the first where the *gate passed*: the cell
  was recomputed to one word under its cap, which satisfies
  `check-gapmap-cells.py` and defeats the point, since the recompute
  existed to make room for a known-pending landing. A cap bounds growth;
  it cannot express purpose. So **dispatch a recompute with a target**
  — a word count that leaves room for the landings already queued into
  that row — and **verify label preservation by a scripted set-diff, not
  by eye** (the coordinator's own recompute dropped a label and only the
  script caught it). The recurring mechanism behind all five regressions
  is unchanged and now named in the row itself: the
  "Since Steps X–Y (direction Z), W changed" construction, appended
  rather than folded into current state.

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

- **F26 — a residual can be *correct* and still be the wrong target; check what
  the consumer actually consumes before spending a direction on it.** Phase 39
  ran five consecutive directions (GCHEAP → GPRICE → GBLAW → GXESC → GHWIT) at
  (GR-104)(i), the (b′) price form. Every one was sound; the last refuted the
  target outright. Then GMINM read the *consumer* and found (b′) has **three
  pairwise-inequivalent readings** — `∀M`, `min_M` of the difference, and the
  ledger's own **difference of minima** — and the consumers run on the third.
  The refuted statement was never consumed. **No gate can catch this**: every
  figure was right, every landing verified, and the defect lived in the choice
  of target. Two structural causes, both fixable and both fixed at the
  2026-08-26 landing: the phase note's candidate list was ordered by *the
  previous direction's successor order*, which mechanically chases residuals;
  and the option board ranks **cheapest-decisive**, a property of the direction
  rather than its distance to the target. **The rule:** before dispatching at a
  residual, open its consumer and confirm the exact statement it takes — the
  same *slot-trace* discipline the playbook already mandates for build
  hand-offs, applied to research targets. A residual-of-a-residual that "does
  not touch a named gap" is a documented smell; this arc had that sentence
  written on its own board and ran at the target anyway.

- **F27 — one draw is a lower bound, not a measurement, whenever the statistic
  is semicontinuous.** BATTAIN's first sweep reported three rank shortfalls
  from a **single seed each**; rank is lower semicontinuous, so a one-seed
  shortfall establishes nothing — all three attained on another draw. The
  dispatch caught it itself and said so. This is the **second** instance of the
  shape in this phase (C3's `0/179` was the first, in mirror image), which is
  what makes it promotable rather than an anecdote. **The rule:** any claim of
  the form *"this shape fails to reach X"* needs multiple independent draws
  before it is a measurement at all, and the return must say how many; the
  *positive* direction needs only one, because an exhibited certificate is a
  proof. State the asymmetry explicitly — BATTAIN's 774/774 are proofs, its
  shortfall reports would have been guesses.
| 2026-08-28 | Phase39 57th direction BSHARP (`20082de1`; this commit repairs it) | opus (coordinator) | **F12 again, at the ORIGINATING sites: the correction reached the new section and the gap-map row, not the paragraphs that STATE the refuted claim** | BSHARP refuted (BE-38)(iii)'s *"`0` wherever two `u–v` paths leave `u` by different edges"* and recorded it thoroughly — in its own (BE-45)(iii) and in the `(K-bare)` row. But `git show --unified=0` showed it touched **only** line 267 and its own appended section: (BE-38)(iii)'s summary and (BE-42)(iii)'s mechanism sentence both still asserted the refuted clause, unmarked — the two sites it is **cited from**, and (BE-42)(iii) had inherited it once already. **The catch was the hunk list, not a grep**: `--unified=0` answers *did the correction reach the originating prose?* in one call. |
