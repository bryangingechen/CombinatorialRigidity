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
