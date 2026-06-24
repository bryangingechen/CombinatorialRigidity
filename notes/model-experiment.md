# Model-tier experiment — repo-local log

**Status:** running. (This line arms the coordinator hook —
`.claude/commands/coordinate-phase.md`'s model-tier step is
conditional on it.)

**Protocol:** [`notes/model-experiment-protocol.md`](model-experiment-protocol.md)
— the portable, repo-agnostic half (axes, assignment map, rubric, log
schema), byte-identical across participating repos. This file carries only
repo-local state: config, the dispatch log, and *Findings*.

**Cross-repo protocol-sync** (pending amendments + last-sync date) lives in
[`notes/model-experiment-sync.md`](model-experiment-sync.md) — one pointer
line per amendment, *not* a copy of the amendment text (that copy is what
ballooned this header for a month; the text's canonical home is the protocol
file).

**Archive:** [`notes/model-experiment-archive.md`](model-experiment-archive.md)
(search-target, not read on load) holds the cold half of the log — the
grandfathered **rows 1–189**, the **Phase 23a + 23b rows 190–372** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23c, 373–**), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). 22k/22l + the post-22l perf round closed 2026-06-16;
  23a/CARRIER Lean closed 2026-06-16 (row 190); 23b/CHAIN closed 2026-06-21
  (CHAIN bricks landed, the `hρGv`-seam characterized as a hard core); the open
  sub-phase is **23c** (`notes/Phase23c.md` — the redundancy-carry
  re-architecture decision + chain-dispatch completion). Continues into successor
  phases until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23c.md` *Hand-off* + the recon
  `notes/Phase23-design.md`; the general-`d` reuse map is §1.33(C) of
  `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–372) now live in the archive (frozen, not gated).
- **Standing rung override — Phase 23: OPUS-ONLY** (user-set, scoped to the
  whole phase: Case III general `d` is the conjecture's crux and sits in the
  §38 defeq-fragility zone where sonnet-and-below have repeatedly failed).
  S/P/B is still **rated and logged** per dispatch (experiment data), but the
  rung is **opus regardless of the map**; probes off; boundary pairs run
  opus-vs-opus or are skipped. Re-confirm (or lift) at session start.
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): the **same triple** — OPUS-ONLY kept, 10-run check-in cap
  **lifted** (loop runs to phase close or a surfaced concern), step-4 mechanical
  fixups (wrong branch / author / trailer, incl. the `Claude-Session` trailer)
  **pre-authorized** — plus the **same availability**: opus confirmed (the
  coordinator runs on it, reachable via the Agent `model` param); other rungs
  not probed under OPUS-ONLY, so a fresh coordinator reverting to the S/P/B map
  would re-probe. Set/re-confirmed sessions #6–#27 (latest: **#27**, 2026-06-23,
  fresh `/coordinate-phase`; user re-confirmed the triple at session start; opus
  reachable via the Agent `model` param, no substitution needed). **The
  override expires session-end — a fresh coordinator re-runs the
  session-start availability check + re-confirms the triple.** (A) is OPEN; the
  `±r`-row seam is RESOLVED end-to-end; `chainData_dispatch` is DECOMPOSED (5
  leaves) with the `Relabel/` split + LEAF-1/2 + the option-(a) contract field
  `d_eq : d = n` + the `cd.d=k+1` bridge LANDED; next = the rest of LEAF-3 — see
  `notes/Phase23c.md` *Hand-off* / *Orientation*.
- **Session #25 close (2026-06-22; rows 392–401, all opus / OPUS-ONLY, gate-verified; user stopped the
  loop after the corner-data assembly + a handoff-housekeeping pass).** **The `±r`-row seam — the
  conjecture-crux remnant blocking 23c across 4 prior arm attempts + 2 recons — is RESOLVED + build-proven
  end-to-end** (option (A) escapes the member-mapping wall *at the arm*, `hρe₀` only, no `hρGv`). Landed: the
  off-slot GROUP leaf (392, kept for the bottom family), the reproduced-slot leaf (394, later DELETED as
  mis-targeted), the corrected `±r` sourcing (399), the arm spine (400, over-shrunk → kept as cert→tail
  spine), the corner-data assembly integration (401). The resolution came from a **diverse-lens recon pair**
  (397/398: constructive NEEDS-REVIEW vs adversarial-refute LIKELY-SOUND; the refute member's two-rows
  distinction adjudicated, coordinator source-confirmed) — the graph-endpoints-vs-overridden-support
  decoupling. **Durable lessons** (this session's instruction edits): the satisfiability-check on
  deferred-hypothesis leaves (a LANDED+axiom-clean leaf can be mis-targeted), the un-named-dispatch default
  (a `name` routes to the async mailbox), and the diverse-lens recon pair for a recurring-mis-pin design
  seam → *Findings* + the 2026-06-22 sync pointers. OPUS-ONLY/cap/fixups expire session-end.
- **Session #26 close (2026-06-23; rows 402–412, all opus / OPUS-ONLY, gate-verified; user stopped the loop
  after the LEAF-3 arithmetic bridge + a handoff-readiness pass).** Decomposed + began CHAIN-2c-iii
  `chainData_dispatch`: the `Relabel/` 5-file split (402), the easy combinatorial accessors (403), a
  coordinator-escalated **decomposition design-pass** into 5 ranked leaves naming LEAF-4 the hard core (404,
  per a user directive after 2 scope-to-fit shrinks), LEAF-2 (405) + LEAF-1 (406), then LEAF-3 BLOCKED (407)
  on a **frozen-contract gap** — the discriminator's `Fin(k+1)` panels vs the `Fin cd.d` candidates need
  `d=k+1`, which the frozen `ChainData` contract left unencoded. A design-pass (408) + a **diverse-lens recon
  pair** (409/410, CONVERGED) + coordinator KT-PDF-verification confirmed `d=k+1` is structural (KT Prop 1.1 +
  Lemma 4.6); user adjudicated → option (a), the `d_eq : d = n` record field (411) + its `cd.d=k+1` bridge
  (412). **Durable lessons** (this session's instruction edits): a frozen contract must ENCODE the invariants
  relating its parameters (a known identity left as a docstring aside surfaces at the first consumer) +
  decompose a multi-commit chunk EARLY (the 2nd shrink) naming the hard core, + the `| tail` exit-code mask on
  `check-log-rows.py` → DESIGN.md *Frozen contracts …* + the `coordinate-phase` step-1 trigger / design-pass
  clause (iii) / step-2 gate note + *Findings*. OPUS-ONLY/cap/fixups expire session-end.
- **Expired overrides (audit trail in git + *Findings*).** The
  2026-06-{10,12,13,16} session-local rung / availability overrides all
  expired by their own terms; a fresh coordinator reverts to the S/P/B → map
  (substituting opus when fable is unavailable). Grounds: *Findings* (the
  §38-trap / KT-4.2-fiber sonnet-failure clusters).
- **Boundary-pair worktree (repo-local standing constraint).** Git worktrees
  *outside* the project dir fail under the sandbox — create them *inside*
  (e.g. `.bp-<slice>`, hidden via a `.git/info/exclude` line) or use the Agent
  tool's `isolation: "worktree"`. (`~/.cache` write was granted 2026-06-13 so a
  duplicate can run `lake exe cache get`; verify per session — the protocol's
  `.lake`-seeding default works regardless.)

## Log

Schema per the protocol. Rubric vector order: gates / scope / Lean
quality / blueprint sync / notes discipline / commit message
(✓ = pass, ✗ = fail, — = not applicable, e.g. doc-only commits).
Rows 1–372 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 373 | (A)-feasibility recon — (A) escapes the wall but is a rank-cert re-arch, NOT engine-feedable; §(o‴)(I.8.21), 50fb322 | 3/2/1 | opus | normal | clean | ✓✓——✓✓ | 191642 tok / 44 tools / ~7.4 min | (A)-feasibility recon (S3 design-settle→fable→opus, OPUS-ONLY); dispatched FRESH (independent of rows 370–372). Both clauses honored; coordinator spot-checked the two load-bearing source facts (ρ₀=∑lamAB•rab, Candidate.lean:432; the single hρGv use, :1606–1611) — both confirmed. Flag-don't-force GO/NO-GO: (A) named NEITHER buildable (hardest leaf = basis-free block-rank-additivity, genuinely-new + cost-unknown, STOP-and-escalate branch) NOR dead (escapes the wall via KT's Mᵢ-block/±r ℝ^D-equality). No manufactured leaf. → Findings 2026-06-21. |
| 374 | (2b)(β) Mᵢ-corner pin recon — (2b)(β) MIS-TARGETED, re-point to (2b)(γ); §(o‴)(I.8.22), 94710ee | 3/2/1 | opus | normal | clean | ✓✓——✓✓ | 169427 tok / 42 tools / ~6.5 min | (2b)(β) Mᵢ-corner pin recon (S3 design-settle→fable→opus, OPUS-ONLY); dispatched FRESH. HIGH-VALUE re-route caught BEFORE a build: OVERTURNED §I.8.21's premise — the landed rank-cert ALREADY does KT's Mᵢ+base decomposition inline, so (2b)(β) is mis-targeted and the de-risk leaf (2b)(α) CONSUMES the dead inclusion, not the (A) consumer. Coordinator verified both source claims. Flag-don't-force: hard leaf re-id'd (2b)(β)→(2b)(γ); §I.8.21's "telescope re-statement" guess REFUTED (different carrier). No manufactured sig. → Findings 2026-06-21. |
| 375 | (2b)(α) block-rank-additivity de-risk spike — POSITIVE, no §38 friction; cdf6016 (chronologically PRECEDED row 374) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 143328 tok / 56 tools / ~11.5 min | (2b)(α) de-risk spike (P3→opus, OPUS-ONLY); landed the abstract block-rank-additivity lemma + its ScrewSpace-carrier instantiation, both axiom-clean + warning-clean, no §38 friction (carrier never unfolded). De-risk POSITIVE as posed. NB: a follow-up recon (row 374, §I.8.22) found this leaf is NOT (A)'s binding constraint (the cert already does Mᵢ-block inline) — a pin-scoping issue, NOT an agent fault; the lemma is correct + may serve later. Logged LATE (coordinator omission; this dispatch ran before row 374). → Findings 2026-06-21. |
| 376 | (2b)(γ) ±r ℝ^D-identity de-risk spike — POSITIVE, already BUILT (interior_group_acolumn_eq_neg_baseRedundancy); §(o‴)(I.8.23), 22c4628 | 3/3/1 | opus | normal | clean | ✓✓——✓✓ | 211983 tok / 57 tools / ~12 min | (2b)(γ) de-risk spike (S3→fable→opus, OPUS-ONLY). Make-or-break POSITIVE: the degree-2 column-vanishing localizes cleanly into a Module.Dual ℝ (ScrewSpace k) ±r equality (hingeRow_comp_single_tail/_off, no §38 friction). KEY: the (6.66) ±r identity is ALREADY BUILT (interior_group_acolumn_eq_neg_baseRedundancy, 23b LEAF 1–4), coordinator axiom-checked clean — docs-only, no new leaf (a wrapper would be vacuous, clause-ii forbidden). §I.8.22's "(2b)(γ) is the genuinely-new hard leaf" superseded — delivered in 23b. Both (A) de-risks now POSITIVE. → Findings 2026-06-21. |
| 377 | cert-re-shape design-pass — §I.8.22-vs-§I.8.23 tension RESOLVES FAVORABLY ((A) escapes the wall); pin forked general-d cert + FIRST build; §(o‴)(I.8.24), 493063c | 3/2/1 | opus | normal | clean | ✓✓——✓✓ | 196637 tok / 39 tools / ~9.1 min | Cert-re-shape design-pass (S3 design-settle→fable→opus, OPUS-ONLY). RESOLVED the §I.8.22-vs-§I.8.23 tension FAVORABLY: the cert is selector-agnostic (one ends/q both sides; `hFvle` :1551 is the direct Gv≤G inclusion, NOT a relabel-image) — coordinator verified signature + hFvle. So the wall is ONLY the collapsed Unit-row's hρGv sourcing; re-sourcing via the member-free ±r value escapes it (§I.8.22's "dead inclusion" was an eval artifact). Pinned the FORKED general-d cert + FIRST build = case_III_rank_certification_chain (sub-risk: package W as a subspace). → Findings 2026-06-21. |
| 378 | W-packaging leaf `exists_le_finrank_eq_card_of_injective_map` (closes the §I.8.24(3) FIRST-build sub-risk); bca0f62 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 135222 tok / 35 tools / ~4.5 min | Routine build (dispatched for the FIRST build case_III_rank_certification_chain; S2/P2 → map=sonnet, ran opus under OPUS-ONLY). Agent self-shrank CORRECTLY (scope-to-fit): landed the flagged §I.8.24(3) sub-risk leaf first — `exists_le_finrank_eq_card_of_injective_map` (W-packaging via LinearIndependent.map' on the injective dualMap) — de-risking the cert. Coordinator verified warning-clean build + axiom-clean; clean 3-line term proof. Next = the cert itself (only remaining genuinely-new content = the hLI discriminator-mod-W reduction). → Findings 2026-06-21. |
| 379 | case_III_rank_certification_chain — forked general-d cert (§I.8.24(1) FIRST build, NO hρGv); 604a2f4 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 166353 tok / 55 tools / ~12.1 min | Routine build (S2/P2 → map=sonnet, ran opus OPUS-ONLY). Landed the forked general-d cert in §I.8.24(1) block-rank shape: wires the de-risk leaf + count, NO hρGv — the wall is structurally GONE. Coordinator verified shape vs §I.8.24(1), warning-clean build, axiom-clean, old cert UNTOUCHED (d=3 fork zero-regression). CRUX-DEFERRAL: the cert TAKES hLI/hWS/hg as HYPOTHESES, deferring the genuinely-new hLI (Mᵢ-corner LI-mod-W via discriminator@fixed-ρ₀ + ±r value) to the ARM. Rate the NEXT dispatch by that deferred crux (P3), not this plumbing. → Findings 2026-06-21. |
| 380 | shared W6a-W6f tail factored into case_III_realization_of_rank (§I.8.24(3) REUSE brick); 08d3d57 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 171292 tok / 59 tools / ~9.9 min | Routine build (dispatched for case_III_arm_realization_chain, rated by the deferred hLI crux P3). Agent self-shrank AGAIN (2nd consecutive): instead of the hLI crux, factored the shared W6a-W6f tail into case_III_realization_of_rank (§I.8.24(3) reuse brick) — faithful refactor, d=3 engine delegates, zero-regression. Coordinator verified warning-clean build + axiom-clean. Legit de-risk BUT the hLI crux is now TWICE-deferred — flag the NEXT dispatch to tackle hLI directly (or as a standalone lemma), not shrink a 3rd time. → Findings 2026-06-21. |
| 381 | linearIndependent_mkQ_sumElim_unit_of_notMem_span — chain arm hLI abstract core (mirror, §I.8.24(3)); 0067269 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 165554 tok / 56 tools / ~9.2 min | Routine build (for case_III_arm_realization_chain, P3 by hLI crux). 3rd consecutive self-shrink — landed hLI's abstract append-one LI-mod-W criterion (reusable mirror); concrete (a)+(b) arm wiring still deferred. Per the session-#19 lesson (3 slices now defer the crux), coordinator ran the convergence recon: read the d=3 dispatch — the arm RECEIVES (b)'s non-annihilation `hgate` as a HYPOTHESIS (discriminator supplies it via the dispatch's fin_cases u; u↔i match is 2c-iii's job, NOT the arm). Convergence CONFIRMED → arm buildable, next = the arm build. → Findings 2026-06-21. |
| 382 | exists_le_finrank_span_rigidityRows_eq_card_of_injective_map — hWS/hWcard carrier packaging (§I.8.24(3)); ce45762 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 143192 tok / 37 tools / ~7.9 min | 4th consecutive self-shrink — landed the hWS/hWcard carrier-packaging leaf (a thin exact-wrapper of the landed mirror on the ScrewSpace-dual carrier), the §I.8.24(3) last not-yet-in-tree infra piece. ALL arm corner-data infra is now in tree; the concrete (a)+(b)+g-transport assembly is the only thing left. Coordinator call: infra is now EXHAUSTED, so the next routine build can't peel another infra leaf — it must engage the arm body (full assembly, or factor the (b) crux). Dispatching the arm build once more; coordinator-decompose only if it still dodges. → Findings 2026-06-21. |
| 383 | linearIndependent_mkQ_of_comp + linearIndependent_mkQ_panelRow_of_edge — hLI corner obligation (a) (§I.8.24(3)); fe35f95 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 241700 tok / 107 tools / ~16.7 min | 5th self-shrink, but ENGAGED the arm body — landed the hLI (a) half as 2 clean leaves. Cost OUTLIER (107 tools/16.7 min, ~2x prior; diff only 135 LoC) = tried the arm, hit the (b)+assembly monolith, retreated — a difficulty signal, not bloat. 5 builds couldn't land the arm atomically. Coordinator ESCALATING per the repeated-non-fit mandate → a decomposition design-pass to pin (b)'s exact signature + the assembly so a build can't extract-and-defer a 6th time. → Findings 2026-06-21. |
| 384 | chain-arm leaf decomposition design-pass — (b) crux isolated (§I.8.24(4)); a0b5f29 | 3/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 179876 tok / 44 tools / ~6.8 min | Coordinator-ESCALATED decomposition design-pass after 5 build self-shrinks (design-settle → fable, ran opus OPUS-ONLY). Broke the atomic arm into named sub-leaves: isolated the (b) crux as `notMem_span_mkQ_pmR_row_of_gate` (KT (6.65); pinned signature, hyps satisfiable, NO smuggled fixed-member). Clause-(ii) honesty held — flagged (α) candidate column-transport + (β) bottom family as not-yet-isolated arm steps (member-MOVING buildable, neither a wall), NOT forced. Coordinator verified the (b) signature + reasoning vs landed source; re-pointed the hand-off to (b). → Findings 2026-06-21. |
| 385 | notMem_span_mkQ_pmR_row_of_gate — the (b) crux (§I.8.24(4.1)); ac4d5ee | 1/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 169772 tok / 63 tools / ~12.8 min | The decomposition WORKED — with (b) isolated as a pinned single lemma, the build had an un-shrinkable target and landed it (the FIRST non-shrink in 6 dispatches). Matched the design-doc signature verbatim, no renegotiation. Proof = the single-vᵢ column read-off contradiction, all ingredients in tree (no new math). Coordinator verified vs §I.8.24(4.1): non-vacuous (hgate genuinely used as the contradiction), warning-clean build + axiom-clean. Confirms the escalation-to-decomposition was right after 5 self-shrinks. → Findings 2026-06-21. |
| 386 | funLeft_dualMap_comp_single — (α) column-naturality bridge (§I.8.24(4.5)(α)); c3a3ef5 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 182772 tok / 50 tools / ~8.7 min | 6th shrink but LEGIT — landed (α), the design-pass-flagged column-naturality bridge (the riskier base-vs-candidate seam). (α) is NOT a wall: factored cleanly as a general lemma `((funLeft σ).dualMap φ).comp (single w) = φ.comp (single (σ⁻¹ w))`. The decomposition keeps working — builds land the pinned sub-leaves one at a time. Coordinator verified warning-clean + axiom-clean. Only (β) [bottom family, the 2c-iii dispatch's job per the d=3 template] + the assembly remain; the arm now takes (β) as hypotheses like the M₃ arm takes w/hw/hwmem. → Findings 2026-06-21. |
| 387 | funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy — (α) candidate hrCol (§I.8.24(4.5)(α)); 6032852 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 207588 tok / 83 tools / ~16.2 min | 7th shrink but LEGIT — landed the (α) APPLICATION (candidate-side hrCol = −ρ₀); (α) now FULLY done. Cost outlier (83 tools/16.2 min) = tried the arm assembly, retreated (diff 53 LoC, exploration not bloat). ALL crux content ((b)/(α)) landed; only (β) [bottom family] + assembly remain. Coordinator confirmed via the engine signature (Arms.lean:310 takes w/hwcard/hw/hwmem as HYPOTHESES) that the arm TAKES (β) as hypotheses, the dispatch produces it — settling the (β) ambiguity that drove the shrinks. → Findings 2026-06-21. |
| 388 | linearIndependent_mkQ_corner_of_gate — hLI corner-assembly (§I.8.24(4.3)); f4889ab | 2/1/1 | opus | normal | clean | ✓✓✓—✓✓ | 181633 tok / 51 tools / ~8.6 min | 8th shrink — landed the hLI corner-assembly (3-line composition of the 3 hLI leaves → the cert's g-block shape). hLI is now a one-line arm application. Shrank DESPITE the (β)-settle (cited arm SIZE ~200 lines, NOT (β)) — but ~200 is the M₃ template, an overestimate (the chain arm delegates tail+cert+hLI). Decomposition converging: only g-production (±r row + transport) + W-wire + the application chain remain. Coordinator verified warning-clean + axiom-clean. Dispatching the arm once more; a 9th shrink would be to g-production, then a trivial arm. → Findings 2026-06-21. |
| 389 | §I.8.24(4.6) pre-arm-build corrections — Relabel.lean placement + caseIIICandidate bridge (docs); 84abe8e | 3/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 217626 tok / 55 tools / ~11.2 min | 9th "shrink" but a HIGH-VALUE pre-build VERIFICATION — the agent self-applied the research-shaped trigger and caught 2 errors a build would've implemented wrong: (1) arm goes in Relabel.lean not Arms.lean (import DAG Arms⊂Relabel — VERIFIED), (2) the cert is over caseIIICandidate with NO ofNormals bridge in tree (VERIFIED via grep), so the arm CONSTRUCTS its candidate + routes the ofNormals memberships — a real ~200-line body, NOT the "pure assembly" my (β)-settle claimed. Re-pointed to a scope-to-fit split (bridge leaves, then arm, all Relabel.lean). → Findings 2026-06-21. |
| 390 | ofNormals→caseIIICandidate row-routing bridge (§I.8.24(4.6)); 7f2bd28 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 232169 tok / 123 tools / ~17.7 min | 10th dispatch — landed the caseIIICandidate↔ofNormals row bridge (the missing seam row 389 found): a framework-general supportExtensor-eq⟹row-membership primitive + the caseIIICandidate instantiation routing ofNormals memberships into the candidate-stated cert. Cost OUTLIER (123 tools/17.7 min) but diff modest (~61 Lean LoC) = proving effort, not bloat. Coordinator verified warning-clean (2776 jobs) + axiom-clean. ALL arm leaves + the bridge now landed; the ~200-line arm body (construct caseIIICandidate + wire, Relabel.lean) is the last piece — nothing left to factor. → Findings 2026-06-21. |
| 391 | case_III_arm_realization_chain (full arm) — BLOCKED; no commit | 2/2/1 | opus | normal | BLOCKED | — (no commit) | 190224 tok / 29 tools / ~6.4 min | BLOCKED at the full arm with a coordinator-VERIFIED diagnosis — a HIGH-VALUE block, not a failure: the agent refused to force a ~200-line speculative build (unfrozen sig, no consumer to validate, a missing leaf) per de-risk-before-pin, with a precise diagnosis — the ±r-row hg GROUP membership is genuinely-new + NOT in tree (coordinator grep-confirmed). 3rd time the arm surfaced a missing leaf after "all leaves in tree" — the §I.8.24(4) arm estimate was optimistic, the substance of the user checkpoint. Salvaged: pinned the hg-GROUP leaf as next. → Findings 2026-06-21. |
| 392 | ±r-row candidate-span hg GROUP leaf (§I.8.24(4.6)); 44d7b73 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 196505 tok / 65 tools / ~14.4 min | Coordinator-mechanics confound: FIRST dispatch NAMED → async mailbox, idled w/o returning (rescue §2; named-agent cost unavailable, wasted); re-dispatched UN-NAMED → synchronous LANDED. Clean: the genuinely-new GROUP-form sum-assembly (map_sum over a per-summand brick) built; per-edge chain-correspondence relocated to a bundled htransport hyp the arm discharges from landed chainData_bottom_relabel machinery. No bloat. NEXT (arm) must be rated by the htransport discharge (deferred math), not plumbing. |
| 393 | arm-buildability recon — off-slot GROUP leaf mis-targeted, decompose reproduced-slot leaf (§I.8.24(4.7)); 2b22d59 | 3/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 214678 tok / 56 tools / ~10.6 min | Design-pass recon (S=3 design-settle, fable→opus sub, OPUS-ONLY). HIGH-VALUE: OVERTURNED row-392's mis-pin — the off-slot GROUP leaf (44d7b73; coordinator-verified "legitimate" but htransport-risk flagged + deferred to the arm) is mis-targeted for the arm's ±r hg. Source-grounded the unsatisfiability (±r-group→edge i→relabels to candidate fresh pair = reproduced slot e_r, not off-slot genuine) + re-routed via the reproduced-slot leaf (M₃ :2756 mechanism). Coordinator re-verified vs landed bodies (:971, :4140). Vindicates recon-early over a 4th arm build. |
| 394 | reproduced-slot ±r-row hg leaf (§I.8.24(4.7)); b675317 | 2/1/1 | opus | normal | clean | ✓✓✓—✓✓ | 161052 tok / 53 tools / ~10.1 min | Clean LANDED of the row-393 recon-pinned reproduced-slot leaf; the exact-signature + proof-shape pin made it near-mechanical (agent: zero build iterations). One faithful refinement: hlink surfaced as an explicit hyp (the pin's "endsσρ e_r records the fresh pair"). The agent's #print-axioms "unknown constant" via a scratch lake-env file = module-system import-visibility artifact (Relabel.lean not module/public); coordinator confirmed warning-clean build = authoritative no-sorry per CLAUDE.md. Validates recon-then-build: a tightly-pinned leaf builds clean. |
| 395 | case_III_arm_realization_chain (full arm) — BLOCKED; no commit | 2/2/1 | opus | normal | BLOCKED | — (no commit) | 179555 tok / 36 tools / ~6.1 min | 4th arm-related BLOCK, HIGH-VALUE verified diagnosis: agent refused to force the ~200-line arm, surfacing a genuine ±r-row-sourcing seam — the just-landed reproduced-slot hg leaf's hcollapse (full-row collapse of the FILTERED edge-i group) is unsatisfiable; the filtered group has column-only machinery (interior_group_acolumn), the only full-row relabel (T-2, ORPHANED) is over A-1's FULL combination. Confirmed vs source (T-2 :4693 full-sum, A-1 :444 full-comb). The 393 recon circled but didn't resolve it. NEXT: design-settle ±r sourcing. → Findings. |
| 396 | design-settle ±r-row sourcing — BLOCKED, diagnosis committed (§I.8.24(4.8)); 7273c0f | 3/3/1 | opus | normal | BLOCKED | ✓✓✓—✓✓ | 234318 tok / 65 tools / ~12.6 min | Design-settle recon (S=3, fable→opus sub). 2nd consecutive recon deepening the ±r-row seam: committed a verified diagnosis (docs) that NEITHER route closes both hg + hrCol — body-mismatch (discriminator reads hrCol at single(vtx i), :1809; landed hrCol leaf gives −ρ₀ at vtx(i-1); full-comb reads 0 at vtx i), and the arm bottoms out on an OPEN KT eq-(6.66) step hingeRow(vtx i)(vtx i-1)ρ₀ ∈ span candidate rows the leaves miss — flagged as the dead hρGv-spine's math. 4th overstatement of "arm=wiring". Coordinator confirmed discriminator body :1809. STOP→user adjudication. → Findings. |
| 397 | adversarial recon PAIR member A (constructive) — ±r seam | 3/3/1 | opus | recon | clean | — (read-only) | 215723 tok / 38 tools / ~6.9 min | User-requested extra-scrutiny pair (opus×opus, OPUS-ONLY; A=constructive lens). Returned NEEDS-BROADER-REVIEW: confirmed §4.8 (landed objects don't close hg+hrCol; reproduced-slot leaf b675317 → DELETE), proposed the genuine-e_b-row fix but flagged its membership as an OPEN DECISION (worried it's the dead-hρGv-spine math / lands on the fresh pair not vtx i) + a cert-graph G-vs-G−vᵢ concern. HIGH conf on the incompatibility, MEDIUM on the fix. Adjudicated by B + coordinator source-check → resolved. → Findings. |
| 398 | adversarial recon PAIR member B (adversarial-refute) — ±r seam | 3/3/1 | opus | recon | clean | — (read-only) | 236450 tok / 57 tools / ~12.1 min | Pair member B (refute lens). Returned LIKELY-SOUND — could not refute; adjudicated A's open decision by distinguishing two rows: the relabel-image fresh-pair row (reads 0 at vtx i, dead) vs the DIRECT genuine reproduced-slot e_b-row hingeRow(vtx i)(vtx i-1)ρ₀ (graph link → vtx-i column = hrCol; support-override → membership = hρe₀; the M₃ hvb_row pattern, NO hρGv). Coordinator confirmed at source (cert :1922 full-G/slots e_a,e_b; M₃ hvb_row :2866; reproduced override :971). Pair CONVERGED post-adjudication; seam resolved (build confirms next). → Findings. |
| 399 | corrected ±r-row sourcing — direct genuine reproduced-slot e_b-row (§I.8.24(4.9)); 695c61a | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 207592 tok / 70 tools / ~14.8 min | The make-or-break build PROVING the recon-pair-adjudicated seam resolution: the corrected ±r-row sourcing built clean (no BLOCK), confirming option (A) escapes the wall at the arm — the direct genuine reproduced-slot e_b-row (hρe₀ only, NO hρGv) via the graph-endpoints-vs-overridden-support decoupling. Two leaves (membership + hrCol). DELETED the mis-targeted reproduced-slot leaf (grep+build-confirmed consumed-nowhere; supersession-deletion check passed). The 4×-mis-pinned seam genuinely resolved; arm now wiring. Coordinator verified shape vs adjudicated route. → Findings. |
| 400 | chain arm case_III_arm_realization_chain — LANDED (over-shrunk); 7afca03 | 2/2/2 | opus | normal | clean | ✓✓✓—✓✓ | 195178 tok / 48 tools / ~9.4 min | Arm LANDED but OVER-SHRANK to a thin cert→tail spine — took the ENTIRE corner data (W,hWS,hg,hLI) as hypotheses, deferring the hg/hLI ASSEMBLY (the seam end-to-end test: does the corrected ±r leaf feed the cert's hg + the hrCol feed hLI?) into "the dispatch". hWS-defer is valid (needs the bottom family), but hg/hLI is separable (raw hρe₀/hgate as hyps) + the integration the seam's 4× history warrants checking. Self-shrink (cf. 383-388). Commit correct + axiom-clean — KEEP. Coordinator re-pointed hand-off to the assembly integration test before the dispatch. → Findings. |
| 401 | corner-data assembly producer case_III_arm_corner_assembly — the seam integration test (§I.8.24(4.9)); 4ef07cd | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 192790 tok / 75 tools / ~13.2 min | The seam-resolution END-TO-END INTEGRATION — LANDED clean, confirming the corrected ±r leaf feeds the cert's hg + the hrCol feeds hLI. CONSTRUCTS g/hg/hLI from the landed leaves (panels + the genuine reproduced-slot ±r row via hρe₀, NEVER hρGv; hLI via the corner assembly), taking only the dispatch's raw outputs (ρ₀/hgate/hρe₀/W) as hypotheses — proper layering, NOT an over-shrink (contrast 400). Option (A) escapes the wall, build-confirmed end-to-end. Flagged for the dispatch: thread concrete W=span(range(L∘f)) so hW is provable. → Findings. |
| 402 | `Relabel/` 5-file split (scope-to-fit from the named `chainData_dispatch`); 9961b19 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 168861 tok / 95 tools / ~32.6 min | Rated for the named CHAIN-2c-iii `chainData_dispatch` (2/2/1); agent scope-to-fit to the hand-off's flagged overdue `Relabel/` split prerequisite (dispatch is ~3–5 commits; split flagged "before/alongside") — a legit shrink-the-deliverable-not-completeness call. Mechanical semantics-preserving cut of the 5066-line monolith into 5 files. Coordinator verified: decl-name set preserved (95==95), importer build warning-clean, lint clean, no sorry, imports + 3 doc pointers repointed, pins unaffected (no rename). |
| 403 | CHAIN-2c-iii interior-split-tuple ChainData accessors (combinatorial half of `chainData_dispatch` inputs); bfcd891 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 161274 tok / 42 tools / ~22.5 min | 2nd consecutive scope-to-fit shrink away from `chainData_dispatch`'s hard core (402 split → 403 the easy combinatorial accessors hvVc/haVc/hbVc/hsplitG + v≠a/v≠b distinctnesses); analytic core (discriminator hgate/hρe₀, base block W/hWS/hW threading, routing) still untouched — the 3–5-commit-chunk deferral the user flagged (cf. the 378–388 self-shrink run). Coordinator pivoting to a decomposition recon per user directive. Commit clean: additive, coordinator-verified build/lint/sorry, decls idiomatic. |
| 404 | decomposition design-pass — `chainData_dispatch` → 5 ranked leaves, LEAF-4 = hard core (§I.8.24(4.10)); f2d024c | 3/2/1 | opus | normal | clean | ✓✓——✓✓ | 226644 tok / 46 tools / ~9.2 min | Coordinator-escalated per user directive after 2 scope-to-fit shrinks (402/403) away from the dispatch's hard core. Ranked 5 leaves easiest→hardest, NAMED LEAF-4 the hard core so a build can't peel-and-defer; re-pointed to LEAF-2 (concrete-W carrier, the genuinely-new small piece). Both design-pass clauses honored: self-caught a σ.symm column-index trap (4.8-class), coordinator source-verified it + the existential-W + assembly-slot + bridge-direction claims against landed bodies. → Findings 2026-06-23. |
| 405 | dispatch LEAF-2 — concrete-W carrier `span_relabelImage_le_and_finrank_and_acolumn_vanish` (§I.8.24(4.10)); 1ab7cac | 1/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 114740 tok / 37 tools / ~7.0 min | First leaf off the row-404 decomposition; tightly-pinned exact signature → built clean with NO shrink (contrast the 402/403 shrinks), 37 tools/~7min. Landed statement byte-identical to the pinned sig (shape check pass, incl. hvanish at σ.symm v — the bridge-forced direction). Coordinator-verified: build/lint warning-clean downstream, no sorry, axiom-clean per agent. Validates decompose-then-pin breaking the shrink run. → Findings 2026-06-23. |
| 406 | dispatch LEAF-1 — interior-candidate framework defs `candidateEnds`/`candidateSeed` (§I.8.24(4.10)); fab855b | 1/1/1 | opus | normal | clean | ✓✓✓—✓✓ | 163253 tok / 51 tools / ~10.1 min | Landed only the 2 framework defs + simp _apply lemmas; RE-SCOPED the graph/seed hyps (hends_ea/eb, hLn/hgab/hne_Gv, hVone/hVcard) out of LEAF-1 → tracked under LEAF-3/4 with source pointers. Sound refinement: those hyps depend on the discriminator n'/GP context or are dispatch-inline per the d=3 template, i.e. preceded their own deps in the decomposition's LEAF-1 bundling — NOT the deferral anti-pattern (hard core LEAF-4 untouched, now 2 commits out). Coordinator-verified: build/lint warning-clean, no sorry, deferred items tracked not stranded. |
| 407 | LEAF-3 (discriminator firing + candidate match) — BLOCKED; no commit | 2/2/1 | opus | normal | BLOCKED | — (no commit) | 164746 tok / 29 tools / ~4.1 min | High-value verified BLOCK: the decomposition's "panel u:Fin(k+1) ↔ candidate i:Fin cd.d match" latitude is a real gap — they align only if cd.d=k+1, which the FROZEN ChainData/C.3 contract asserts nowhere (d a free ℕ; design only flags d=3=k+1). 2nd gap: hgate/hρe₀ stated vs candidateSeed but produced vs base seed q₁ (wall-adjacent). Refused to guess a frozen-contract change. Coordinator confirmed BOTH discriminators return Fin(k+1). Next: design-pass to settle below-contract re-pin vs contract change. → Findings 2026-06-23. |
| 408 | design-pass: settle LEAF-3 discriminator-index gap → frozen-contract change needed (§I.8.24(4.11)); 2871679 | 3/2/1 | opus | normal | BLOCKED | ✓✓——✓✓ | 198578 tok / 50 tools / ~7.5 min | Verified the row-407 BLOCK vs KT §6.4.2 + landed source: d=k+1 is STRUCTURAL (d candidates = k+1 panels, same index; no separate selector; D=(d+1 choose 2)=screwDim k=(k+2 choose 2)), but the FROZEN ChainData/C.3 leaves cd.d free → contract change forced. Flag-don't-force honored: committed docs-only options (a: add d_eq=k+1, ~1 commit, rec; b: re-index over Fin cd.d, ~3-5, higher risk; c: ruled out), returned BLOCKED for user adjudication. Coordinator verified screwDim=C(k+2,2) + assembly cd.d-agnostic. → Findings 2026-06-23. |
| 409 | diverse-lens recon PAIR member A (constructive) — the LEAF-3 d=k+1 contract gap | 3/3/1 | opus | recon | clean | — (read-only) | 148660 tok / 37 tools / ~5.1 min | Constructive lens (read KT §4+§6.4.2). Verdict: d=k+1 STRUCTURAL + ENTRY-dischargeable, HIGH conf — KT-verified (Prop 1.1: D=C(d+1,2); Lemma 4.6: chain length=d; §6.4.2: d candidates over d panels, ±r shared, count=D). Full route closes under option (a); LEAF-1/2 landed. Rec (a). Flagged downstream-only: the ENTRY KT-4.6 extraction leaf + the eq-6.66 ±r-chain generalization. → Findings 2026-06-23. |
| 410 | diverse-lens recon PAIR member B (adversarial-refute) — the LEAF-3 d=k+1 contract gap | 3/3/1 | opus | recon | clean | — (read-only) | 122861 tok / 32 tools / ~5.2 min | Refute lens (read KT §4+§6.4.2). ALL 4 attacks COULD-NOT-REFUTE → SOUND. Lemma 4.6 pins chain length=ambient dim (truncates to exactly d, NOT a free graph path); D=(d+1 choose 2) is KT's; route hρGv-free. KEY: d_eq dischargeable BY CONSTRUCTION (ENTRY builds the chain to k+1; KT-4.6 truncation IS the constructor) → avoids the 392/394 trap. Refinement: d_eq on the ChainData RECORD, not a dispatch hyp. Watch: eq-6.66 ±r across all interiors. → Findings 2026-06-23. |
| 411 | option (a) contract field d_eq : d = n on the ChainData record (§I.8.24(4.11)); 8105ebc | 2/2/2 | opus | normal | clean | ✓✓✓—✓✓ | 123229 tok / 45 tools / ~31.9 min | The recon-resolved frozen-contract fix. Landed purely additive — NO ChainData value constructor exists yet (rated B=2 for the lockstep ripple, actual B=1; ENTRY/23d sets d_eq by construction), so the green build self-verifies nothing broke. Field on the RECORD (not a dispatch hyp), stated d=n (record-local; n=k+1 at use sites) per the recon refinement — shape check matches the pin. ~32min wall is upstream-rebuild-dominated (16-line diff), not bloat. Coordinator-verified build/lint warning-clean, no sorry; hand-off re-pointed to LEAF-3 proper. |
| 412 | LEAF-3 arithmetic bridge `Graph.ChainData.d_eq_kAdd` (cd.d=k+1 from d_eq+hn) (§I.8.24(4.11)); e92d589 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 262308 tok / 100 tools / ~20.4 min | Scope-to-fit to the small arithmetic prerequisite (coordinator-anticipated pre-dispatch): the cd.d=k+1 bridge from d_eq+hn (nlinarith after clearing the /2). The genuinely-hard rest of LEAF-3 (eq-6.66 hρe₀ ±r-annihilation + candidate selector) remains — flagged risk R2. Hit the namespace-trap (TACTICS-QUIRKS §56): standalone Realization build clean but importer Theorem55 broke (16 parse errors); fixed via _root_, caught only by the FULL-project build. 100 tools = friction-debug + nlinarith search, not bloat. Coordinator full-build/lint warning-clean, no sorry. |
| 413 | LEAF-3 panel→vertex selector `candidateVtx` + injectivity (CHAIN-2c-iii, eq. 6.67); 1cd7636 | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 198244 tok / 53 tools / ~10 min | Rated P=3 (the flagged eq-6.66 hρe₀ sits in "rest of LEAF-3 proper" scope); agent scope-to-fit to the `k`-free genuinely-new piece `candidateVtx`+injectivity (1st shrink of LEAF-3 proper; deferred discriminator-firing + eq-6.66 hρe₀). NOT a thin alias — the eq-6.67 panel→vertex map + a real `split_ifs`/`omega` injectivity proof, coordinator-verified. Below-top-rung gates re-run: sorry-grep clean, warning-clean build + lint. Healthy decomposition progress; a 2nd consecutive shrink away from discriminator-firing would trip decompose-early. |
| 414 | design-pass recon: matched-interior hρe₀/hgate sourcing → §I.8.24(4.12) + re-pointed hand-off; fa842aa | 3/2/1 | opus | normal | clean | ✓✓——✗✓ | 279221 tok / 74 tools / ~14.6 min | S=3 design-settle (opus, OPUS-ONLY), triggered by the 2nd consecutive build-shrink away from the discriminator-firing producer (recon-early). RESOLVED: hgate LANDED-direct; interior hρe₀ a genuinely-new LEAF-4 leaf, NO contract change. Core verdict coordinator-source-verified (Arms.lean:910–913 → only the base-split IH in scope, interior W6b unavailable). Bit5✗ (clause-i lapse): cited `redundancy_panel_carry` as LANDED — actually a DELETED orphan (rows 268/271, the §(o‴)-killed degree-2 carry); coordinator corrected + flagged a LEAF-4 route recon (e68b391). → Findings. |
| 415 | LEAF-3 composed Fin(k+1) panel selector `candidatePanel` (CHAIN-2c-iii); 64b5563 | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 171172 tok / 63 tools / ~8.5 min | 3rd consecutive scope-to-fit shrink to an index-plumbing primitive (candidateVtx → candidateVtx_succ_eq → candidatePanel); the LEAF-3 discriminator-firing producer still unbuilt. candidatePanel = the discriminator's cand/hcand input (thin composition of candidateVtx + Fin.cast d_eq_kAdd, legitimately named + injective). Infra now EXHAUSTED (no selector primitive left), so the next build MUST engage the producer body — dispatching once; a 4th unproductive shrink → escalate to a sharper pin. Gates re-run clean (build+lint+sorry-grep). → Findings. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

### Session #26 (rows 402–404) — a 3–5-commit chunk invites the hard part being deferred; decompose EARLY, on the 2nd shrink (user-originated)

The hand-off named a single ~3–5-commit deliverable (`chainData_dispatch`). Two consecutive opus
dispatches both scope-to-fit AWAY from its hard analytic core — first to the (legitimate, flagged)
`Relabel/` file split, then to the easy combinatorial `ChainData` accessors — each a defensible
"shrink the deliverable, not the completeness" call, yet together leaving the discriminator /
base-block / routing untouched. The user named the mechanism: **leaving a big unstructured chunk lets
agents continually defer the hard parts as "too big."** Durable lessons:

- **Trigger the decomposition design-pass EARLY — the 2nd consecutive shrink away from a multi-commit
  chunk's core is the floor, not the 4th–5th.** This is the same self-shrink dynamic as the 378–388
  run (8 shrinks before the rows-384/389 decomposition broke it); the cheaper move is to decompose as
  soon as the pattern shows, before the easy leaves are exhausted. The decompose-on-repeated-shrink
  rule already exists for *infra* peeling (rows 382–383); this extends it to a coarse hand-off chunk.
- **A decomposition must NAME the hard-core leaf explicitly + rank EASIEST→HARDEST with exact
  signatures**, so a subsequent build has an un-shrinkable target and cannot peel an easy leaf while
  deferring the hard one (the §(4.4)(β) composer → the named LEAF-4). Ranking without naming the core
  still lets the deferral continue.
- **The design-pass's two clauses caught a real trap at the top rung.** The verify-against-source
  mandate made the agent re-read the landed bridge `funLeft_dualMap_comp_single` and self-correct its
  own pin's column-index direction (`σ v` → `σ.symm v`, a 4.8-class error); the coordinator then
  source-verified the existential-`W` carrier, the assembly's explicit `W`/`hW` slots, and the bridge
  direction before trusting the pin. Single-pass design output is fallible even at opus; the grounding
  is what made it sound.
- **Recon-early caught a frozen-contract gap before three leaves were built on it; a diverse-lens pair +
  coordinator PDF-verification settled it (rows 407–410).** The LEAF-3 build refused to guess a frozen-contract
  change (the discriminator's `u : Fin(k+1)` ↔ chain candidate `i : Fin cd.d` match needs `d=k+1`, which the
  frozen `ChainData`/C.3 contract carries nowhere) → a design-pass flagged it + named options → a diverse-lens
  recon pair (constructive + adversarial-refute, opus×opus, read-only) CONVERGED: `d=k+1` is STRUCTURAL
  (KT 2011 Prop 1.1 `D=C(d+1,2)` + Lemma 4.6 "chain of length d"; the coordinator PDF-verified both verbatim).
  Durable points: (i) the satisfiability trap (rows 392/394) is AVOIDED here because `d_eq : cd.d=k+1` is
  *dischargeable by construction* — the ENTRY extractor BUILDS the chain to length `k+1` (KT-4.6's truncation IS
  the constructor), not a property proved after the fact; the refute member's "put it on the ChainData RECORD,
  not a free dispatch hypothesis" makes that manifest. (ii) A diverse-lens pair that CONVERGES (vs the ±r-seam
  pair that split on the label) plus an independent coordinator primary-source check is a strong trust signal
  for a phase-crux contract decision. (iii) Two downstream risks both members independently flagged: the ENTRY
  KT-4.6 chain-extraction leaf (genuinely-new, but constructive) and KT eq-6.66's `±r`-shared-across-all-interiors
  step (KT's most compressed: "easily show… cf. 6.44", no derivation) — both downstream of the contract decision.

### Session #25 (rows 392–396) — the chain-arm `±r`-row `hg` resolves into the open KT eq-(6.66) step (not wiring); two correct-but-mis-targeted leaves landed first

The arm's `±r`-row `hg` was framed as "wire a landed leaf"; two leaves (off-slot GROUP `44d7b73`,
reproduced-slot `b675317`) landed clean but were each found mis-targeted, and a design-settle (`7273c0f`)
established the arm bottoms out on the genuinely-new KT eq-(6.66) redundancy-membership with a body-mismatch
(the "arm = pure wiring" framing was overstated a 4th time). Durable lessons:

- **A conditional leaf is real progress only if its hypothesis is SATISFIABLE for the actual consumer — check
  before landing, not at the consumer's build.** Both `±r` leaves are true `(hyp) → goal` lemmas, but
  `htransport`/`hcollapse` are unsatisfiable for the arm's real `±r` row (relabel lands on the reproduced slot,
  not off-slot; the filtered group is column-only, no single-row collapse). Signature-match + gate-green +
  decl-existence ALL passed; only a satisfiability trace catches it — the "abstraction defers the crux"
  anti-pattern at the hypothesis level. → DESIGN.md *Constructibility recon …* (the satisfiability corollary).
- **Recon-then-build validated leaf SIGNATURES, not hypothesis satisfiability — so a second mis-targeted leaf
  landed after the first was caught.** The iter-2 recon caught the off-slot mis-target but re-pinned the
  reproduced-slot leaf with an unsatisfiable `hcollapse`; the coordinator verified the pinned signature + decls
  (matched) but not `hcollapse`'s satisfiability for the filtered group (and had even flagged the analogous
  iter-1 `htransport` risk, then deferred it). Fold the satisfiability trace into recon scrutiny.
- **Recon-early paid off (again): the design-settle, not a 5th build, surfaced the real obstacle** — neither
  `±r`-sourcing route closes both `hg` and `hrCol` (body-mismatch: the discriminator reads `single (vtx i)`, the
  landed `hrCol` gives `−ρ₀` at `vtx(i-1)`; the full combination reads `0` at `vtx i`). Triggering the
  design-settle instead of dispatching the arm build converted a likely 5th BLOCK into a precise decomposition +
  a user-surfaced decision on the open KT eq-(6.66) step.
- **A diverse-lens recon PAIR (constructive + adversarial-refute, opus×opus) resolved the 4×-mis-pinned ±r
  seam where single reads + coordinator scrutiny had failed.** The two members split (A: NEEDS-REVIEW, flagged
  the membership "open / dead-hρGv-spine math"; B: LIKELY-SOUND, could not refute) — and B's refutation lens
  *adjudicated A's open decision* by distinguishing two rows. The KT-math lesson (→ BlueprintExposition ledger):
  when an object must satisfy a column-value read AND a span-membership, check whether its two relevant
  structures are DECOUPLED — the reproduced slot's GRAPH endpoints `(vtx i, vtx i-1)` (give the `vtx i` column =
  `hrCol`) are decoupled from its OVERRIDDEN support panel (gives membership = `hρe₀` = `hg`), so the direct
  genuine `e_b`-row closes both where every "natural" transported/support-panel row (reads 0 at `vtx i`) cannot.
  The process lesson: a diverse-lens pair beats two identical reads; the adversarial member found the distinction
  the constructive member flagged as open. Coordinator confirmed at source (cert :1922 full-`G`/slots `e_a,e_b`;
  M₃ `hvb_row` :2866 hρe₀-only; reproduced override :971) before trusting it.
- **Process: named/async Agent dispatch routes to the mailbox and idles without a synchronous return** (rescue
  §2) — the iter-1 named agent emitted only `idle_notification`s (no `LANDED`/cost), forcing an un-named
  re-dispatch; the named-agent cost is unavailable/wasted. Dispatch un-named for a synchronous return.

### Session #23 (paused; rows 373–380) — the (A) re-architecture: a recon-chain to feasibility, then the cert compiles (the wall is gone)

The user opened 23c on the redundancy-carry fork and chose **(A)** (re-shape the rank-cert to KT's
`±r`/`Mᵢ`-block form, escaping the member-mapping wall). A recon/spike chain (§I.8.21–I.8.24) established (A)
feasible and the forked general-`d` cert `case_III_rank_certification_chain` LANDED compiling + axiom-clean
with **no `hρGv`** — the wall that blocked all of 23b is structurally gone (the `d=3` path byte-identical,
zero-regression). Durable lessons:

- **A POSITIVE de-risk of leaf X does NOT retire the phase's risk unless X is confirmed BINDING.** The (2b)(α)
  block-rank-additivity spike (row 375) landed clean + POSITIVE, but the follow-up (2b)(β) recon (row 374,
  §I.8.22) found the leaf is *not* on (A)'s critical path — the landed cert already does the `Mᵢ`-block
  decomposition inline, and the de-risk leaf *consumes* the dead relabel-image inclusion as its `hWS`/`hg`
  inputs. The real binding leaf was elsewhere ((2b)(γ), then found already-built in 23b). Verify which leaf is
  actually binding before reporting a de-risk as risk-retiring; the coordinator re-surfaced the corrected
  picture to the user mid-loop.
- **Recon-early + coordinator-verify-against-source converged a 4-shift architecture decision with ZERO wasted
  build commits.** Four design-passes (§I.8.21–I.8.24) each refined/overturned the prior pin
  (block-rank-additivity → not binding → (2b)(γ) → already-built → the cert is selector-agnostic, so the wall is
  only the collapsed-row `hρGv` sourcing). Every shift was caught in docs, before a build. The coordinator
  independently re-verified each pin's load-bearing source claims (the rank-cert `fam` assembly :1596–1599;
  `hFvle` :1551 the direct `Gv≤G` map; the `±r` identity conclusion `= −ρ₀`), which is what made trusting the
  convergence safe — a single-pass design pin in this zone was wrong ~half the time.
- **Crux-deferral across a re-architecture build-out — track the deferred crux; don't let it shrink
  indefinitely.** The cert (row 379, P2 plumbing) took `hLI` as a hypothesis; the next build (row 380)
  self-shrank again (the shared-tail refactor). Both shrinks were legitimate scope-to-fit, but the
  genuinely-new `hLI` `Mᵢ`-corner LI-mod-`W` crux is now twice-deferred — the coordinator flagged the next
  dispatch to tackle it directly (or as a standalone lemma), not shrink a 3rd time.
- **Process: piping `check-log-rows.py` through `tail` masks its exit code** (the pipeline returns `tail`'s 0),
  so a `… | tail && git commit` chain proceeds even on FAIL — an over-cap row 379 rode into a commit before
  being caught + amended. Gate by grepping the output for `^OK` (or check `${PIPESTATUS[0]}`), not the pipeline
  exit.

