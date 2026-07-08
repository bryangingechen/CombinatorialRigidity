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
grandfathered **rows 1–189**, the **Phase 23a–23h rows 190–670**, the
**post-Phase-23 cleanup-round rows 671–717**, the **Phase 24 rows
718–723**, and the **Phase 25 rows 724–739** (each with session-close
config notes + *Findings* close-outs), plus the **closed-phase
*Findings*** (Phase 22h–22l + post-22j
perf). This live file keeps only the config, the **active phase's** rows
(the **Phase-26-cleanup** program-closing round, active from 2026-07-07 —
the experiment was continued past the molecular program's close by user
decision), and active-phase *Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **COMPLETE. Phase 26 CLOSED
  2026-07-07** (Cor 5.7, all 5 `molecule-application.tex` nodes green in
  one session, rows 740–745), ending the 10-phase program (17–26). The
  **Phase-26-cleanup** program-closing round is now the active testbed —
  the experiment was **continued** past program-close by user decision
  (2026-07-07 session). Phase status lives in the ROADMAP table +
  `notes/Phase26-cleanup.md`, **not here**.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/MolecularConjecture.md` (the program map;
  Phase 26 planning) + `notes/Phase25.md` *Hand-off* (the Phase-25 close
  record; its design doc `notes/Phase25-design.md` keeps the §2.2/§2.6
  Phase-26 contract live). `notes/Phase23-design.md` is frozen as the
  §-cited archive.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed phases'
  rows (1–739) now live in the archive (frozen, not gated).
- **OPUS-ONLY lifted (2026-07-01, user-directed).** The Phase-23 standing
  override is retired: fable is back, and the protocol's **map v2**
  (the S=1/P=3 sonnet boundary cell + the fragility-zone modifier + the
  versioned rung addenda, all adopted 2026-07-01) replaces the blanket
  override as the fragile-zone control. S/P/B → map v2 governs from row 635.
  Trial discipline (user: "pay close attention to the results"): surface the
  first below-opus repaired / escalated / BLOCKED outcome under the new map
  to the user immediately, not just at the check-in cap.
- **Fragility-zone list (repo-local input to map v2's fragility-zone
  modifier):** `Molecular/AlgebraicInduction/` (esp. `CaseIII/` +
  `Theorem55.lean`), `Molecular/RigidityMatrix/`, and any
  ScrewSpace-carrier-touching edit — the §38 / heavy-`whnf` defeq-fragile
  zone where sonnet has wedged (archive rows 7, 157). **Producer builds**
  touching these → **opus minimum**; mechanical refactors / doc edits there
  stay mapped (archive row 166: a sonnet refactor in the same zone ran
  clean). The combinatorial side (`Molecular/Induction/`, incl.
  `ForestSurgery/`) is NOT in the zone.
- **Per-session run modifications (2026-07-07 program-closing
  cleanup-round session, user-confirmed at the session-start
  check-in):** **fable is unavailable** — fable-mapped commits
  (design-settle / phase-boundary / S=3) substitute **opus** (nearest
  available); haiku / sonnet / opus reachable. Run cap **lifted** (run
  to phase close or a genuine stop-trigger); mechanical fixups (rescue
  §1) **pre-authorized**. Experiment **continued** for the
  Phase-26-cleanup round (user decision at the phase boundary).
  **Addenda versions in effect: `haiku-a1` / `sonnet-a2`.** Expires at
  this session's close. *(The earlier 2026-07-07 session that ran
  Phase 26 open→close, rows 740–745, is closed.)*
- **Availability check is user-confirmed from 2026-07-02 on** (user-directed
  amendment to `.claude/commands/coordinate-phase.md`): no probe dispatches;
  the session-start check-in asks the user whether any rungs are missing, and
  that check-in **blocks** until answered (no timeout-default).
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
Rows 1–745 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–670 = Phases 23a–23h + the umbrella close; 671–717 = the
post-Phase-23 cleanup round; 718–723 = Phase 24; 724–739 = Phase 25;
740–745 = Phase 26, opened and closed 2026-07-07, ending the
molecular-conjecture program 17–26). This live table holds only the
**active phase's** rows (no successor — the program is complete).

| # | Task (short + sha) | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 746 | A2-w blueprint `\uses`-wiring `a528e227` | 2/1/1 | sonnet | normal | clean | ✓✓—✓✓✓ | 157k tok / 44 tools / 7.4 min | Mapped rung (max=2). Sonnet traced the real Lean chain (chainData_fire_discriminator → … → complementIso_gen) to place the edge rather than guessing; added `\uses` only (no removals/over-reach); gates attested from real output, sonnet-a2 foreground rule held. First dispatch died at launch on a transient API server error (0 work/0 cost, clean tree); relaunched — not an agent fault. |
| 747 | A3 `lem:case-II` liveness determination + docstring honesty fix `daaec9d4` | 2/2/1 | opus | recon | clean | ✓✓✓✓✓✓ | 164k tok / 36 tools / 24 min | Recon-shaped design-pass; rung opus by recon-stakes, not the 2/2/1→sonnet map. Verdict sound under coordinator scrutiny: independently confirmed the no-divergence crux (`lem:case-II-realization` omits `\uses{lem:case-II}`) + node-liveness (6 edges). Liveness lesson held — grep/`lean_references` decisive (no `_gen` sibling, unlike d=3). Agent ran gates via a background build + Monitor-wait → several intermediate idle notifications (coordinator briefly misread as a stranded neither-return); it recovered + committed correctly with foreground-attested gates. → Findings 2026-07-07. |
| 748 | B3 multi-label `\cref` "??" fix + `lint.sh` guard `3660f994` | 2/1/1 | sonnet | normal | clean | ✓✓—✓✓✓ | 157k tok / 88 tools / 10 min | Clean sonnet blueprint fix, mapped rung (max=2). Confirmed the plastex cleveref-shim root cause by rebuild rather than assuming the P23 claim; fixed 9 instances + added `lint.sh` check 6; correctly surfaced + tracked a distinct new bug (B4, numberless `\subsubsection` refs) as its own item rather than scope-creeping B3. sonnet-a2 foreground gates held; definitive LANDED (no interim-notification confusion this time). 88 tool uses reflects rebuild-verifying each instance, not a wedge. |
| 749 | B4 subsubsection-cref "??" reword (approach a) + `lint.sh` check 7 `f93a515f` | 2/1/1 | sonnet | normal | clean | ✓✓—✓✓✓ | 158k tok / 80 tools / 10 min | Clean sonnet blueprint reword, mapped rung (max=2), approach (a) as pinned (no `\subsection` promotion). Found all refs to the 2 numberless subsubsections across case-iii + genericity-and-count (not just the one file the checklist named); added a sound awk `lint.sh` check 7 (subsubsection-label guard, brace-depth for multi-line titles). Surfaced B5 (the LAST "??": a multi-line multi-label cref that check 6's single-line regex missed). sonnet-a2 gates held; definitive LANDED. Convergent — 1 "??" left corpus-wide. |
| 750 | B5 multi-line 3-label `\cref` "??" fix + check-6 multi-line-aware `8be3a2b7` | 2/1/1 | sonnet | normal | clean | ✓✓—✓✓✓ | 122k tok / 52 tools / 8 min | Clean sonnet blueprint fix, mapped rung (max=2). Closed the B-"??" family: last (10th) "??" fixed + check 6 hardened multi-line-aware (awk joins `%`-continuation lines) — the persistent-guard route the pin preferred, not the escape-hatch; agent sanity-tested by reintroducing the bug + confirming the guard fires. Coordinator ran the DECISIVE closure test independently: whole-corpus "??" grep = 0. sonnet-a2 gates held; definitive LANDED. Cheapest of the B-family (122k/52 tools). |
| 751 | D3 close ScrewSpaceCarrier-design.md `c699e767` (+note `93d88826`) | 1/1/1 | haiku | normal | clean | —✓——✓✓ | 62k tok / 13 tools / 1.4 min | First haiku dispatch, mapped (1/1/1). Work correct: doc closed (Status→DONE, Part-2 subsumed by Phase-23), archival §§ preserved. Minor haiku wobbles: split the single change into TWO commits (`c699e767` close + `93d88826` note-update), reported the follow-up sha as LANDED; condensed the Status paragraph beyond the literal "flip the line, don't compress" pin (no info loss — detail is in §5). Cheap+fast. haiku-a1 "do exactly the named edit" only loosely honored. |
| 752 | C1 top-~10 long-proof screen (no-op) `bc3c4471` | 2/1/1 | sonnet | normal | clean | —✓——✓✓ | 142k tok / 33 tools / 3.7 min | Clean sonnet no-op audit, mapped (2/1/1). Genuine, specific screen: ran the §C LoC ranking twice (whole `Molecular/` tree 41 files/53.8k lines, then Phase-24–26-scoped), read the top ~10 (46–94 lines) in full, walked the 5-question §C gate per candidate with concrete decl:line citations — not a fabricated no-op. Verdict matches the §C calibration (sibling long proofs resist a shared combinator). sonnet-a2 gates held; definitive LANDED. Doc-only, no follow-up. |
| 753 | D2a exposition-ledger accounting reconcile `261e61c7` | 2/1/1 | sonnet | normal | clean | —✓——✓✓ | 269k tok / 78 tools / 12.8 min | Clean sonnet reconcile, mapped (2/1/1); owner-re-scoped to reconcile-ONLY (no writing) — respected: only notes/*.md, no `.tex`. Flipped 9/13 stale `[pending]`→done (exposition had already landed via post-Phase-23 readability rewrites); header corrected to 4 pending/25 done. Coordinator source-verified the 2 checklist-named "missing" flips (Lemma 2.1/extensor.tex + forest-surgery/molecular-induction.tex): both genuinely carry detailed exposition, so the claim holds. 269k tok/78 tools = the 13-entry `.tex` verification-read cost, not bloat. |
| 754 | Round-close (post-Phase-26 cleanup) `adf3cfeb` | —/—/— (close) | opus | normal | clean | ✓✓——✓✓ | 98k tok / 38 tools / 8 min | Round-close, fable-mapped (phase/round-close cell) → opus (fable out this session). Clean: ROADMAP cleanup row → ✓ with A/B/C/D summary; note compressed 529→145; deferred follow-on family (A2-x/D1/D2b/retrospective) recorded; final gate green (2860 jobs) + both headline theorems axiom-clean via `#print axioms`. Project-org review caught + fixed a stale `MolecularConjecture.md` pointer (still called the sweep "open") the close would otherwise have left. Coordinator independently reconfirmed build green. Opus close needed no addendum; definitive LANDED. |

*(Phase-26-cleanup rows begin here — experiment reopened 2026-07-07 by user
decision. Rubric order: gates / scope / Lean / blueprint / notes / commit-msg.
B1 + A2-i predate the reopening and carry no rows.)*


## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **(2026-07-07, A3 / row 747) Background-build idle notifications ≠ a stranded
  neither-return.** A background subagent that runs its gates via a background
  build + a Monitor-wait emits an idle "completed" notification each time it
  pauses — these fire *before* the agent's definitive LANDED/BLOCKED, and the
  interim tree can look stranded (dirty, HEAD not advanced). The coordinator here
  read that interim state and began finalizing the agent's work (writing a commit
  message) before the agent self-completed and committed `daaec9d4` — a near
  double-commit. Lesson: on a mid-flight-looking notification, checking git state
  is fine, but **wait for the LANDED/BLOCKED-shaped final message before
  finalizing on the agent's behalf**. Seen at opus (no addendum): the fixed
  prompt's foreground-gate clause is not always honored even at the top-available
  rung — but the agent recovered without coordinator intervention.

### Phase-26-cleanup close-out (rows 746–754, 2026-07-07)

**9 dispatches, all clean — zero repairs / escalations / BLOCKED.**
- **sonnet on S=2 blueprint/doc tasks** (A2-w wiring; B3/B4/B5 the `\cref` "??"
  family; C1 long-proof screen; D2a ledger reconcile): **6/6 clean, mapped.** A
  clean positive data point for map v2 on hygiene/blueprint/doc work — no
  below-opus task needed escalation this round.
- **haiku on a tightly-pinned 1/1/1 doc-close** (D3): clean + cheap/fast (62k tok,
  1.4 min) but with minor process wobbles — split one logical change into two
  commits, reported the follow-up sha as LANDED, condensed a doc beyond the literal
  "flip the line, don't compress" pin (no info loss). The *work* was correct;
  `haiku-a1`'s "do exactly the named edit" was only loosely honored.
- **opus on a recon** (A3 liveness) **+ the round-close**: both clean, no addendum.

**Lessons:**
- (above) Background-build idle notifications ≠ a stranded neither-return (A3).
- **A "write the missing X" checklist item warrants a reconcile-FIRST check** (D2a).
  The D2 item named Lemma 2.1 + the forest-surgery family as "genuinely-missing"
  exposition, but a reconcile found *both already written* (via post-Phase-23
  readability rewrites) — the checklist's "missing" framing was a stale marker, the
  same class as this round's liveness lesson. Scoping the write before confirming
  the target is actually absent risks a duplicate; the owner's reconcile-only
  re-scope + the coordinator's source-verification of the two named flips caught it.
- The "??"-rendering sweep **converged in 3 distinct root causes** (B3 single-line
  multi-label / B4 numberless `\subsubsection` / B5 multi-line multi-label), each
  surfaced by the prior's whole-corpus grep; the decisive test (zero "??"
  corpus-wide) confirmed convergence, and `lint.sh` checks 6–7 guard recurrence.
