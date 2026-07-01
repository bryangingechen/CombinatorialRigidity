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
grandfathered **rows 1–189**, the **Phase 23a–23f rows 190–630** (with their
session-close config notes + *Findings*, incl. the **23f rows 515–630** + the
**23f close-out**), and the **closed-phase *Findings*** (Phase 22h–22l +
post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23g**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). Open sub-phase = **23g** (`notes/Phase23g.md`; being opened
  this session — ENTRY chain extraction + CHAIN-5 reshape). Closed
  sub-phases (22k–23f) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23g.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23g.md` *Hand-off* (the active sub-phase)
  + the recon `notes/Phase23-design.md` §C.2/§C.5 (the CHAIN-5 reshape + the ENTRY
  `exists_chain_data_of_noRigid` extractor) and the frozen CHAIN↔ENTRY contract
  §C.0–C.6; the general-`d` reuse map is §1.33(C) of
  `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–514) now live in the archive (frozen, not gated).
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
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): availability = **all four rungs** (haiku / sonnet / opus /
  fable) probed reachable 2026-07-01, no substitution; **addenda versions in
  effect: `haiku-a1` / `sonnet-a1`**; step-4 mechanical fixups (wrong branch /
  author / trailer) **pre-authorized**; 10-run check-in cap **kept** for this
  map-v2 trial session.
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
Rows 1–630 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d;
502–514 = Phase 23e; 515–630 = Phase 23f). This live table holds only the **active sub-phase
(23g)** rows.

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 631 | 23g OPEN — `notes/Phase23g.md` + sub-phase-open sync (`60f5ddd5`) | 3/1/1 | opus | normal | clean | —✓——✓✓ | 137k tok / 36 tools / 4.6 min | Phase-open (fable-mapped by commit type; OPUS-ONLY→opus). Clean docs-only sub-phase open: `Phase23g.md` Layer plan faithful to §C.0–C.6 + the §C.4 record↔tuple map; umbrella Phase-23 row correctly stayed ◐ (not ✓); public surfaces left at arc level (correct for sub-phase open). Coord verified the hand-off's first commit (§C.4 `d=3` `ChainData`-ctor adapter) against source: record has `d_eq : d = n` (`Operations.lean:1314`, d=3⟹n=3) + the `d_eq_kAdd` bridge — grounded, not a hallucinated field. No gate bits (no `.lean`/blueprint pointer touched). |
| 632 | 23g §C.4 `d=3` `ChainData`-ctor adapter `chainData_of_exists_chain_data` (`9b65f960`) | 1/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 170k tok / 130 tools / 20.1 min | P=2 additive record ctor; sonnet-mapped→opus (OPUS-ONLY). Clean, idiomatic 58-line `def`, warning-clean + axiom-clean. Cost on the higher side (20min/130 tools) for a P=2 leaf — fiddliness was the `deg_two` defeq-closure + deriving the extractor-missing `e_b≠e_c` via `IsLink.eq_and_eq_or_eq_and_eq`, NOT degradation (diff is tight). Coord shape-checked vs §C.4: `vtx/edge/link/deg_two/d_eq` all faithful (link flips `e_b` to chain orientation; deg_two i=1→`hclv.symm`, i=2→`hcla`); confirmed strictly leaf-most (additive on the still-8-tuple tree). |

| 633 | 23g CHAIN-5 reshape route-composition SPIKE (read-only; no commit) | 3/3/1 | opus | recon | clean | ✓✓✓—✓✓ | 149k tok / 59 tools / 16.9 min | Compiler-checked spike, CHAIN-5 reshape (§38 defeq zone). GREEN: router discharges reshaped `hdispatch` sorry-free; `hd2` derivable, `hn` a below-contract surrounding add; d=3 re-discharge sorry-free (C.4 + `splitOff_swap_ab`). Found a 4th trio decl. Key re-route: general-n producer can't build `cd` (landed extractor is length-3 only) → ENTRY must supply it; reshape carries the extractor green-modulo. Coord verified vs source (extractor 4-tuple at general n; producer inline `Arms.lean:912`). Tree reverted clean. |

| 634 | 23g CHAIN-5 reshape — discharge the Case-III dispatch at general `k` (`74bd9003`) | 2/3/2 | opus | resume | clean | ✓✓✓—✓✓ | 275k tok / 99 tools / 29.6 min (cumulative resume) | Resume (SendMessage-continued, context intact) of the spike agent; reused its sorry-free router-discharge + d=3 re-discharge. Went STRONGER than scoped: DISCHARGED the dispatch via the router (not merely carried `hdispatch`), so 23f's router is now LIVE; only `hextract` (§C.2 ENTRY interface) stays green-modulo. Verified: full build warning-clean + lint + sorry-grep; shape faithful to §C.3 (`hn` below-contract add); `hextract` satisfiable at the d=3 consumer (`chainData_extract_d3`). Cost a large outlier but cumulative-resume + tight diff — not degraded. |

| 635 | 23g ENTRY satisfiability design-pass — OD-1 settled, E1–E5 ladder pinned (`ab26fa1c`) | 3/3/1 | fable | normal | clean | —✓——✓✓ | 222k tok / 65 tools / 20.1 min | First fable dispatch since the 22h rows (availability restored; map-v2 fable cell). Verdict OVERTURNED the contract's stated OD-1 default (chain-only) via a source-grounded short-cycle refutation; OD-2/3 settled from the tree. Coord verified the pivotal grounding (`splitOff_isMinimalKDof` general `{n}`, `Reduction.lean:161`; KT 6.13's own cycle case split makes the refutation KT-internal). Raised S to 1 for the whole ENTRY ladder (exact signatures). High-yield, consistent with the 22h fable profile. |

| 636 | 23g E1 `CycleData` record + `vertexSet_ncard` (`7aac3c1e`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 251k tok / 62 tools / 22.6 min (cumulative incl. resume) | First below-opus build under map v2 (sonnet cell; `Induction/` outside the fragility zone; `sonnet-a1` addendum). Lean faithful to the §(4.107.D) pin (all 9 fields; the `Fin.mk`-vs-OfNat deviation honestly re-flagged + FRICTION recurrence bullet — no checklist rewrite). ONE procedural miss: ended its turn parked on a background `lake build` (§2 neither-return) — coordinator SendMessage-resume finished gates+commit; candidate `sonnet-a2` clause. Coord re-ran build+lint clean; sorry-grep clean. |

| 637 | 23g E4 `hextract`/`hcycle` binder reshape, shape-2 disjunction (`ddc2db43`) | 1/2/2 | opus | normal | clean | ✓✓✓✓✓✓ | 182k tok / 42 tools / 14.2 min | First fragility-zone-modifier application under map v2 (max(S,P,B)=2 would map sonnet; the reshape touches `Arms`/`Realization`/`Theorem55` = the zone, and CHAIN-5's defeq trap bit in exactly this commit shape → opus). Clean first pass, zero friction. Faithful to the §(4.107.D) E4 pin at all sites incl. the 4th `hextract` site (the `k=2` wrapper) the pin's "three sites" undercounted — completeness win, consistent w/ the row-633 spike's find. Coord verified: gates re-run clean, sorry-grep clean, blueprint no-edit claim confirmed (`lem:case-III` statement unchanged). |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **23g session (2026-07-01, rows 631–634): the spike→resume pattern paid off on the CHAIN-5
  reshape.** A compiler-checked read-only spike (row 633) on the "wire the landed router into the
  reshaped `hdispatch` slot" route-composition — dispatched *before* the coupled can't-land-partially
  build — GREEN-lit it AND re-routed the hand-off: it found the router needs `hn`/`hd2` the C.3 slot
  doesn't carry (both below-contract-resolvable), and that the general-`n` producer can't build `cd`
  because the landed extractor is length-3 only (→ ENTRY is the real remaining crux). A
  SendMessage-**resume** of the same spike agent (row 634) then reused its sorry-free reshape to land
  the build, which went *stronger than scoped* — discharging the dispatch via the router (23f's router
  is now LIVE) rather than merely carrying `hdispatch`. Lessons: (i) the coordinator-acceptance
  "grep the brick's conclusion vs the consumer's slot" check surfaced the `hn`/`hd2` gap that
  justified the spike (a blind build would have hit it mid-reshape and had to revert wholesale);
  (ii) the spike→resume mechanic (protocol *Mode* now covers it) reuses the fragile defeq work instead
  of re-deriving; (iii) a large *cumulative-resume* cost figure (275k/99t/30min) is not a degradation
  signal when it's a resume total + the diff is tight. Un-named-dispatch return-mechanism clarified
  (command step-3 / rescue §2): un-named backgrounds but delivers LANDED/BLOCKED + cost via the
  completion notification.

- *(The 23f *Findings* (sessions #39–#51, rows 515–599: the geometry-arm /
  corner-saga / GO-cascade / (D-canonical) episodes — the deferred-GATE-through-a-GO-cascade trap, the
  recurring-wall heuristic, the recon's-escape-is-a-hypothesis pattern, faithfulness to KT's actual
  construction) are in the **23f close-out** in `notes/model-experiment-archive.md`. The durable
  cross-phase lessons live in the coordinate-phase command + DESIGN.md *Constructibility recon* /
  *Statement faithfulness*.)*
- *(The 23e *Findings* (sessions #36–#38: the spike-before-build /
  2-leaf-trigger pattern that broke the recurring "remaining = ASSEMBLY" mis-framing, the
  deferred-crux scrutiny, the architecture-shape satisfiability check, profile×rung) are in the
  **23e close-out** in `notes/model-experiment-archive.md`. The durable cross-phase lessons live in
  the coordinate-phase command + DESIGN.md *Constructibility recon*.)*
