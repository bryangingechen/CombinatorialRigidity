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
- **Standing rung override — Phase 23: OPUS-ONLY** (user-set, scoped to the
  whole phase: Case III general `d` is the conjecture's crux and sits in the
  §38 defeq-fragility zone where sonnet-and-below have repeatedly failed).
  S/P/B is still **rated and logged** per dispatch (experiment data), but the
  rung is **opus regardless of the map**; probes off; boundary pairs run
  opus-vs-opus or are skipped. Re-confirm (or lift) at session start.
- **Per-session run modifications** (re-confirm at session start, expires
  session-end): the **Standard triple** — OPUS-ONLY kept, 10-run check-in cap
  **lifted** (loop runs to phase close or a surfaced concern), step-4 mechanical
  fixups (wrong branch / author / trailer) **pre-authorized**. **Re-confirmed
  2026-07-01** (23g-open session; user-selected). Availability under
  OPUS-ONLY: only **opus** is probed (the coordinator runs on it, reachable via the
  Agent `model` param), verified reachable this session, no substitution; a fresh
  coordinator reverting to the S/P/B map would re-probe the other rungs. **The
  override expires session-end — a fresh coordinator re-runs the session-start
  availability check + re-confirms the triple.**
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

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

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
