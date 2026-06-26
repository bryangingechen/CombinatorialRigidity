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
grandfathered **rows 1–189**, the **Phase 23a–23d rows 190–501** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23e**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). Open sub-phase = **23e** (`notes/Phase23e.md`). Closed
  sub-phases (22k–23d) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23e.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23e.md` *Hand-off* (the active sub-phase)
  + the recon `notes/Phase23-design.md` (§(4.48)–(4.52) = the live cert-route arc);
  the general-`d` reuse map is §1.33(C) of `notes/Phase22-realization-design.md`.
- **Attribution:** top-level `CLAUDE.md` *Working* → *Commit attribution*
  (exact author string + actual-model trailer).
- **Log-row length gate:** `notes/check-log-rows.py` enforces the protocol's
  ~600-char Notes cap. Run it before committing a log row (default mode checks
  only the rows this commit touched); it is wired into the coordinate-phase
  per-commit step. `--all` audits the whole (live) table; the closed sub-phases'
  rows (1–434) now live in the archive (frozen, not gated).
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
  would re-probe. Set/re-confirmed sessions #6–#38 (latest: **#38**, 2026-06-26, this
  `/coordinate-phase` loop — opus availability confirmed via the Agent `model` param,
  Standard triple re-confirmed by the user; #37 was the user-directed STRATEGIC session
  that closed the cert route, below). **The override expires session-end — a fresh
  coordinator re-runs the session-start availability check + re-confirms the triple.** **Session #37 made the phase's biggest adjudication + closed the cert
  route:** (1) the user chose to **pursue the genuinely-new certificate** (complete formalization
  of KT is the goal; fallback (C) / freeze-at-`d=3` declined; design §(4.48)); (2) the de-risking
  arc §(4.48)–(4.52) SETTLED the cert route to the **A3-transposed `fromBlocks A 0 C D`** shape,
  GO verdict (KT's union-dimension `Mᵢ`-invertibility is already landed general-`d`; remaining =
  ASSEMBLY, not new math). **The §(4.43) `chainData_dispatch` next-step is SUPERSEDED:** 23e
  re-scoped to the rank certificate; the dispatch + CHAIN-5 moved to **23f**. No open
  design/strategic decision is owed — the next dispatch is the **forked-cert build (item 3a)**, a
  BUILD. (Session #36's `hIH` C.3 adjudication still stands — it lands with 23f.) Phase status +
  next dispatch live in `notes/Phase23e.md` *Hand-off* + the ROADMAP cell, **not here**.
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
Rows 1–501 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 509 | item (3b′) — LEAF-RowOp-1/2: the two trivial row-op LA facts `rowOp_isUnit_det` + `rowOp_zeroes_upperRight` (`Mathlib/.../Matrix/Rank.lean`); axiom-clean (1d69932) | 1/1/1 | opus | normal | clean | ✓✓✓—✓✓ | 118k tok / 46 tools / 12.5 min | opus (OPUS-ONLY; map=haiku, 1/1/1). Clean trivial-LA build (det_fromBlocks_zero₂₁ + fromBlocks_multiply). Gates verified independently (forced Rank-module rebuild warning-clean, lint, no sorry). Agent caught + honestly disclosed a needed signature fix vs §4.53 (DecidableEq m₁/m₂ for the identity `One` instance). First leaf of route A — the cert-reshape route the §4.53 spike re-routed to after refuting the §4.52 "no new math" wall. |
| 508 | item (3b) hA-half — `corner_hA'_of_gate`, the `Mᵢ=[r(Lᵢ);ρ₀]` corner LI from the candidate-slot gate (`Concrete.lean`); axiom-clean (351fdec) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 113k tok / 37 tools / 9.5 min | opus (OPUS-ONLY; map=sonnet). Clean BUILD; agent self-shrank 3b to the hA-half (`corner_hA'_of_gate` re-created from the §4.52 scratch fact, 1 rw + 1 exact). Gates verified independently (forced Concrete rebuild warning-clean, lint, no sorry); sound + faithful. Per the 2-leaves-into-hard-core recon trigger (3a cert + this hA-fact both feed the unbuilt U/re/en/hblock matrix core), next = a compiler-checked spike on the rest-of-3b assembly, not another build. |
| 507 | item (3a) — forked A3-transposed Case-III rank cert `case_III_rank_certification_zero₁₂` + A3-transposed scaffolding (Rank.lean `fromBlocks A 0 C D` mirrors + Concrete.lean A5c-transposed core); axiom-clean (a3e4a55) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 160k tok / 58 tools / 15.3 min | opus (OPUS-ONLY; map=sonnet). Clean BUILD; gates verified independently — `touch` didn't re-emit (lake content-hashes), so forced a transient-edit rebuild of Candidate + LSP-checked Rank/Concrete, all warning-clean. Cert leaf dodges the 23d architecture-shape wall: `re` injection drops the D−2 surplus rows, `≤` subspace bound (not the total partition that killed 23d), `hD` a rank-fact not the walled `hbotmem`. Self-shrank 3a to scaffolding+composition, honestly deferring the satisfiability-critical `hblock`/`hA` construction to 3b. |
| 506 | A4 de-risk spike — CORRECTS §(4.46): A3/A4/cert/arm ALL LANDED (~80% of the spine) but the literal-`Matrix` route does NOT escape the bottom-deficiency wall; genuinely-new core = the `R(Gab)`-reproduction bottom (read-only, tree clean) | —/—/— | opus | recon | recon — corrects §(4.46) prose optimism; all 4 bottom routes wall (high-value) | — | 216k tok / 66 tools / 13.7 min | Read-only A4 de-risk spike (tree clean). CORRECTS §(4.46)'s prose optimism. A3/A4/cert/arm ALL LANDED (~80% of the spine). But the literal-`Matrix` route does NOT escape the bottom wall: the `columnOp` gives 0 LOWER-left (not KT's upper-right), so the operated `e_b` `ab`-fill strands in the discarded block and the bottom is the deficient pure-`Gv` `R(Gv)` (`hD` unsatisfiable = §(4.36)); KT's `R(Gab)` is not a submatrix of `R(G,p)`, matrix-equality BLOCKED. All 4 bottom routes wall. Genuinely-new core = the `R(Gab)`-reproduction bottom. STOP — strategic decision (a/b/c). → §(4.47). |
| 505 | KT §6.4.2 source-faithfulness recon — the override-gate wall is a REPRESENTATION ARTIFACT (dual-span `rigidityRows`), NOT a KT obstruction; KT-faithful fix = the §(4.30) literal-`Matrix` route A, heavy but NOT new math (read-only, tree clean) | —/—/— | opus | recon | recon — reframes the wall as artifact; feasible KT-faithful path found (pivotal/high-value) | — | 113k tok / 15 tools / 2.9 min | Read-only KT §6.4.2 source recon (tree clean). PIVOTAL — REFRAMES §(4.45): the override-gate wall is an ARTIFACT of the dual-span `rigidityRows` representation, NOT a KT wall. KT certifies the interior bottom by an invertible COLUMN op → a LITERAL block-triangular submatrix (6.61→6.64), no span membership / no override-gate, deficiency inherited (IH 6.1). §(4.42)'s option-1 was a row-op-Schur, not KT's column op. KT-faithful fix = the §(4.30) literal-`Matrix` route A (23d's A1–A5c reusable; A3/A4 new ENGINEERING, ~9–14 leaves) — heavy, NOT new math. STOP — strategic decision owed. → §(4.46). |
| 504 | comparative bottom-architecture recon (R1/R2/R3) — ALL THREE WALL on the one §(4.18)–(4.29) override-gate obstruction; route A bottom transport = the §(4.30) genuinely-new heavy residual (read-only, tree clean) | —/—/— | opus | recon | recon — all 3 directions WALL; strategic adjudication owed (high-value) | — | 148k tok / 38 tools / 6.6 min | Read-only comparative compiler-checked recon of the §(4.44) directions (tree clean). HIGH-VALUE — all three WALL on the ONE §(4.18)–(4.29) override-gate obstruction (no full-rank v-blind bottom in `span F₀` when `Gᵥ` deficient). R2 DEAD (k'∈[0,D−2], D=screwDim 2=6 ⟹ k'≥2 generic > 1 fork redundancy). R1 WALLED (`_chain` `W`-producer needs `hG_eb_cand` = the FALSE interior a—b link, kernel-checked = the 23c wall). R3 WALLED (option-1 Schur). Route A's bottom transport = the §(4.30) heavy residual, never built. STOP — strategic adjudication owed (a/b/c). → §(4.45). |
| 503 | LEAF-4 satisfiability spike — option-2 bottom `hbotmem` UNSATISFIABLE (R(Gab) `e₀` rows escape `F₀`); §(4.38) make-or-break refuted (read-only, tree clean) | —/—/— | opus | recon | recon — WALL caught; reverses §(4.43) "CLEAR" (high-value) | — | 240k tok / 79 tools / 38 min | Read-only compiler-checked LEAF-4 spike (tree clean). HIGH-VALUE — REVERSES §(4.43) "CLEAR": the option-2 cert's `hbotmem` is UNSATISFIABLE with `bottom=R(Gab)` — the fresh `e₀=(a,b)` rows escape `span F₀` (G has no a—b link; only redundancy `ρ` lands). = the §(4.36)/(4.37) bottom-deficiency wall; §(4.38)'s "R(Gab) dissolves it" make-or-break (KT (6.61)→(6.62)) was UNSPIKED, now refuted. Count/`hbotindep`(basis route, NOT L-hD)/`hbotblind`/corner compose. Landed 23d leaves sound-but-walled ⟹ rank-cert close premature. STOP — adjudication owed (R1 relabel/`_chain` rec'd). → §(4.44). |
| 502 | 23e phase-open — `notes/Phase23e.md` + ROADMAP cell re-thin + program-doc sync (2da7fb9) | 2/2/1 | opus | normal | clean | ✓✓——✓✓ | 143k tok / 37 tools / 4.4 min | Phase-open (opus, OPUS-ONLY). Docs-only: new `notes/Phase23e.md` (forward-weighted; leaf checklist transcribing §(4.43) with exact decl names + the session-#36-approved C.3 `hIH` add, 1-field, no motive/IH change) + ROADMAP Phase-23 cell re-thin (23a–23d closed; 23e in progress) + `MolecularConjecture.md` program sync. Surfaces (README/home_page/intro.tex) confirm-only (arc-level). Coordinator verified mechanics / no-`.lean` / surface syncs; Phase23e.md hand-off names `chainData_dispatch` next. NEXT = (3) `chainData_dispatch`. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **Session #37 (strategic, non-loop): construct-or-concede spikes + "verify framing against the
  landed source" resolved a "no-estimate open wall" to a GO+assembly verdict** (the §(4.48)–(4.52)
  arc; rows NOT logged individually — a user-directed strategic session, not a `/coordinate-phase`
  loop, and the background-spike costs were not separately captured; canonical record = design
  §(4.48)–(4.52) + git). All-opus. Two high-leverage moves stood out, both already in the
  coordinate-phase command but worth a data point: (1) **the construct-or-concede spike discipline**
  (scratch file, reverted) — three spikes each returned a *kernel-checked* verdict (NO-GO / concede /
  GO) that a prose recon would have gotten wrong (§(4.46)'s prose optimism was the cautionary
  precedent; here every verdict was compiler-grounded); (2) **the "verify against the landed source"
  acceptance check caught a STALE DESIGN-DOC FRAMING** — §(4.49)/(4.50) carried forward "the `d=3`
  discriminator needs generalizing to general `d`", but reading the actual signature (§(4.51)) showed
  it was already `{k:ℕ}` general and landed. The lesson sharpens the command's step-4 rule: a stale
  framing can persist across *multiple* design-§ entries (not just one pin), so re-verify a
  load-bearing "X is only landed at the special case" claim against the decl's actual signature before
  scoping a generalization build on it. The arc also confirmed the recurring-walls trigger (3 NO-GO/
  concede spikes on cert *shape* before the recon found the union-dimension was the irreducible
  shared-downstream object — exactly the "recon the shared downstream object" pattern).
