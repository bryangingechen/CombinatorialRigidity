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
  effect: `haiku-a1` / `sonnet-a2`** (a2 from row 639 on; rows 636/638
  ran a1); step-4 mechanical fixups (wrong branch /
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

| 638 | 23g side-leaf: `Fin.ofNat_eq_mk`/`two_eq_mk_of_lt` OfNat↔mk bridge (`de0b2e17`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 202k tok / 92 tools / 29.8 min | User-directed side-leaf (defuse the FRICTION defeq trap by API), statements pinned in the tailored prompt. Model checked mathlib FIRST per prompt and correctly shrank the deliverable (found `natCast_eq_mk`/`one_eq_mk_of_lt` upstream; landed only the 2 missing forms in a new mirror file, root import wired, FRICTION Resolution + [mirrored] entry honest). No procedural miss this time (turn ended committed). Cost high-ish for a small leaf — mostly the mandated mathlib-coverage search, justified. Coord re-ran build+lint clean. |

| 639 | 23g E2a min-degree ≥ 2 + connectivity (`540fef21`) | 2/2/1 | sonnet | normal | repaired (trailer amend, ~1 min) | ✓✓✓—✓✓ | 106k tok / 13 tools / 3.7 min + resume | E2-split first sub-leaf (coordinator sizing prologue). Lean clean + route-faithful (composed the landed 22i `twoEdgeConnected_of_isKDof_zero` rather than re-deriving; honest `1 ≤ D` floors). TWO sonnet procedural recurrences: (i) turn parked on a background build AGAIN (2nd in 3 builds) → SendMessage-resume; drove the `sonnet-a2` bump (this commit); (ii) trailer copied from git log ("Fable 5") → coord amended (`5a448a5d`→`540fef21`), not graded per attribution-hygiene. Coord re-ran build+lint clean; sorry-grep clean. |

| 640 | 23g E2b degree-2 existence at general `n` (`7d5fe03c`) | 2/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 184k tok / 92 tools / 12.0 min | First `sonnet-a2` dispatch: clean turn-end (foreground gates run to completion — the a2 rail held on its first outing), correct trailer. Better than the pinned route: found the Phase-20 `exists_degree_le_two` already general-`n` (design's "re-run the count" was pessimistic) → pure 2-lemma composition, no new counting. Coord grounded the claim (`ReducibleVertex.lean:627`, `{n}{k}` general at `D ≥ 3`); gates re-run clean; sorry-grep clean. |

| 641 | 23g E2c deficiency count `isKDof_zero_of_cycle` (`8fbda09a`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 281k tok / 79 tools / 35.1 min | P=3 by the generalize-a-landed-lemma trigger → opus. Legitimate scope-to-fit self-shrink: landed the genuinely-new counting core, deferred the wrapper with a sound consumer-first rationale (input shape E2d-dependent) + honest `[◐]` checklist mark. Statement's `link` matches `CycleData.link`'s `⟨1,_⟩` form (future instantiation direct); dropped unneeded `vtx_inj`. Lifted QUIRKS §70 (scoped `Fin` ring instances) properly. Coord: gates re-run clean, sorry-grep clean. |

| 642 | 23g E2c/E2d/E2e design-settle §(4.107.G) (`dcf4ff1a`) | 3/3/1 | fable | normal | clean | —✓——✓✓ | 230k tok / 51 tools / 26.9 min | 2nd fable design pass. Consumer-grounded verdicts: rejected the note's own `(G.induce X).CycleData` wrapper candidate (its `edge_surj` IS the conclusion — burden-shift caught), pinned the walk-builder on READ package API (coord re-grounded `idxOf_get`/`IsPrefix`/`concat_isPath_iff`), reshaped KT's maximal-chain count to a per-vertex-per-direction charge keeping the d=3-tight factor 2. Coord traced the reshape end-to-end (fiber bound, E2d-7 arithmetic vs `no_rigid_edge_count`, E2e tight at n=3,i=3) — sound. E2b honestly de-listed as assembly dep. Whole E2 ladder now S=1. |

| 643 | 23g E2c wrapper `cycle_isProperRigidSubgraph` + helper (`8ff9bd4e`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 294k tok / 130 tools / 32.0 min | Signature landed VERBATIM to the §(4.107.G.5) pin (incl. the `Fin.mk` cyclic forms + internal properness via the third-edge escape); diff tight (104 lines), not bloated despite the cost outlier (130 tools — proof iteration on the induced-edge antisymm computation, visible in a lifted QUIRKS entry). Clean turn-end (a2 rail held again), correct trailer. Coord: gates re-run clean, sorry-grep clean. E2a/E2b/E2c now all landed; hand-off at E2d-1. |

| 644 | 23g E2d-1 path→`ChainData` bridge, opens `ChainExtraction.lean` (`d953c3e1`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 339k tok / 168 tools / 66.8 min | LARGE cost outlier for an exactly-pinned bridge — coord applied the hardest scrutiny: diff TIGHT (139-line new file, both decls pin-verbatim, idiomatic proofs, no bloat/heartbeats). Outlier cause disclosed + legitimate: the vendored `-`-notation poison broke `omega`-adjacent rewrites (broadened QUIRKS §48 in place — proper lift). Clean turn-end, correct trailer. Coord: gates re-run clean (new module + root + lint), sorry-grep clean. |

| 645 | 23g E2d-2 cycle-branch confinement (`4eeb5b33`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 260k tok / 89 tools / 22.2 min | Pin-verbatim signature (`closed_path_degree_two_spanning`), axiom-clean, clean turn-end + correct trailer (3rd consecutive clean `a2` dispatch — the addendum bump is holding). Coord: gates re-run clean, sorry-grep clean. Hand-off at E2d-3. |

| 646 | 23g E2d-3 closed-walk packaging pair (`6f355720`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 274k tok / 83 tools / 24.5 min | Pin-verbatim pair (`exists_cyclic_data_of_closed_path` + `cycleData_of_closed_path`), clean turn-end + correct trailer (4th consecutive clean `a2` dispatch). Coord: gates re-run clean, sorry-grep clean. Hand-off at E2e. |

| 647 | 23g E2e numeric linking facts (no commit) | 1/1/1 | haiku | normal | BLOCKED | —✓———— | 151k tok / 71 tools / 19.4 min | First mapped-haiku build this phase (`haiku-a1` rails; optimistic-ladder 1/1/1 — the pinned route made P look mechanical). HONEST block (a1's stop-don't-improvise held: no commit, no fabrication, correct signatures in the stub) but the failure is capability: ignored the pinned cast-to-ℤ + `nlinarith` route and tried `interval_cases` on unbounded `n`. Coord reverted the partial edit; escalating to sonnet (rows 647→648 escalation pair). ℕ-division casting = P=2 in truth; the 1/1/1 rating was the miss, not the map. |

| 648 | 23g E2e numeric linking facts (`bf65fc9d`) | 1/1/1 (true ~1/2/1) | sonnet | escalation-retry | clean | ✓✓✓—✓✓ | 167k tok / 49 tools / 10.3 min | Escalation of row 647 (haiku BLOCKED): sonnet landed both lemmas in 10 min on EXACTLY the pinned route (ℤ-cast + `nlinarith` w/ the `(n−2)(n−3)` slack + the `hbb` identity), which the coordinator had restated verbatim in the escalation prompt. Pair verdict: the haiku cell cannot execute a *named multi-step tactic route* even at S=1 — haiku stays fit only for true-mechanical (doc/restate) 1/1/1s. Coord: gates re-run clean, sorry-grep clean. Hand-off at E2d-4. |

| 649 | 23g E2d-4 capped trichotomy builder (`de4c6829`) | 1/3/1 | sonnet | boundary-pair-primary | clean | ✓✓✓—✓✓ | 405k tok / 123 tools / 42.9 min | The map-v2 S=1/P=3 sonnet-cell's FIRST in-cell pair (the 22k open data need). Pin-exact statement + the pinned strong-induction architecture; consumed all five bridges exactly as scoped; honest notes + FRICTION entry. Clean turn-end, correct trailer. Coord: gates re-run clean, sorry-grep clean. → pair verdict in row 650. |

| 650 | 23g E2d-4 duplicate (`123472e0`, branch `bp-e2d4`, discarded) | 1/3/1 | opus | boundary-pair-duplicate | clean | ✓✓——✓✓ | 336k tok / 70 tools / 34.9 min | Seeded-worktree duplicate, parallel dispatch. Also pin-exact (+280 vs primary's +291 lines, same architecture); no pin error surfaced (pair-as-pin-audit: the §(4.107.G) settle held under two independent builds). PAIR VERDICT: sonnet HOLDS the S=1/P=3 cell (2nd same-task confirmation after rows 155/156), at ~1.75× tool-uses / ~1.2× wall vs opus — the cell stays sonnet on cost (per-token pricing gap ≫ the iteration overhead). Blueprint/venv gates n/a in worktree (—). Worktree pruned post-log; nothing harvested (diffs equivalent). |

| 651 | 23g E2d-5 chain-walk determinism (`94729abb`, amended from `e5db7d2e`) | 1/2/1 | sonnet | resume | repaired (trailer amend, ~1 min) | ✓✓✓—✓✓ | 188k tok / 29 tools / 12.8 min (+ a killed 36-tool read phase, org spend limit) | Spend-limit kill mid-read-phase (clean tree, no agent fault) → SendMessage resume preserved the read map; landed pin-verbatim first-try after resume. Trailer copied from git log ("Fable 5") AGAIN (2nd, cf. row 639 — both post-resume sonnet commits; candidate a3 clause or CLAUDE.md emphasis). Note compression was the legitimate forward-weighted rebalance (finished-tail collapse, checklist intact). Coord: gates re-run clean, sorry-grep clean. |

| 652 | 23g E2d-6 fiber lemma `chainWalk_isPrefix_of_terminated` (`e8f7227c`) | 1/3/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 161k tok / 33 tools / 9.5 min | Took the design's SANCTIONED candidate split (fiber lemma first, `chainWalk_charging` deferred honestly in the hand-off) — correct scope-to-fit, not a dodge (the split is named in §(4.107.G.5)). Correct trailer after the prompt gained an explicit don't-copy-from-git-log clause (fixes the rows-639/651 recurrence — fold into `sonnet-a3`). Coord: gates re-run clean, sorry-grep clean. |

| 653 | 23g E2d-6 charging bound `chainWalk_charging` (`7321aa55`) | 1/3/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 492k tok / 178 tools / 67.5 min | 2nd large sonnet outlier — scrutinized hard: +217-line dense Finset double-count, NO heartbeats hacks, no bloat markers, statement pin-faithful (unused pinned hyps honestly `_`-ed, instance set adjusted below contract per the pin's own latitude), proper QUIRKS/FRICTION lifts. The S=1/P=3 cell's cost profile is confirming: sonnet lands the cell clean but at 1.5–2× opus iteration cost on dense leaves (cf. rows 649/650) — cell verdict still sonnet on price, revisit at Findings. Coord: gates re-run clean, sorry-grep clean. |

| 654 | 23g E2d-7 arithmetic close (`b816dfa3`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 275k tok / 85 tools / 21.0 min | Pinned-route close (charging + E2e pointwise + handshake vs `no_rigid_edge_count`), completes the E2d sub-ladder. Correct trailer (don't-copy clause holding), clean turn-end, proper QUIRKS/FRICTION lifts. Coord: gates re-run clean, sorry-grep clean. Hand-off at E2-assembly. |

| 655 | 23g E2-assembly `chainData_or_cycleData_of_noRigid` (`dee1adee`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 181k tok / 39 tools / 7.1 min | KT Lemma 4.6 CLOSED — the §(4.107.D) public pin landed VERBATIM in 7 min (the exact-pin ladder paid off: the assembly was pure composition once E2d-4/E2d-7 existed). Correct trailer, clean turn-end. Coord: gates re-run clean, sorry-grep clean. Hand-off at E3. |

| 656 | 23g E3 general extractor `chainData_extract` (`43e9395e`) | 1/2/1 | sonnet | normal | clean | ✓✓✓—✓✓ | 230k tok / 72 tools / 16.7 min | E3 conclusion TEXTUALLY IDENTICAL to the `hextract` slot (coord ran the slot-match check: same `Fin.mk` forms + conjunct order; all E3 inputs available at the consumption site) — `hextract` now dischargeable at general `n`, binder stays for 23h's assembly by design. Bonus: the primitive-field read at `i=⟨1,_⟩` gave the pinned `(a,b)` order directly, no `splitOff_swap_ab` needed. Correct trailer. Coord: gates re-run clean, sorry-grep clean. Remaining: E5 only. |

| 657 | 23g E5 detailed recon — design §(4.108), the E5a–E5c ladder (`36b374c5`) | 3/3/1 | fable | normal | clean | —✓——✓✓ | 218k tok / 54 tools / 15.4 min | 3rd fable design pass, high-yield again: verified KT 5.4 + BOTH source citations (Crapo–Whiteley 1982 Prop 3.4 / Whiteley 1999 Prop 3) against the `.refs/` PDFs; found the feared projective brick mostly LANDED (`rankHypothesis_zero_of_cycle` general, GAP-2 upgrade interface confirmed) — coord re-grounded both decls. Deflated the own-letter-split hedge with a 3–4 commit estimate + keep-in-23g rec, correctly ROUTED the phase-boundary call to the user rather than deciding. Index-family match traced via 4 stated facts. |

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
