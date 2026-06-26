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
grandfathered **rows 1–189**, the **Phase 23a/23b/23c rows 190–434** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23d**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). Open sub-phase = **23d** (`notes/Phase23d.md`). Closed
  sub-phases (22k–23c) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23d.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23d.md` *Hand-off* + the recon
  `notes/Phase23-design.md`; the general-`d` reuse map is §1.33(C) of
  `notes/Phase22-realization-design.md`.
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
  would re-probe. Set/re-confirmed sessions #6–#34 (latest: **#34**, 2026-06-25,
  fresh `/coordinate-phase`; user re-confirmed the Standard triple at
  session start; **availability**: only opus probed under OPUS-ONLY, reachable via the
  Agent `model` param, no substitution needed, other rungs un-probed). **The override
  expires session-end — a fresh coordinator re-runs the session-start availability check +
  re-confirms the triple.** **Session #33 ADJUDICATED the open route-A design decision
  (row 473's cert-SHAPE FLAG): the user chose option (4b′)** — reshape the cert kernel
  (A3/A4 in `Rank.lean`) to a row-SUBMATRIX (injection `em : m₁⊕m₂ ↪ rows`, ignoring the
  `D−2` surplus `v`-rows); options (4a)/(C) declined, route A stays the plan. No open
  design decision is owed (4b′ adjudicated; the A6 plan is in §(4.34)). Phase status +
  next dispatch live in `notes/Phase23d.md` + the ROADMAP cell, **not here**.
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
Rows 1–434 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 435 | A1 §I.8.21(α) feasibility spike (→ design §(4.22)) | —/—/— | opus | recon | recon — verdict UNSOUND, caught | — | 171k tok / 36 tools / 8.9 min | First-pass FEASIBLE = a route-COMPOSITION verdict (static-`W` cert type-checks w/ corner data carried as hyps; lone residual = spine deficiency) mis-read as dischargeability; leaned on the §(4.18)-dead cert + §(4.17)-dead router branch, and answered the wrong A1 question (the existing cert, not the new matrix-infra). Mechanically clean, substantively unsound — caught only by the coordinator confronting prior kernel impossibilities. → Findings 2026-06-24. |
| 436 | A1 spike resume — construct-or-concede (→ §(4.22)) | —/—/— | opus | recon/resume | recon — CONCEDED | — | 194k tok / 9 tools / 3.3 min | SendMessage-resume of 435 (same agentId, context intact) w/ the §(4.17)+§(4.18) confrontation. CONCEDED; built 2 sorry-free `concede_*` kernel re-derivations of the impossibilities for the real dispatch slot; confirmed SPIKE 1/2 carried `hG_eb_cand`/`W`/`hWS` as hyps, never discharged. Resume reused the full read phase (9 tools) — cheap vs a fresh refute agent. → Findings 2026-06-24. |
| 437 | §I.8.21(α) matrix-level (row-op) rework spike (→ design §(4.23)) | —/—/— | opus | recon | recon — INFEASIBLE (hypothesis disproven) | — | 199k tok / 71 tools / 15.3 min | User-authorized rework swing: does KT's rank-preserving ROW-OPERATION redundancy handling (vs span membership) escape the wall? DISPROVEN at the kernel (SPIKE 3b/4a/4b): the row-op IS the membership — pure-`vᵢ` corner needs `hingeRow a b ρ₀ ∈ span` (=hρGv), confirmed against the project's OWN Phase-22g `r̂=wGv` docs. The scissors: htopvanish-corner needs hρGv; hρe₀-corner not pure-vᵢ. 4th independent wall confirmation; honest INFEASIBLE (flag-don't-force worked) → option (C). → Findings 2026-06-24. |
| 438 | geometry-aware-transport scoping recon (→ design §(4.24)) | —/—/— | opus | recon | recon — RELOCATES-TO-WALL (scoping) | — | 202k tok / 51 tools / 9.8 min | Scoped the user's "remember the geometry" transport idea. Found the transport is ALREADY geometry-aware (`shiftPerm`=KT ρᵢ, `qρ`=config relation, `rigidityRow_relabel_to_genuine` absorbs reproduction as abstract `hsupp`) — corrects the coordinator's "remembers only σ" framing. Closed by a LINEARITY IMPOSSIBILITY (SPIKE 3): linear `T` forces `T(Σcⱼgⱼ)=Σcⱼ T(gⱼ)`, so the redundant row lands at its ρᵢ-image (moved member), never fixed `hφ`. 5th wall confirmation; transport layer CORRECT (nothing to rework). → Findings 2026-06-24. |
| 439 | route-B (genuine-basis) architecture pass (→ design §(4.25)) | —/—/— | opus | recon | recon — B-WORKS (pending LEAF-B1) | — | 235k tok / 71 tools / 20.7 min | Architecture pass on the user-directed faithful re-arch. FOUND the escape after 5 wall-confirmations: an inversion faithful to KT (6.64) — redundant row → CORNER (hρe₀), genuine rows → base block W (off-vᵢ, transport works). Q1/Q2 kernel-spiked sorry-free, axiom-clean; CONSTRUCTED Q2-B/C/D (the satisfiability §(4.18) called impossible for the redundant-INCLUDING block). Honestly flagged the ONE carried hypothesis = LEAF-B1 (genuine-basis extraction) as crux/risk — flag-don't-force + construct-discipline worked. Light reformulation, not a Matrix rebuild. → Findings 2026-06-24. |
| 440 | LEAF-B1 genuine-basis extraction — build resume (b239c97) | 2/3/1 | opus | resume | clean | ✓✓✓✓✓✓ | 309k tok / 82 tools / 18.3 min | Spike-salvage build resume of 439 (rescue §6): CONSTRUCTED the route-B crux LEAF-B1 + Q2-B, sorry-free + axiom-clean. PASSED the construct-or-concede test that caught the 2 false FEASIBLEs — coordinator read the proof: genuinely constructed via mathlib `exists_fun_fin_finrank_span_eq`, NOT carried; the structural-twin risk (motive strengthening) dissolved (link data free from set-membership). Salvage: 3/4 thin wrappers correctly SKIPPED. → Findings 2026-06-24. |
| 441 | LEAF-B2 genuine-only `W` producer (dd26563) | 2/2/1 | opus | normal | clean (1 carried-hyp flag) | ✓✓✓✓✓✓ | Fresh routine build. Clean 3-lemma composition (LEAF-B1 + LEAF-2 + the card fact) → the route-B base block, sorry-free/axiom-clean/warning-clean. Agent CORRECTED the coordinator's perm-direction slip (σ = (shiftPerm)⁻¹ → σ.symm v = vtx 1, the removed base body, resolving `hvanish` at the signature level). Legitimate slice but CARRIES `hS`/`hvanish` universally over `Fbase.rigidityRows` (discharge deferred to LEAF-4); coordinator flagged the universal `hS` as possibly too strong (the §4.17-dead branch) — the one residual route-B risk, pinned in the hand-off. → Findings 2026-06-24. |
| 442 | LEAF-4 `hvanish` half — `ofNormals_removeVertex_rigidityRow_comp_single_self` (5d742bd) | 2/2/1 | opus | normal | clean (scoped to hvanish half) | ✓✓✓—✓✓ | 149k tok / 49 tools / 13.3 min | Scope-to-fit shrink of LEAF-4 to its `hvanish` half. Landed `ofNormals_removeVertex_rigidityRow_comp_single_self`: every rigidity row of `ofNormals (G−v)` annihilates `single v`, universal over the WHOLE family (no per-member split) — destructure each `(G−v)`-link row → `x,y≠v` (`removeVertex_isLink`) → `hingeRow_comp_single_off`. Coordinator confirmed the `hvanish` satisfiability vs the consumer's actual object (instantiable at `v=vtx 1`, `σ.symm vᵢ=vtx 1`). The flagged `hS`-universal-form router (genuine vs §4.17-dead branch) is the remaining substantive LEAF-4 piece. |
| 443 | LEAF-4 `hS`-router half — `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` (1a87dee) | 2/2/1 | opus | normal | clean (residual risk RESOLVED) | ✓✓✓—✓✓ | 179k tok / 57 tools / 13.3 min | Flagged route-B residual-risk piece, RESOLVED. = LEAF-B2's universal `hS` slot via a 2-brick composition `chainData_bottom_relabel … (Or.inl hφ)` → `bottomRelabel_image_mem_span_caseIIICandidate` (23c routers). The `Or.inl` genuine-row feed routes EVERY base row through the cert-SOUND branch; the output block-tag arm uses the genuine candidate link `hG_eb_cand` (a `G.IsLink`, NOT the §4.17 `hρGv` the wall was about) — `hS` provably closes, no narrowing/route A. Coordinator confirmed LEAF-B2's `W` sits at the assembly's `W`-slot level; next = the assembly call. |
| 444 | LEAF-4 assembly call — `case_III_arm_corner_assembly_via_leafB2` (0f1d3b2); rank cert CLOSED via route B | 2/2/1 | opus | normal | clean (LEAF-4 COMPLETE) | ✓✓✓—✓✓ | 160k tok / 57 tools / 10.7 min | LEAF-4 COMPLETE; rank cert CLOSED via route B. `case_III_arm_corner_assembly_via_leafB2`: 2-step composition — `obtain` LEAF-B2's `(W,hWS,hWcard,hW)` at `Fcand = F₀` (the assembly's OWN candidate), then `exact case_III_arm_corner_assembly`. Design call: `Fcand = F₀` DISSOLVES the framework-alignment bookkeeping (the relabel form is pushed into the dispatch's `hS` discharge). Conclusion `HasGenericFullRankRealization k n G`; carries `hS`/`hvanish`-universal + the RAW interface as the dispatch's discharge obligation. ROADMAP kept `◐ In progress`. Next = CHAIN-2c-iii dispatch. |
| 445 | interior-`hρe₀` producer — `interior_hρe₀_of_widening` (446273a) | 2/2/1 | opus | normal | clean (scoped; dispatch gap flagged) | ✓✓✓—✓✓ | 199k tok / 47 tools / 8.7 min | Scope-to-fit (full `chainData_dispatch` is multi-commit): landed the interior-`hρe₀` producer `interior_hρe₀_of_widening` — produces `case_III_arm_corner_assembly_via_leafB2`'s `hρe₀` slot from the W6b edge-grouped widening bundle, composing the landed crux `baseRedundancy_perp_interior_reproduced_panel` + the relabel bridge. Discovered gap (source-verified): LEAF-3 discards the `hedgeGv` bundle this consumes; `chainData_split_w6b_gates` DOES expose it (Realization.lean:825) — dispatch re-fires/widens to feed it. Interior arm's 4 producers all landed; remaining = `chainData_dispatch` wiring. |
| 446 | LEAF-3 widening — re-expose W6b `hedgeGv` bundle (3771023); interior-arm gap closed | 2/1/1 | opus | normal | clean (gap closed) | ✓✓✓—✓✓ | 151k tok / 43 tools / 10.6 min | Closed the interior-arm gap (prior-row discovered). Widened LEAF-3 `exists_shared_redundancy_and_matched_candidate`'s output ∃ to re-expose the W6b edge-grouped `G_v`-row widening bundle: `_hedgeGv`→`hedgeGv` in the W6b `obtain` + the matching conjunct via `refine`. Pure output widening, value flows from `chainData_split_w6b_gates` — no new proof. Coordinator-verified: LEAF-3 NOT blueprint-pinned (per-slice statement-change gate OK) + no callers (widened ∃ caller-safe). Dispatch now reads `hρe₀` off LEAF-3, owing only the `(a,b)`→`(vtx 0,vtx 2)` re-anchoring + the Fin-case router alignment. |
| 447 | interior-`hρe₀` re-anchoring — `interior_hρe₀_of_baseWidening` (eaf6cad); dispatch `hρe₀` now one-call | 2/2/1 | opus | normal | clean (re-anchoring-free) | ✓✓✓—✓✓ | 175k tok / 59 tools / 12.7 min | 3rd interior-`hρe₀` commit (re-expose→producer→re-anchor); owed work monotonically shrank, NOT thin-wrapper deferral. Landed `interior_hρe₀_of_baseWidening`: folds LEAF-3's `hedgeGv` bundle (`(a,b)=(vtx0,vtx2)`) + `hends_i` into `interior_hρe₀_of_widening`, discharging the 3 re-anchorings INTERNALLY — `hcomb.symm`, `G−vtx1`→`G` link-lift, and a real `hdeg1` degree-2 argument at `vtx 2` (`deg_two` minus the `vtx 1`-incident `edge 1`). Genuine content. Dispatch now reads interior `hρe₀` in ONE call; owes only the `Fin cd.d` router + the `hS`-candidate `endsσρ`/`qρ` alignment. |
| 448 | interior-split `heab_off` accessor — `removeVertex_isLink_edge_succ_pred_off` (7d51345) | 2/1/1 | opus | normal | clean (4th leaf; cost outlier) | ✓✓✓—✓✓ | 202k tok / 71 tools / 30.8 min | 4th consecutive dispatch-input leaf (`hρe₀`-prod → LEAF-3-widen → `hρe₀`-reanchor → this). `removeVertex_isLink_edge_succ_pred_off`: every `G−vtx i`-link uses an edge ≠ `edge i`/`edge (i−1)` (both incident to removed `v`, contra `removeVertex_isLink`) — the `hS` router's `heab_off`, now one-call. Sound 3-step, no bloat. COST OUTLIER: 30.8 min for a tiny accessor → the agent explored the `chainData_dispatch` ROUTER, found it hard, retreated. 4 leaves + unbuilt core + outlier (the 22g pattern) → coordinator triggers a compiler-checked spike on the router next, not a 5th leaf. |
| 449 | dispatch recon — compiler-checked spike of `chainData_dispatch` → GAP 1 | —/—/— | opus | recon | recon — GAP 1 found (route-B interior `hS` unsatisfiable) | — | 220k tok / 67 tools / 16.7 min | Coordinator-triggered after 4 leaves + a cost outlier (22g pattern). Read-only compiler-checked spike of `chainData_dispatch`: built the `Fin cd.d` skeleton + interior arm, sorry'd the gaps, mapped residuals. FOUND GAP 1 (decisive): the interior `hS` is UNSATISFIABLE — the wrap-edge `edge i` row relabels to the reproduced-slot `(a,b)`-block tag, whose routing needs `hG_eb_cand : G.IsLink (edge (i−1)) (vtx(i+1)) (vtx(i−1))`, kernel-PROVED false. Other interior slots (`hgate`/`hρe₀`/`hvanish`/`heab_off`/`hrec`/`hrhat`/`hIH`) spike-verified mechanical. No commit (read-only). |
| 450 | spike resume — GAP 1 investigate / fix-or-flag (592a202, docs) | —/—/— | opus | recon/resume | recon — BLOCKED (phase decision) | — | 300k tok / 46 tools / 9.2 min | SendMessage-resume of 449 (read-only LIFTED for salvage). GAP 1's fix is NOT a clean leaf: root cause = LEAF-B2 hardcodes `Fcand = caseIIICandidate` (corner-overridden), but KT (6.62)'s bottom block maps to the candidate's SEED framework `ofNormals (G−vᵢ) endsρ qρ`; the wrap-edge row is the independent `±r` corner row (option A transports it only as a GROUP), so individual-row `hS` re-introduces the wall. Fixes (phase-direction): (4) seed-framework re-arch, or fall back to option-A's LANDED group transport. Committed design §(4.26) + note/ROADMAP corrections. BLOCKED for adjudication. |
| 451 | dispatch recon — scope option-A `W`-production (6800e9b, design §4.27) | —/—/— | opus | recon/resume | recon — VERDICT (B): option A walls; route 4 wall-free | — | 375k tok / 39 tools / 10.3 min | SendMessage-resume of the spike to scope the option-A fallback. VERDICT (B): the option-A engine `W` ALSO walls (takes `hρGv`; per-`i` realization needs out-of-scope IH + unrelated `ρᵢ`), correcting the §(4.26) hope. WALL-FREE = route 4 (seed-framework): `W := span(candidate seed rows)`; `hWS`/`hW` kernel-verified wall-free (`probe3_seed_W`), residual = `hseedrank` = the relabel rank-iso (`hρGv`-free, base IH). COST ≈ 2 leaves + dispatch + CHAIN-5; de-risk = NEW LEAF 1 (general-`d` `rigidityRows_ofNormals_relabel`, chain-generalize the `d=3` lemma, MEDIUM). Committed §(4.27). |
| 452 | route-4 NEW LEAF 2 — `exists_seed_base_block` (057a86e); seed-`W` producer | 2/2/1 | opus | build/resume | clean (2 rounds; bg-build stall recovery) | ✓✓✓—✓✓ | 76 tools / ≈25 min (2 resume rounds) | Build-resume of the spike, salvaging its verified `probe3_seed_W`. Landed `exists_seed_base_block` (route-4 NEW LEAF 2, wall-free seed-`W` producer): `W := span(candidate seed rows)`; `hWS`/`hW` discharged with NO `hS`/`hρGv`; `hWcard` ⟵ `hseedrank` — the genuinely-true relabel rank-iso, a SATISFIABLE hyp NEW LEAF 1 discharges (NOT route B's unsatisfiable `hG_eb_cand`). Took 2 resume rounds: build-resume STALLED awaiting a background `lake build`; a finish-resume ran the gate foreground + committed. NEXT = NEW LEAF 1 (the involution-fail/splitOff-bridge risk). |
| 453 | route-4 NEW LEAF 1 build (fresh agent) — BLOCKED: `hseedrank` false for the bare seed (→ §4.28) | —/—/— | opus | build | BLOCKED — route 4-bare walls (caught the §4.27 error) | — | 154k tok / 26 tools / 4.9 min | FRESH agent (spike context degrading). Recon-before-building found `hseedrank` PROVABLY FALSE for the BARE seed: the wrap edge `edge i` relabels (landed `removeVertex_genuine_shiftRelabel` `Or.inr`) to the non-chain pair `(vtx(i−1),vtx(i+1))`, absent from `R(G − vᵢ)`. The landed `d=3` relabel iso is SPLITOFF-only. CONTRADICTS + corrects §(4.27) (asserted `hseedrank` from a bare-seed iso the coordinator accepted without reading the lemma's splitOff form). Wrap-edge wall, 3rd time. → §(4.28); route 4-splitOff is the unverified fix; user decision owed. No commit. |
| 454 | route-4-splitOff verify-first spike (50af6e0, §4.29) — Q1 wall-free, Q2 WALLS | —/—/— | opus | recon/resume | recon — route 4-splitOff WALLS (4th wrap-edge; base-block family CLOSED) | — | 293k tok / 87 tools / 23.6 min | Verify-first spike. Q1 (splitOff↔splitOff relabel rank-iso, non-involutive cycle) = WALL-FREE, sorry-free (~40 LoC; involution facts NOT load-bearing). Q2 (`hWS`: the splitOff seed's fresh `e₀'` row ∈ candidate span) = WALLS: `e₀' ∉ E(G)` kills the off-slot bridge; the difference-collapse through `vᵢ` needs `ρ' ⊥ C(vᵢ₊₁,n')` (the OVERRIDDEN slot), gate-violated. The wall = the discriminator gate, intrinsic to the `caseIIICandidate` slot-override, INVARIANT under base-block re-targeting (4th: A/B/4-bare/4-splitOff). Base-block family CLOSED → route A vs (C). Q1 bankable. §(4.29). |
| 455 | route-A feasibility scoping recon (5216e2b, §4.30) — FEASIBLE but HEAVY (~9–14 leaves) | —/—/— | opus | recon | recon — route A FEASIBLE (genuinely ≠ refuted §4.22/4.23), HEAVY | — | 216k tok / 57 tools / 9.8 min | Scope-route-A recon. Reconciled §(4.23) "wall intrinsic to KT" vs §(4.29): §(4.22)/(4.23) refuted an abstract span-block-rank lemma WITHIN the dual-space rep (KT (6.61) as a MEMBERSHIP = the wall); route A is a from-scratch mathlib `Matrix R(G,p)` where (6.61) is an entrywise column-op (`Matrix.rank_mul_eq_right_of_isUnit_det`, confirmed), NEVER a membership → wall dissolves. VERDICT: FEASIBLE but HEAVY (~9–14-leaf sub-phase; A3/A4 genuinely-new; no existing Matrix infra). Residual: A1/A2 opacity constant-factor (a d=3 spike settles). Decision = A-vs-(C) on COST. §(4.30). |
| 456 | route-A A1+A2 `d=3` de-risk — `rigidityMatrix` + the rank bridge (803ad8c); opacity CLEAN | 3/2/1 | opus | build/resume | clean (de-risk PASSED) | ✓✓✓—✓✓ | 334k tok / 117 tools / 25.1 min | Build-resume of the route-A scoping agent, salvaging §4.30. Landed A1 (`rigidityMatrix`, the literal `(D−1)|E|×D|V|` matrix) + A2 (the `rigidityMatrix_rank_eq_finrank_span_rigidityRows` capstone via a carrier-agnostic `Matrix.rank_of_dualCoord` core) in new `RigidityMatrix/Concrete.lean`, axiom-clean. DE-RISK PASSED: the `ScrewSpace`-opacity composition is CLEAN — `Matrix.rank_eq_finrank_span_row` fires through the opaque carrier with zero detour (§4.30's residual RESOLVED). Capstone lands on the honest `finrank(span rigidityRows)`. Leaf count ≈7–11. NEXT = A3 (matrix block-additivity). |
| 457 | route-A A3 — block-additivity kernel `Matrix.rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` (fc9682a) | 2/3/1 | opus | normal | clean (genuinely-new piece) | ✓✓✓—✓✓ | 164k tok / 81 tools / 23.4 min | Routine build of the route-A genuinely-new piece. Landed `rank_fromBlocks_zero₂₁_ge_of_linearIndependent_rows` (upstream `Rank.lean`): KT (6.64) block-additivity as a pure-`Matrix` rank inequality, forming NO span membership (= why route A dissolves the §(4.18)–(4.30) wall the dual-space cert hit). Came in at ~1 clean leaf, under the ~2–3/MEDIUM-HIGH estimate. Friction→QUIRKS§64. Coordinator (opus=below-top-rung): read statement+proof (sound; A3/A4 split faithful), warning-clean rebuild, axiom-clean. NEXT=A4 (column-op). |
| 458 | route-A A4 — the (6.61) column-op bridge `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` (93770ac) | 2/2/1 | opus | normal | clean (scope-to-fit; crux deferred to A5) | ✓✓✓—✓✓ | 129k tok / 49 tools / 21.8 min | Scope-to-fit shrink to the BRIDGE half. Landed the A4→A3 bridge `rank_ge_of_isUnit_mul_reindex_fromBlocks` (`Rank.lean`) + specialization: KT (6.61) = rank-invariant unit-det right-multiply, never span membership. DEFERRED-CRUX-AS-HYP: bridge takes `hblock:(M*U).reindex=fromBlocks A B 0 D` as a hyp → the genuinely-new explicit-`U` build + `hblock` discharge (§(4.21) 'WHOLE content') relocates to A5. Coordinator: sound reusable slice; the crux is HONESTLY re-flagged as A5's cost-outlier (NOT re-buried) → rate A5 by the `U`-build; warning-clean rebuild, axiom-clean. |
| 459 | A5 route-composition compiler-checked spike → re-route to add leaf A4.5 (ce535fd, design §4.31) | —/—/— | opus | recon | recon — VERDICT: A5 needs a preceding re-coordinatization leaf (route A sound) | — | 181k tok / 91 tools / 13.1 min | Coordinator-triggered spike of A5 (recon trigger #7 + flat-vs-product column concern; defeq-fragile → spike not prose, rescue §6). VERDICT: A5-as-scoped UNDISCHARGEABLE on the flat `rigidityMatrix` (arbitrary `finBasis` cols don't factor `α × Fin D`); route A's escape HOLDS → fix = ONE preceding re-coordinatization leaf A4.5 (`rigidityMatrixProd`, same honest rank). 5 probes SORRY-FREE; A4.5/A5/A6 sigs in §(4.31). Flag-don't-force worked: no motive/IH change, no phase-direction call owed. Coordinator: re-route orphans no obligation; 'same rank' SCHEDULED as A4.5d, not assumed. NEXT=A4.5. |
| 460 | route-A A4.5 build (resume of the 459 spike) — product-column matrix + generalized rank bridge (fc6954f) | 1/2/1 | opus | build/resume | clean (7 decls, axiom-clean) | ✓✓✓—✓✓ | 258k tok / 56 tools / 12.0 min | Build-resume of the spike (rescue §6 salvage) → 7 axiom-clean decls in `Concrete.lean`: the recommended refactor `rank_of_dualCoord`→generalized `rank_of_coordEquiv` (flat instance PRESERVED, no orphan, capstone green) + `rigidityMatrixProd` (cols factor `α×Fin D`) + the product honest-rank bridge. Friction: name `screwBasis` clashed (PanelLayer, out of import-closure) — single-file build PASSED but whole-project `lake lint` caught it → QUIRKS §65 (name-check + run lint, not just build). Coordinator: shape OK, warning-clean rebuild + RE-RAN `lake lint` (PASSED), axiom-clean. NEXT=A5a. |
| 461 | route-A A5a — the (6.61) column-op-as-right-multiply on `rigidityMatrixProd` (c65e0df) | 1/2/1 | opus | normal | clean (3 decls, axiom-clean) | ✓✓✓—✓✓ | 147k tok / 60 tools / 8.7 min | Routine FRESH build (chose fresh over a 3rd spike-resume: A5a fragments fully quoted in §(4.31), spike context heavy). Landed the 3 A5a column-op pieces in `Concrete.lean`, matching spike PROBE 2c/4: `prodColumnOpEquiv`, the `IsUnit U.det` 4-liner, and `rigidityMatrixProd_mul_columnOp_row` (the row identity). KT (6.61) = rank-preserving right-multiply, no `ScrewSpace` unfolding, never a span membership. Coordinator: shape matches §(4.31) exactly, warning-clean rebuild + `lake lint` PASSED, axiom-clean. NEXT=A5b (Mᵢ gate re-wrap, content landed). |
| 462 | route-A A5b — the gate re-wrap (LI-transport bridge `linearIndependent_row_of_coordEquiv`) (40be3a0) | 1/2/1 | opus | normal | clean (2 decls; gate-cert wiring deferred to A5c) | ✓✓✓—✓✓ | 168k tok / 70 tools / 9.1 min | Routine fresh build, scope-shrunk to the generic LI-transport BRIDGE (`linearIndependent_row_of_coordEquiv`). DEFERRED: the gate-cert wiring (Mᵢ rows LI from the landed `interior_group_eq_baseRedundancy`+`omitTwoExtensor_linearIndependent`) → A5c, NOT done here. Coordinator: iff sound + reusable, but this is the 4th consecutive infra/bridge leaf feeding the unbuilt hblock+gate core (22g pattern); MITIGANT = the A5 spike kernel-verified the core dischargeable. Warning-clean + lint PASSED, axiom-clean. NEXT=A5c (hblock + deferred gate discharge — concentrated crux; consider decomposition). |
| 463 | route-A A5c-keystone — the (6.61) zero block entrywise (`rigidityMatrixProd_apply_eq_zero_of_ne`) (6f57ae3) | 2/3/1 | opus | normal | clean (2 decls; assembly deferred) | ✓✓✓—✓✓ | 196k tok / 95 tools / 13.8 min | Routine build, scope-shrunk to the A5c KEYSTONE — assembly deferred (needs chain-data geometry). Landed `dualProductCoordEquiv_apply` (PROBE-5 entrywise identity) + `rigidityMatrixProd_apply_eq_zero_of_ne` (KT (6.61)'s lower-left zero block, entrywise-true: entry vanishes when body∉{edge endpoints}). SUBSTANTIVE crux content, NOT plumbing. Friction: frozen `Classical.decEq` on Σ-index forced `simp only` over `rw` → QUIRKS §66. Coordinator: both sound + substantive, warning-clean + lint PASSED, axiom-clean. NEXT=A5c-assembly (em/en + fromBlocks; COUPLED to chain-data geometry + A6). |
| 464 | route-A A5c operated-entry facts — the (6.61) zero block of `M*U`, entrywise (1c25bb8) | 2/3/1 | opus | normal | clean (2 decls; assembly deferred 3rd time) | ✓✓✓—✓✓ | 176k tok / 52 tools / 8.9 min | 3rd consecutive scope-shrink deferring the A5c-assembly (em/en + fromBlocks reindex) for the SAME reason ('needs chain-data geometry'). Landed the OPERATED entrywise facts: `rigidityMatrixProd_mul_columnOp_apply` + `_apply_eq_zero_of_ne` (operated (6.61) zero block). Sound prerequisites, NOT padding. Coordinator: leaf count CONVERGED 7–11→1.5–3 (not a 22g stall — all prerequisites landed), BUT 3 deferrals citing the chain-data geometry = recurring-wall trigger → NEXT = a RECON of the assembly/A6 chain-data coupling (spike), not a 4th entrywise leaf. Gates clean (warning + lint + axiom). |
| 465 | A5c+A6 integration compiler-checked spike → re-point next leaf to A4.5e (edge-restricted matrix) (64fbf25, §4.32) | —/—/— | opus | recon | recon — VERDICT: A6 skeleton fires; 1 un-surfaced leaf A4.5e needed (route A sound) | — | 256k tok / 77 tools / 16.3 min | Integration spike (recurring-wall trigger). VERDICT (5 probes SORRY-FREE): the A6 skeleton FIRES on the actual arm (route A replaces the walled cert at the `Arms.lean:350` seam) — BUT a level-mismatch one layer up: the A2/A4.5d capstones need `hgp`/`hends` TOTAL over β, unsatisfiable on the real arm (non-edges `e₀∉E(G)`; deferred-hyp-unsat trap + ZERO callers). Fix = 1 un-surfaced leaf A4.5e (edge-restricted matrix over `{e//e∈E(G)}`, PROBE 6 SORRY-FREE). Q(d) clean. Coordinator: capstone total-β hyps + zero-callers CONFIRMED vs source. Re-decomp ≈3.5–5.5 (A4.5e→A5c→A6). NEXT=A4.5e. |
| 466 | route-A A4.5e — the edge-restricted rigidity matrix `rigidityMatrixEdge` (862ebc4) | 1/2/1 | opus | normal | clean (6 decls, axiom-clean) | ✓✓✓—✓✓ | 195k tok / 91 tools / 12.3 min | Routine fresh build of the recon-surfaced A4.5e. Landed 6 decls in `Concrete.lean` (`rigidityMatrixEdge` over `{e//e∈E(G)}` + edge-restricted span identity + honest-target capstone) — resolving the §(4.32) all-β-vs-edge mismatch: edge-restricted row index + SATISFIABLE `∀ e∈edgeSet, hgp/hends` (the all-β capstones were arm-unsatisfiable). Rank bridge = 1-line `rank_of_coordEquiv` on Subtype rows. Friction: `E(G)` scoped-notation trap → QUIRKS §67. Coordinator: capstone lands on honest `span rigidityRows` w/ satisfiable hyps, warning-clean + lint PASSED, axiom-clean. NEXT=A5c (rank-cert crux). |
| 467 | route-A A5c composition core `finrank_span_rigidityRows_ge_of_edge_fromBlocks` (2d910b6) | 2/3/1 | opus | normal | clean (1 decl; hblock deferred 4th time) | ✓✓✓—✓✓ | 165k tok / 50 tools / 7.0 min | Routine build, scope-shrunk to the A5c COMPOSITION CORE — hblock construction deferred (4th deferral). Landed `finrank_span_rigidityRows_ge_of_edge_fromBlocks` (spike PROBE-2 body): edge-restricted hyps + geometry inputs U/em/en/hblock/hA/hD ⟹ honest-target bound (A4 bridge + A4.5e capstone). Sound, not vacuous. Coordinator: residual now FULLY isolated (supply U[landed]/em-en[PROBE 3]/hblock[landed zero-block]/LI[A5b iff]) — nothing left to extract; next dispatch MUST build the hblock (5th deferral = recon/decompose). Warning-clean + lint PASSED, axiom-clean. NEXT=A5c hblock residual (crux). |
| 468 | route-A A5c `en` column split — `columnSplit` (the (6.62)–(6.64) corner reindex) (fe5c0a6) | 2/3/1 | opus | normal | clean (2 decls, axiom-clean) | ✓✓✓—✓✓ | 164k tok / 53 tools / 7.8 min | 5th A5c-layer scope-shrink, now landing a PIECE of the hblock itself (not a new prerequisite — convergence, as the coordinator flagged). Landed `columnSplit` (the `en`: partitions `α×Fin D` into corner `{body=a}×Fin D` ⊕ rest, KT (6.62)–(6.64) corner isolation as a pure product reindex) + `columnSplit_corner_card = screwDim k`. 2 of 3 composition-core inputs in hand (U[A5a], en[here]); remaining = `em` row split + `hblock` equality + LI → cert. Sound, carrier-agnostic. Coordinator: decl + card sound, build/lint/warning/axiom-clean. NEXT = `em` + `hblock` residual. |
| 469 | route-A A5c `em` panel-row split — `edgeRowSplit` (the (6.66) corner-edge row partition) (2d5b37c) | 2/3/1 | opus | normal | clean (2 decls, axiom-clean) | ✓✓✓—✓✓ | 164k tok / 40 tools / 6.0 min | 6th A5c-layer scope-shrink — the layer is being sliced VERY granularly. Landed `edgeRowSplit` + `edgeRowSplit_corner_card` (the `em` panel-row analog of `columnSplit`: corner-edge `(D−1)`-row partition). 3/4 composition-core inputs in hand (U/en/em-panel); remaining = the `+1` reproduced e_b row + the hblock EQUALITY (the hard proof, deferred each time) + cert wrap. Coordinator: build/lint/warning/axiom-clean. PATTERN: easy structural inputs land, the hblock entrywise proof keeps deferring → surfacing a checkpoint (over-slicing + marathon session). NEXT = +1 row + hblock. |
| 470 | route-A cert `case_III_rank_certification_matrix` — the (6.64) drop-in (resume-drive of 469) (0fa8c5a) | 2/3/1 | opus | build/resume | clean (cert LANDED; hblock carried as hyp → A6) | ✓✓✓—✓✓ | 278k tok / 65 tools / 23.9 min | RESUME-DRIVE (user-chosen): the warm resume drove A5c through to the CERT (not a micro-piece). Landed `case_III_rank_certification_matrix` (Candidate.lean): a faithful BYTE-IDENTICAL drop-in for the walled `_chain`, consuming matrix block data (U/em/en/hblock/hA/hD) where `_chain` took dual-space (W/g). Crux `hblock` carried as a HYPOTHESIS per the 'crux-as-hyp, never sorry' idiom → A6. Coordinator: conclusion byte-matches `_chain`, `_chain` dead-but-sound, acyclic import Candidate→Concrete, build(2777)+lint+warning+axiom-clean. NEXT=A6 (hblock construction — the MED-HIGH crux — + arm wiring). |
| 471 | route-A A6 edge-restricted (6.61) operated-entry facts (b97063b) | 2/3/1 | opus | normal | clean (3 decls; closed a spike-hand-waved gap) | ✓✓✓—✓✓ | 170k tok / 61 tools / 14.8 min | A6 scope-shrink to the edge-restricted entry facts — CLOSED a real gap: the facts were on `rigidityMatrixProd` (all-β), the cert consumes `rigidityMatrixEdge` (edge); §(4.32) + coordinator assumed 'row-index-agnostic carries' but they're distinct lemmas. Landed the three `rigidityMatrixEdge_mul_columnOp_*` mirrors, so the hblock's entrywise reads now exist on the cert's edge row index. Coordinator: sound, sorry-clean, build/lint/warning/axiom-clean. Lesson: 'carries verbatim' was imprecise — distinct matrix defs need distinct entry lemmas. NEXT = hblock equality + em(+1 row); resume-drive. |
| 472 | A6 hblock crux — resume-drive → BLOCKED (caught the §(4.32) garbled corner index map) | —/—/— | opus | build/resume→BLOCKED | recon — design error caught (high-value) | — | 209k tok / 15 tools / 4.1 min | Resume-drive of hblock → BLOCKED, HIGH-VALUE design-error diagnosis: §(4.32)'s corner index map is GARBLED — corner pinned at `v=(ends e_b).1` not `a`, so `en:=columnSplit v` not `a` (the latter ZEROS the corner block — provably wrong). The row-471 edge zero lemma also has the wrong vanishing condition for the 0 block; bottom block = the real depth (4a/4b choice). Agent correctly declined a guessed-wrong hblock — model WIN. Coordinator: confirmed pin-at-`v` vs source (the error my §(4.32) acceptance missed); salvaged to design+hand-off (3fc73c1). NEXT = recon/spike the corrected route. |
| 473 | corrected-hblock spike → 3 §(4.33) bricks LANDED + cert-SHAPE obstruction FLAGGED (f6ca0a6, §4.33) | —/—/— | opus | recon/build (2 resume rounds) | recon — bricks landed; cert-shape obstruction FLAGGED (4b′ rec) | ✓✓✓—✓✓ | 291k tok / 86 tools / 22.2 min (+ a weekly-limit cut-off round) | Corrected-hblock spike (2 resume rounds; weekly-limit cut-off after PROBE A). LANDED 3 corrected §(4.33) bricks sorry-free (corner pin `v`). Settled hD/hA as ~1-leaf gate facts ('real depth' dissolved). FLAGGED a deeper cert-SHAPE obstruction: the total-`em`-bijection `fromBlocks` is UNSATISFIABLE for D≥3 (D−2 surplus v-rows break the 0 block + hD); KT (6.64) is a SUBSPACE stmt. Fix = 4b′ row-submatrix reshape of A3/A4 (~2–3 leaves), RECOMMENDED. Model WIN. Coordinator: gate-clean, obstruction sound, scratch deleted. LOOP STOPPED per user; NEXT = 4b′. |
| 474 | (4b′) row-submatrix cert kernel — `rank_ge_of_isUnit_mul_submatrix_fromBlocks` + edge composition core (615abab) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 150k tok / 47 tools / 16.0 min | First (4b′) leaf (session #33, the user-adjudicated A6 direction). 2 mechanical mirrors of A4/A5c-core, `rank_submatrix_le` (no injectivity) for `rank_reindex` — dissolves the §(4.33)(3) cert-shape obstruction at the kernel by dropping the D−2 surplus rows. Coordinator (below-top-rung): full diff read, warning-build + lint re-run clean, axiom-clean; A3's column-submatrix step confirmed as the mirror source on acceptance. NEXT = cert reshape. |
| 475 | reshape cert `case_III_rank_certification_matrix` to the row-submatrix core (6ced25b) | 2/1/1 | opus | normal | clean | ✓✓✓—✓✓ | 135k tok / 43 tools / 10.1 min | Mechanical cert reshape: `em ≃`→`re` injection, `en` flipped, `.reindex`→`.submatrix`, body fires `_of_edge_submatrix_fromBlocks`. Conclusion byte-identical to `_chain` (still a `hrank`-seam drop-in); cert NOT blueprint-pinned (per-slice statement-change gate OK). Coordinator: full diff read, warning-build + lint clean, axiom-clean. NEXT = A6 geometry. |
| 476 | A6 `hblock` 0-block kernel `_submatrix_toBlocks₂₁_eq_zero` (row-submatrix form) (dbe2097) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 199k tok / 48 tools / 13.6 min | Agent independently found+filled the gap the coordinator flagged: the `.reindex`-form 0-block brick can't supply the cert's `re` injection → built the `.submatrix` analog (verbatim mirror) + verified via lean_multi_attempt that it + `fromBlocks_toBlocks` makes `hblock` a one-liner. 3rd consecutive A6-prerequisite commit → coordinator triggers a satisfiability spike on hA/hD next (recurring-deferral + defeq-fragile route-composition). Gates clean (full diff, warning-build, lint, axiom). |
| 477 | A6 arm-assembly satisfiability spike — `hA`/`hD` = 2 new bridges (→ §4.34, read-only) | —/—/— | opus | recon | recon — NEEDS-X (arm composes sorry-free; `hA`/`hD` are 2 genuinely-new dual→matrix-row LI bridges) | — | 200k tok / 50 tools / 10.8 min | Coordinator-triggered before the A6 build (deferred-hyp-satisfiability discipline + 3 consecutive prerequisite commits + defeq-fragile route-composition → spike not blind build). CAUGHT that row-473's "~1-leaf gate facts" `hA`/`hD` are actually 2 NEW bridges: the A5b iff is for the FULL rigidity row, not the operated/`v`-restricted `toBlocks`; `omitTwoExtensor` is extensor-space not `toBlocks₁₁.row`. §38 whnf timed out at 200000 heartbeats — a blind build would have walled. Kernel-read residuals + leaf decomp. Model WIN (flag-don't-force, grounded). → Findings 2026-06-25. |
| 478 | route-A A6 arm spine `case_III_arm_realization_matrix` (8b24b83) | 2/2/1 | opus | build/resume | clean | ✓✓✓—✓✓ | 266k tok / 34 tools / 10.3 min | Spike-salvage build-resume (rescue §6) of row 477: banked the recon's verified `U`/`en`/`hblock` composition as the route-A arm spine, carrying `hA`/`hD` (standing idiom) at their EXACT operated-`toBlocks` shapes — pins the 2 bridges' targets. `_chain` retained (parallel, sound). Coordinator: full diff, shape check (conclusion = `_chain`), warning-build + lint, axiom-clean. NEXT = the 2 bridges. → Findings 2026-06-25. |
| 479 | route-A A6 `hD` bottom-block LI bridge `linearIndependent_toBlocks₂₂_row_of_off_pin` (4b707e2) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 212k tok / 94 tools / 15.2 min | hD bridge (leaf 1) came CLEANER than the §(4.34) Gram plan: KT (6.61)'s op only touches `v`'s coordinate, invisible to `Gv`-rows avoiding `v`, so the operated `toBlocks₂₂` IS the un-operated `R(Gv,q)` submatrix → hD is a submatrix-restriction of the IH row-LI, no rank detour. Reduces the arm's carried hD to `hIH` (dischargeable from the IH at the dispatch). Coordinator: conclusion matches the arm's hD exactly; re-route sound; full diff + warning-build + lint + axiom-clean. Tool-heavy (94) not forced-bloat (4 clean decls + 1 FRICTION). NEXT = hA bridge (§38 whnf guard). |
| 480 | dispatch recon — compiler-checked spike of route-A `chainData_dispatch` interior arm (→ §4.35) | —/—/— | opus | recon | recon — route confirmed (wrap-edge wall escaped); 5-leaf decomp | — | 231k tok / 59 tools / 10.2 min | Coordinator-triggered before any dispatch build: the whole route-A tower feeds the unbuilt `chainData_dispatch` (arm spine has 0 callers) + carried-crux `(re,hbot,hA,hD)` satisfiability exercised here first → spike not blind build (route-B's dispatch walled at GAP 1). Model WIN (flag-don't-force, kernel-probed): route A ESCAPES the wrap-edge wall (e_b corner reads `blockBasisOn` ⇒ member of block A, not span) + CORRECTED the hand-off's "1-line wiring" — landed bridges are dual-space-shaped, leaves 3/4 genuinely-new matrix-shape (P≈3). → §4.35. |
| 481 | leaf-3b cross-hinge spike — mkQ-lift RED HERRING (→ §4.35 corrected) | —/—/— | opus | recon | recon — COMPOSES (existence-form leaf; sorry-free SPIKE 4) | — | 187k tok / 74 tools / 12.1 min | Coordinator-triggered before the leaf-3b build: §(4.35) flagged an unconfirmed quotient→full-LI shape composition (the "re-prove X through landed Y" trigger) → spike not blind build. Model WIN (flag-don't-force, sorry-free SPIKE 4): the mkQ-quotient lift was a RED HERRING — the `hA` leaf's `hLI` is a uniform `blockBasisOn`-family in the full screw dual, so leaf 3b bypasses the quotient via gate→block-incomparability→fresh-`j₀` + `sumElim_candidateRow_iff`. Caught + corrected §(4.35)'s own leaf-3 framing. → Findings 2026-06-25. |
| 482 | dispatch leaf 3b build — `exists_corner_blockBasisOn_linearIndependent` (693448b) | 2/2/1 | opus | resume | clean | ✓✓✓—✓✓ | 261k tok / 77 tools / 28.2 min (resume cumul. incl. #481) | Spike-salvage resume (rescue §6) of #481: built leaf 3b from the sorry-free SPIKE 4, no re-derivation. Existence-form (∃ j₀) per the verdict; leaf 5 consumes the ∃. Coordinator: full diff — genuine crux DISCHARGE not abstraction (the gate→incomparability→fresh-`j₀` chain proves it), new mirror `span_coe_eq` sound + in `Mathlib/` dir, Claim612 import cycle-safe, warning-build + lint + axiom-clean, §(4.35) correction honest (no pinned-clause drop). → Findings 2026-06-25. |
| 483 | leaf-4 bottom-row IH spike — bottom-block deficiency WALL (→ §4.36; USER-ADJUDICATION owed) | —/—/— | opus | recon | recon — WALL / NEEDS-DESIGN (pure-edge bottom unsatisfiable for deficient Gᵥ) | — | 187k tok / 61 tools / 9.7 min | Coordinator-triggered before the leaf-4 build (framework-level + finrank-span→row-LI shape unconfirmed). Model WIN (flag-don't-force, source-grounded): caught a STRUCTURAL WALL the §(4.35) dispatch spike MISSED — route A's pure-`Gᵥ`-edge bottom block `hD`/`hIH` is UNSATISFIABLE for the generic deficient interior split (IH gives `m₂ − k'`, `k'=Gᵥ.deficiency n > 0`; `_chain` fills the gap with candidate ρ'-rows the pure-edge bottom lacks). Coordinator-verified the facts (arm pins only G.def=0; `_chain` `hwmem`; IH deficiency-aware). USER-ADJUDICATION owed. → Findings 2026-06-25. |
| 484 | comparative spike — BOTH §4.36 options WALL (→ §4.37); user-adjudication: new-structure recon vs (C) | —/—/— | opus | recon | recon — both options WALL (verified); recommendation erroneous | — | 262k tok / 35 tools / 7.7 min (resume of #483) | Resume of #483 (leaf-4 agent, context loaded) for the user-requested comparative spike. Coordinator-VERIFIED the core findings (arm CONSUMES `W`; additivity needs `W ≤ span`; no wall-free interior W-producer) → BOTH §4.36 options WALL (reduce to the deficiency-fill span-membership; route A escaped the corner, not the bottom). Model MISS on the FORWARD recommendation: proposed route-4-splitOff, which is CLOSED (row 454) — coordinator caught + discarded it; the core Q1/Q2 verdicts kept. Phase-direction decision owed: new-structure recon vs fallback (C). → Findings 2026-06-25. |
| 485 | scoping pair A (CONSTRUCTIVE) — full matrix route: route A used the WRONG bottom graph (→ §4.38) | —/—/— | opus | recon | recon — wrong-graph found; `Gab` fix; make-or-break = (6.62) | — | 181k tok / 45 tools / 7.4 min | Diverse-lens pair member A (constructive), fresh (avoid anchoring on the comparative spike's "walls"). Read KT §6.4.2 from the primary PDF: KT's eq. 6.64 bottom is the FULL-RANK split-off `Gab`, NOT the deficient `removeVertex` route A used; the d=3 arm already uses `Gab`. Flagged the fix (bottom = `R(Gab)`, fill rows are literal `e₀`-edges) + the one open piece (the (6.62) row-correspondence as a matrix op) + no motive change. Model WIN: reading the primary source for the RIGHT object caught what 3 prior `removeVertex`-framed spikes missed. → Findings 2026-06-25. |
| 486 | scoping pair B (ADVERSARIAL-refute) — full matrix WALLS (but on `removeVertex`; missed `Gab`) (→ §4.38) | —/—/— | opus | recon | recon — refuted the WRONG-graph bottom; conflated e_b/e₀ | — | 126k tok / 34 tools / 5.1 min | Diverse-lens pair member B (adversarial-refute), fresh. Refuted the full matrix route — but its refutation stayed on the `removeVertex`/`R(G)` bottom (the wrong graph) and conflated `e_b` (v-incident CORNER edge) with `e₀` (`Gab` split-off BOTTOM edge at `(a,b)`); it never addressed the `R(Gab)` bottom A proposed. The pair DISAGREED on the label (A: not-closed; B: walls) but CONVERGED on substance (KT's bottom = full-rank `Gab`); the coordinator source-verified the pivotal claim (route A's `Gv` = removeVertex; d=3 uses `Gab`) → A adjudicated correct. → Findings 2026-06-25. |
| 487 | (6.62) row-correspondence spike — operated `e_a` is ZERO off-`v` (project op); op-faithfulness OPEN (→ §4.39) | —/—/— | opus | recon | recon — `e_a→e₀` FAILS in the project op frame (kernel); fork OPEN | — | 216k tok / 28 tools / 5.6 min (resume of #485) | Resume of #485 (Lens A) for the §4.38 make-or-break. Built 4 kernel-clean theorems: the operated `e_a` row is identically 0 off-`v` under the project's `columnOp` (vacuums `e_a` into the corner), so `e_a→e₀` FAILS in THAT op frame; bottom = deficient `R(Gv)`; coordinator-verified. NOT final — the spike tested only the project's op frame (the constructive lens's own "walls"); OPEN fork: is the project's `columnOp` the wrong DIRECTION vs KT's (6.61) (artifact, fixable) or does (6.62) genuinely fail (concrete KT issue)? Next = a primary-source op-faithfulness recon. → §4.39. |
| 488 | fork-decider — FORK 1 (route figured out): KT sound, op faithful, `hbot` excluded e_b; fix = R(Gab) bottom (→ §4.40) | —/—/— | opus | recon | recon — FORK 1: route figured out (kernel-grounded + coordinator-corroborated) | — | 257k tok / 26 tools / 6.7 min (resume of #487) | Resume of #487 (Lens A); coordinator independently read KT (6.61)/(6.62) in parallel; both converge FORK 1: KT's proof SOUND, the op IS KT's (6.61) (`col_a += col_v`), and the §(4.39) "walls" tested the WRONG edge (`e_a` = the corner edge, correctly 0 off-`v`). KT routes `e_b` to the `e₀` bottom; kernel-proved (7 thms) the operated `e_b` row off-`v` = `R(Gab)`'s `ab` row, NO span membership. Artifact = `hbot` excluding the `v`-incident `e_b` row. Route figured out (~4–6 commit `R(Gab)`-bottom reshape, corner leaves reused, no motive change). → §4.40, Findings. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **2026-06-25 (rows 487–488) — a 5-spike "walls" chain was RESOLVED to FORK 1 (route figured out, KT's
  proof sound) by the coordinator reading the PRIMARY SOURCE directly + the fork-decider testing the RIGHT
  object; the shared error was a WRONG-EDGE assumption.** Five spikes over the bottom block (§4.35 dispatch,
  leaf-4, comparative, the diverse-lens pair, the (6.62) spike) all concluded the route walls — because they
  shared an unexamined assumption: that the `e₀` deficiency-fill must be off-`v` from the start, so the
  `v`-incident edges are excluded from the bottom (`hbot`), and the §(4.39) spike tested `e_a` (which IS the
  corner edge). The coordinator's independent read of KT's verbatim (6.61)/(6.62) showed the op is faithful
  and KT routes the OTHER `v`-incident edge `e_b` to the `e₀` bottom (it is `v`-incident PRE-op,
  off-`v`-supported only AFTER the column op); the fork-decider then kernel-proved (7 thms) the operated
  `e_b` row off-`v` = `R(Gab)`'s `ab` row. The wall was a formalization artifact (`hbot` excluding `e_b`),
  not a KT-proof issue. **Lessons:** (1) when a multi-spike chain repeatedly walls, the coordinator reading
  the PRIMARY SOURCE directly (the exact op/correspondence equations) can break a shared-assumption loop the
  agent chain cannot — the agents inherited each other's framing; the paper is the ground truth. (2) A
  "walls" verdict that tests ONE object (`e_a`) does NOT refute the route until the RIGHT object (`e_b`) is
  tested — pin which object KT's argument actually uses BEFORE accepting a per-object impossibility. (3) The
  coordinator's own intermediate hypothesis ("wrong op DIRECTION", §4.39) was also wrong — the op was right,
  the row SELECTION was the bug; running the fork-decider + the parallel source-read corrected both the agent
  chain AND the coordinator. Extends the rows-485–486 wrong-graph lesson (this is the wrong-EDGE within the
  right graph). → DESIGN.md *Constructibility recon* (the primary-source-read corollary).
- **2026-06-25 (rows 485–486) — a diverse-lens recon PAIR caught a WRONG-GRAPH diagnosis that three
  prior single-pass spikes (all framed on the same wrong object) missed; the constructive lens reading
  the PRIMARY SOURCE for the RIGHT object was decisive.** Three spikes (the §4.35 dispatch decomposition,
  the leaf-4 spike, the comparative spike) all concluded the route-A bottom block walls — but all three
  silently assumed the bottom graph was `Gv = G.removeVertex v` (deficient by `k' > 0`). The constructive
  pair member read KT §6.4.2 from the primary PDF and found KT's eq. 6.64 bottom block is the FULL-RANK
  split-off `Gab = G.splitOff …` (zero deficiency) — and the landed d=3 arm already uses `Gab`. So the
  "wall" is a wrong-graph artifact: on `R(Gab)`, the deficiency-fill rows are literal `e₀`-edge rows, not
  span members. The adversarial member returned "WALLS" but its refutation stayed on `removeVertex` (it
  conflated `e_b`, the v-incident corner edge, with `e₀`, the `Gab` split-off bottom edge) — so the pair
  DISAGREED on the label yet CONVERGED on the substance (KT's bottom = full-rank `Gab`), and the
  coordinator's source-verify of the pivotal claim (route A's `Gv` is `removeVertex`; d=3 uses `Gab`)
  adjudicated A correct. **Lessons:** (1) when several single-pass spikes agree a route walls, check
  whether they share an unexamined OBJECT assumption (here the bottom graph) before accepting "intrinsic
  wall" — a wrong shared premise makes N agreeing spikes worth ~1. (2) The diverse-lens pair's value here
  was not the disagreement per se but that the CONSTRUCTIVE lens was told to read the primary source and
  BUILD the route, forcing it to identify the right object; the adversarial lens, refuting the existing
  (wrong-object) framing, reproduced the shared error. Pair a "refute the current framing" lens with a
  "build it from the source" lens, not two refutations. (3) Coordinator source-verification of the ONE
  pivotal claim (which graph?) resolved a 3-spike-deep confusion in two greps. → DESIGN.md
  *Constructibility recon* + *Diverse-lens recon pair*.
- **2026-06-25 (row 483) — the architecture-shape satisfiability trap recurred at the BOTTOM block,
  caught by the per-leaf trace AFTER two prior recons passed it; per-leaf recon claims need independent
  satisfiability checks in BOTH directions (over- and under-estimate).** The route-A arm carried `hD` as
  the row-LI of a *pure `Gᵥ`-edge submatrix* — a SHAPE that is unsatisfiable whenever `Gᵥ = G−v` is
  deficient (`k' = Gᵥ.deficiency n > 0`, the generic interior degree-2 split), because the IH gives only
  `m₂ − k'` independent `Gᵥ`-rows and `_chain` fills the `k'` gap with candidate `ρ'`-rows the pure-edge
  bottom has no slot for. This survived the A6 satisfiability spike (row 477, "arm composes sorry-free" —
  but it never traced `hD`'s satisfiability against the IH's *deficiency*) AND the §(4.35) dispatch spike
  (which decomposed leaf 4 as "from the IH build `re∘Sum.inr`", assuming a pure-edge bottom). Only the
  per-leaf leaf-4 spike, reading the IH's actual deficiency-aware finrank, hit it. **Lessons:** (1) the
  "Sharper still²" SHAPE-satisfiability discipline (rows 457–473) must be run against the real object's
  *dimensions* at EVERY carried hypothesis, including the ones a composition spike "passes" by carrying
  them un-exercised — a sorry-free arm composition certifies the *wiring*, not the carried hyps'
  satisfiability. (2) The same dispatch spike's per-leaf characterizations erred in BOTH directions in one
  session — leaf 3's mkQ-lift was OVER-pessimistic (red herring), leaf 4's pure-edge bottom was
  UNDER-pessimistic (missed wall); a per-leaf recon-before-build catches both, and is cheap vs a built
  dead leaf. (3) The fix is an architecture-shape decision (augmented matrix bottom vs hybrid
  matrix-corner + `_chain` span bottom), user-adjudicated like §(4.33)→(4b′); the landed corner leaves
  (1,2,3) stay sound + reusable under either. → DESIGN.md *Constructibility recon* (the architecture-shape
  corollary). **(4) [row 484] the comparative spike that priced those two options then found BOTH WALL
  (no landed wall-free interior `W`-producer; the deficiency-fill reduces to the same span-membership wall
  that closed the base-block family) — so route A escaped the CORNER wall but not the BOTTOM. Its core
  kernel findings verified, but its FORWARD recommendation (route-4-splitOff) named a route landed history
  records as CLOSED (row 454): a recon reliable on its kernel findings can still err on its recommendation
  — verify a recon's *recommendation* against the landed wall-history, not just its findings. The honest
  decision is now new-structure recon vs fallback (C), §(4.37).**
- **2026-06-25 (rows 480–482) — a dispatch-level recon's own shape-flag can itself be a RED HERRING;
  the per-leaf spike reading the *consumer's actual type* (not the recon's prose) is what caught it.**
  The §(4.35) dispatch spike correctly decomposed `chainData_dispatch` into 5 leaves and confirmed the
  make-or-break (route A escapes the wrap-edge wall, kernel-probed) — but its leaf-3 framing carried a
  WRONG flag: "the corner `hLI` needs lifting the landed `mkQ`-quotient gate-LI to the full screw dual
  (quotient-LI doesn't lift)." The coordinator (rightly, per the "re-prove X through landed Y, shape
  unconfirmed" trigger) spiked leaf 3b before building rather than trusting the flag. The leaf-3b spike
  then read the landed `hA` leaf's ACTUAL `hLI` type — a *uniform `blockBasisOn`-family in the full
  screw dual*, with NO `mkQ`/quotient/Lemma-2.1 object — so the lift was a non-issue: leaf 3b composes
  directly (gate→block-incomparability→fresh-`j₀` + `sumElim_candidateRow_iff` + leaf 3a), sorry-free.
  **Lessons:** (1) a recon that decomposes a core is fallible *per-leaf* even when its top-level verdict
  (the wall-escape) is sound + kernel-probed; treat each leaf's "needs bridge X" flag as itself a
  recon claim to verify against the *consumer's landed type*, not to build on. (2) The cheapest audit of
  a "landed Y is the wrong shape, needs a lift" flag is to spike the consumer's actual hypothesis type
  — here it dissolved the flag in one read. (3) The spike-then-salvage-resume (rescue §6) banked the
  sorry-free SPIKE 4 into the build with zero re-derivation.
- **2026-06-24 (row 454) — the wrap-edge wall is INTRINSIC to the `caseIIICandidate` slot-override
  (the discriminator gate), invariant under any base-block re-targeting; "Q1-clean-while-Q2-walls" was the
  precise diagnostic.** Verifying route 4-splitOff (verify-first, user-chosen) split cleanly: Q1 (the
  splitOff↔splitOff relabel rank-iso at the non-involutive cycle) is WALL-FREE and sorry-free — the relabel/
  rank machinery generalizes fine (the `d=3` involution facts were artifacts, not load-bearing) — but Q2 (the
  fresh `e₀'` short-circuit row entering the candidate span) WALLS by the SAME discriminator-gate condition
  `ρ₀ ⊥̸ C(vᵢ₊₁, n')` that blocked routes A/B/4-bare. That gate is *what makes the `±r` corner the independent
  `D`-th row*, so it re-surfaces wherever the wrap-edge content tries to enter the candidate span, regardless
  of how the base block `W` is chosen (4th appearance). **Lessons:** (1) when a wall recurs across structurally
  different fixes, suspect it is intrinsic to a shared downstream object (here the candidate's slot-override),
  not to the varied upstream choice — and verify THAT before the next re-targeting (this verify-first spike
  cost ~1 recon and closed the whole base-block family, vs. building a 3rd dead route). (2) Splitting a verify
  into independent sub-questions (Q1 rank / Q2 containment / Q3 cert) localizes the wall precisely: Q1 clean +
  Q2 walls told us the obstacle is one layer above the seed, not the relabel. (3) The genuine-row base-block
  rank-cert reconsideration is now CLOSED to all routes in hand; the honest unconditional theorem needs route
  A (concrete `Matrix`, the wrap row a literal row not a span member), else honest-conditional (C).
- **2026-06-24 (rows 451→453) — a scoping recon's "generalize the landed lemma" can hide a
  FRAMEWORK-FORM mismatch (splitOff vs bare), and a fresh make-or-break build caught what the coordinator's
  acceptance did not.** §(4.27) scoped route 4 as wall-free with `hseedrank` "from the relabel rank-iso,
  generalizing the `d=3` `rigidityRows_ofNormals_relabel`". The coordinator scrutinized + accepted it — but
  did NOT read that landed lemma's ACTUAL form (it is stated for SPLITOFF frameworks, where a fresh
  short-circuit edge absorbs the wrap-edge image), so the bare-seed `hseedrank` the recon asserted is in fact
  FALSE. The fresh LEAF-1 build (recon-before-building) caught it kernel-checked, contradicting §(4.27).
  **Lessons:** (1) when a recon says a residual "follows from a generalization of landed lemma X", READ X's
  actual statement (framework form + hypotheses) and confirm the residual's object matches — the 3-clause
  "verify against the landed source" applies to the COORDINATOR's acceptance of a recon verdict, not only to
  the agent writing it. (2) Conflicting agent verdicts on a kernel-checkable fact are resolved by READING the
  cited landed lemma, never by trusting the more recent/confident agent (here the LEAF-1 build was right).
  (3) The wrap-edge wall has now blocked THREE base-block routes (option-A `hρGv`, route-B `hS`,
  route-4-bare `hseedrank`) — it is fundamentally a CORNER/splitOff object; any route that puts it in the
  bottom block `W` walls. A strong signal toward the splitOff variant or the honest-conditional (C).
- **2026-06-24 (rows 449–450) — the deferred-hypothesis-unsat trap recurs at COMPOSITION, and a
  4-leaf + cost-outlier pattern is its tell.** Route B's LEAF-B2 individual-row `hS` re-introduced the
  member-mapping wall §(4.18)–(4.24) it was meant to escape: the wrap-edge `edge i` row is the independent
  `±r` corner row (option A transports it only as a GROUP), not a base-block row, so demanding each genuine
  basis row transport *individually* into the candidate span is unsatisfiable. The row-443 "residual risk
  RESOLVED" was a **coordinator over-claim**: I verified the `hS` router type-checks + that its `hG_eb_cand`
  is a combinatorial `G.IsLink` (not `hρGv`), but NOT that `hG_eb_cand` is SATISFIABLE for *every* consumer
  row — the `Or.inl`-feed framing hid that the wrap-edge rows go through `Or.inr` (the block tag), whose
  premise is provably false. **Lessons:** (1) a deferred-hypothesis leaf's satisfiability must be traced for
  ALL consumer rows incl. edge cases (the wrap edge), never just the happy path the `Or.inl` framing
  suggests — exactly DESIGN.md *Constructibility recon*, the satisfiability corollary, recurring a 3rd time
  this phase (rows 392/394, 435, now 443→449). (2) The 4-consecutive-leaf + cost-outlier signal (a 30.8-min
  accessor) correctly triggered the recon that caught it BEFORE a forced multi-hour build — the spike cost
  ~1 recon. The early-recon discipline (trigger at the 2-leaf floor, watch cost outliers) paid off; do not
  let a string of clean-landing plumbing leaves lull the coordinator past the unbuilt-core trigger.
- **2026-06-24 (rows 435–436) — the A1 §I.8.21(α) dissolution-recon episode (the value of
  construct-or-concede on a fragile-zone dissolution).** A compiler-checked SPIKE answers a
  route-COMPOSITION question ("do these objects compose to goal X?"), NOT a dischargeability one. The A1
  spike built a type-checking composition of the landed static-`W` cert + corner-assembly with the corner
  data (`W`/`hWS`/`hG_eb_cand`/`hvanish`) carried as HYPOTHESES, reported a single (spine-deficiency)
  residual, and returned **FEASIBLE** — but it never discharged those hypotheses, which two PRIOR kernel
  spikes (§(4.17)/(4.18)) had already proved unsatisfiable for the real consumer. Four tells let the
  coordinator catch it without a build: (a) the verdict DISSOLVED the phase's central wall (the
  highest-scrutiny trigger); (b) it contradicted a same-day STOP + primary-source recon; (c) it re-pointed
  at the exact decls those prior spikes killed; (d) it answered the wrong deliverable (the existing
  static-`W` cert, not the *new* §I.8.21(α) matrix-level infra A1 asked about). The decisive settle was a
  **construct-or-concede resume of the SAME spike** (SendMessage to its agentId, context + read phase
  intact, 9 tools / 3.3 min — far cheaper than a fresh refute agent): *produce the actual object at the
  kernel, or concede*. It conceded, re-deriving §(4.17)/(4.18) as two sorry-free `concede_*` theorems for
  the real dispatch slot. **Lesson:** for a dissolution verdict in a fragile zone, the cheapest decisive
  audit is to resume the same spike armed with the prior kernel-impossibilities and force
  construct-or-concede; a "single residual" from a composition spike is NOT evidence of dischargeability
  when the crux is carried as a hypothesis. (The satisfiability corollary is already in DESIGN.md
  *Constructibility recon*; this episode adds the construct-or-concede resume as its audit instrument.)

- **2026-06-24 (row 437) — the matrix-level rework recon (when a wall is genuinely intrinsic, and when to
  STOP reconning it).** After the A1 episode, the coordinator read KT §6.4.2 (eqs. 6.60–6.67) from the
  primary PDF and hypothesized the wall might be an ARTIFACT of the project's span-membership formalization —
  since KT certifies the rank by rank-preserving COLUMN+ROW operations, not membership. The user authorized
  "reworking landed material" to test it. A read-only design+spike DISPROVED the hypothesis at the kernel:
  KT's row operation `r̂ = Σλ rⱼ` IS the `G_v`-row part `wGv ∈ span(R(G_v,q))` — and the project's OWN
  Phase-22g code (`exists_redundant_panelRow_ab_decomposition`, the `r̂ = wGv` docstring) already encoded
  that equivalence. The "scissors": the pure-`vᵢ` corner satisfies the block separator's `htopvanish` but
  needs `hρGv` to enter the candidate span; the `hρe₀`-sourced corner enters the span but isn't pure-`vᵢ`;
  the two differ by exactly the wall row. This was the FOURTH independent kernel confirmation of the wall
  (§(4.18)/(4.20)/(4.21)/(4.23)) + the A1 concede. **Lessons:** (1) when a build-blocking wall has survived
  2–3 independent kernel refutations, one MORE carefully-aimed *orthogonal* recon (here: "is KT's
  row-operation framing genuinely different from the span membership?") is still worth it — it converts "we
  suspect intrinsic" into "kernel-confirmed intrinsic, the rework hypothesis is dead," which is exactly what
  lets a coordinator commit to the honest-conditional path without nagging doubt (and what justifies the
  cost to a user weighing a rework). (2) But after that, STOP: further swings need a genuinely-NEW
  mathematical idea, not another formalization angle. (3) The codebase's own docstrings can carry the
  decisive primary-source equivalence — read them (clause i) before betting a rework escapes.

- **2026-06-24 (row 438) — the geometry-aware-transport scoping recon (distinguishing "missing abstraction"
  from "linear-level impossibility", and the value of scoping a user's idea even when it fails).** After the
  coordinator+user diagnosed the wall as the transport "remembering only the vertex permutation σ, not the
  geometry," the user proposed a geometry-aware transport and asked to scope the effort. The recon found two
  things worth more than a yes/no: (1) the diagnosis was imprecise — the project's transport is ALREADY
  geometry-aware (`shiftPerm` IS KT's `ρᵢ`, `qρ` IS the config relation, and `rigidityRow_relabel_to_genuine`
  already absorbs KT's per-edge reproduction (6.59) as an abstract `hsupp` hypothesis — the exact "absorb the
  entrywise grind into an abstraction" the user hoped for; it works for genuine rows). (2) The redundant row
  is closed not by a missing abstraction but by a LINEARITY IMPOSSIBILITY: for any linear `T`,
  `T(Σcⱼ·gⱼ) = Σcⱼ·T(gⱼ)`, so decomposing the redundancy into genuine rows and transporting each can't change
  where `T` lands the redundant row — it goes to its `ρᵢ`-image (the moved member), never the fixed `hφ`.
  **Lessons:** (1) scoping a user's idea is worth it even when the verdict is negative — the recon converted
  "the transport is missing geometry" (wrong, would have motivated a doomed rework) into "the transport is
  correct; the obstruction is a linearity impossibility on the dual span" (right, and identifies the ONLY
  escape: a non-linear / explicit-`Matrix` object). (2) Distinguish "we need a better abstraction" from "this
  is impossible for the whole class of objects we're using" — a one-line linearity argument settled the
  latter where four prior spikes had only refuted specific instances. (3) Read what's already built before
  proposing to build it (clause i): the geometry-aware transport the rework targeted was already in tree.

- **2026-06-24 (row 439) — route B: the re-architecture escape after 5 wall-confirmations (when "intrinsic"
  is intrinsic only to the CURRENT architecture).** The five prior kernel confirmations all proved the wall
  for the project's *existing* rank-cert architecture (which builds the base block `W` from the full
  relabelled bottom family, forcing the redundant row into `W`). A user-directed faithful-re-architecture
  pass (the user's insistence: "we cannot skip key steps; if KT's proof is valid, that gives us a route")
  found the escape — and it was KT's own block structure (6.64): delete the redundant row from the bottom
  block, put its reproduction in the CORNER. B-WORKS was reached WITH the session's hard-won discipline
  intact: the recon CONSTRUCTED the previously-"impossible" satisfiability facts (Q2-B/C/D, axiom-clean)
  rather than carrying them, and honestly flagged the ONE remaining carried hypothesis (LEAF-B1) as the
  crux/risk — explicitly naming it the structural twin of this session's two earlier carried-hypothesis false
  FEASIBLEs. **Lessons:** (1) "intrinsic to KT, 5× confirmed" can still mean "intrinsic to the current
  ABSTRACTION" — a faithful re-architecture (follow the paper's actual block structure rather than patch the
  existing cert) is a distinct move from "find a missed route," worth attempting when the user values
  faithfulness over a conditional shortcut. (2) A long string of negative recons is not wasted: each
  sharpened *why* the wall held (redundant→`W`), and that diagnosis is exactly what told the positive recon
  where to invert. (3) The discipline that caught the two false FEASIBLEs (construct-don't-carry; flag the
  carried hypothesis) is what makes a *positive* verdict trustworthy — the same test that killed the bad ones
  validated the good one and isolated its single remaining risk (LEAF-B1).

- **2026-06-25 (rows 457–473, session #32) — opus's spike/recon-first discipline caught FOUR
  architecture gaps before any dead build; the resume-drive cleared over-slicing.** Across route A's
  rank-cert build (~13 leaves + 3 recons/spikes), the recons each caught a gap gate-clean builds would
  have propagated: the A5 product-matrix re-route (flat `finBasis` columns don't factor `α×Fin D`), the
  A4.5e total-`β` capstone unsatisfiability, the §(4.32) `v`-vs-`a` corner-pin garble (→ a ZERO corner
  block), and the cert-SHAPE obstruction (total-`em` `fromBlocks` unsatisfiable for `D≥3`). **Lessons:**
  (1) spike-not-prose + flag-don't-force kept catching architecture errors many leaves before assembly —
  a BLOCKED-with-diagnosis is the high-value outcome, not a failed dispatch. (2) When consecutive FRESH
  build agents repeatedly micro-shrink one layer (each paying full context-read overhead), a
  **resume-drive** (SendMessage-resume a warm agent scoped to the larger chunk) clears it — worked twice
  (A5c→cert; corrected-hblock→bricks). (3) The deferred-hypothesis-unsat trap recurs at the cert
  SHAPE/architecture, not just leaf hypotheses → DESIGN.md *Constructibility recon* (the architecture-shape
  satisfiability corollary). Full route history: `notes/Phase23-design.md` §(4.31)–(4.33).

- **2026-06-25 (rows 477–478, session #33) — the A6 arm-assembly satisfiability spike caught a
  `~1-leaf`→`2-bridge` underestimate before a blind build hit a whnf wall.** Before building the A6
  geometry, a read-only compiler-checked spike traced `hA`/`hD` against the REAL arm objects and found
  the row-473 verdict ("`hA`/`hD` are ~1-leaf gate facts via the A5b iff / `omitTwoExtensor` / IH")
  was OPTIMISTIC: the A5b iff is for the FULL `rigidityProd.row`, not the column-operated, row-injected,
  `v`-column-projected `toBlocks`; `omitTwoExtensor` LI lives in extensor space, not `toBlocks₁₁.row`.
  Both need a genuinely-new dual→matrix-row LI bridge; a naive `whnf` on the `caseIIICandidate` carrier
  timed out at 200000 heartbeats (§38), so a blind build would have walled mid-proof. The spike then
  salvage-resumed (read-only lifted) to bank its verified `U`/`en`/`hblock` composition as the arm
  spine, carrying `hA`/`hD`. **Lessons:** (1) the deferred-hyp-satisfiability trap recurs at the
  ARM-ASSEMBLY consumer, not only leaf hypotheses — a carried gate fact rated "~1-leaf via landed
  lemma X" must have its *bridge* confirmed to exist (X's conclusion shape vs the carried fact's exact
  object), not just X landed; rating it from the prior spike's prose was the miss the new spike caught.
  (2) For a route-composition crux in the defeq-fragile zone, spike-before-build beats build-then-BLOCK
  even when prior recon "settled" it — the settling was at the wrong granularity. → DESIGN.md
  *Constructibility recon* (the satisfiability corollary, now also at the consumer-assembly level).

