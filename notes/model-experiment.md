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
  codes-until-open). 22k/22l + the post-22l perf round closed 2026-06-16;
  23a/CARRIER Lean closed 2026-06-16 (row 190); 23b/CHAIN closed 2026-06-21
  (CHAIN bricks landed, the `hρGv`-seam characterized as a hard core); 23c closed
  2026-06-24 (option (A) built + the interior-`hρe₀` crux closed, but the general-`d`
  rank cert hit the member-mapping wall — a phase STOP); the open sub-phase is **23d**
  (`notes/Phase23d.md` — the rank-certification reconsideration; next = the A1
  §I.8.21(α) feasibility recon). Continues into successor phases until concluded.
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
  would re-probe. Set/re-confirmed sessions #6–#32 (latest: **#32**, 2026-06-24,
  fresh `/coordinate-phase`; user re-confirmed the triple [Standard triple] at
  session start; opus reachable via the Agent `model` param, no substitution
  needed). **The override expires session-end — a fresh coordinator re-runs the
  session-start availability check + re-confirms the triple.** **The active
  sub-phase is 23d; the genuine-row base-block family (routes B/4-bare/4-splitOff)
  is CLOSED at the wrap-edge wall** (4 appearances, §(4.18)–(4.29)); the user chose
  **route A** (the honest unconditional concrete-`Matrix` Thm 5.5). A1+A2 LANDED + the
  opacity de-risk PASSED (row 456, `Concrete.lean`). **Next dispatch = A3** (the matrix
  block-additivity-as-inequality lemma — the genuinely-new piece; `notes/Phase23d.md`
  *Hand-off*), then A4→A5→A6, then ENTRY + ASSEMBLY. ALL landed leaves (incl. the
  route-B/4 inventory) stay in tree (sound in isolation, reusable/harmless).
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

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

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

