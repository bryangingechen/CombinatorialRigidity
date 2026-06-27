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
grandfathered **rows 1–189**, the **Phase 23a–23e rows 190–514** (with their
session-close config notes + *Findings*), and the **closed-phase *Findings***
(Phase 22h–22l + post-22j perf). This live file keeps only the config, the
**active sub-phase's** rows (currently **23f**, no rows yet), and active-phase
*Findings*, so the coordinator's every-dispatch read stays small. **When a
(sub-)phase closes, move its rows + its *Findings* close-out + its session-close
config bullet here** in the same close-out cleanup — a project phase-close
checklist item (`PHASE-BOUNDARIES.md` *When this commit closes a phase*); 23b
closed 2026-06-21 without it and the rows went stale (cleaned up 2026-06-22).

## Repo-local config

- **Testbed:** the molecular program — **Phase 23** (Case III general `d`:
  KT Lemma 6.13 → Thm 5.5 → Thm 5.6 → Conjecture 1.2; sub-lettered,
  codes-until-open). Open sub-phase = **23f** (`notes/Phase23f.md`). Closed
  sub-phases (22k–23e) + the phase status / next-step live in the ROADMAP cell +
  `notes/Phase23f.md` *Hand-off*, **not here**. Continues into successor phases
  until concluded.
- **Rungs:** haiku → sonnet → opus → fable (the Agent tool's `model` param).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md` model-tier
  step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase23f.md` *Hand-off* (the active sub-phase)
  + the recon `notes/Phase23-design.md` §(4.54) = the geometry-arm hand-off (the
  cert-route arc §(4.48)–(4.54) is closed/archived with 23e);
  the general-`d` reuse map is §1.33(C) of `notes/Phase22-realization-design.md`.
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
  fixups (wrong branch / author / trailer) **pre-authorized**. Availability under
  OPUS-ONLY: only **opus** is probed (the coordinator runs on it, reachable via the
  Agent `model` param); a fresh coordinator reverting to the S/P/B map would re-probe
  the other rungs. **The override expires session-end — a fresh coordinator re-runs
  the session-start availability check + re-confirms the triple.** Last re-confirmed
  **session #43** (2026-06-27, fresh `/coordinate-phase` loop; availability check:
  **opus** reachable via the Agent `model` param, OPUS-ONLY so only opus probed; build
  sanity check green on the CaseIII chain (ForkedArm, 2783 jobs); Standard triple
  re-confirmed by the user). Session #43 starts the **route-(α) decomposition design-pass**
  per `notes/Phase23f.md` + design §(4.65.E). Session #42 (2026-06-26, rows 532–537)
  ended on the **user route decision: route (α) chosen** — re-shape the `_zero₁₂` `±r`
  row to read the genuine `hingeRow a b ρ₀` (KT eq. 6.66) instead of the opaque-basis
  `(e_b, j₀)` index; en route it landed HD (`b41b99a`) + D1 (`8507ac4`) + D2 (`8e03871`),
  caught+reverted the MIS-TARGETED HA `C=0` build (§(4.62)), and the D3/D4 build BLOCKED
  on the `hred` crux → recon §(4.65) refuted it (`blockBasisOn` opaque). Prior **sessions
  #39–#41** (2026-06-26) ran rows 515–531 — the geometry-arm matrix-backbone leaves
  (i)–(iv) + B1/B2 + the §(4.55) `re`-shape recon, then the §(4.56) wrapper-decomposition
  spike (row 521) and the RE strict-injection sub-arc (RE corner half → BOT-1..BOT-4,
  rows 522–531). The full sessions-#36–#38 history + the strategic
  adjudications (pursue the cert §(4.48); cert-shape route (A) §(4.53); close 23e
  §(4.54)) are archived in the 23e config close-out. (Session #36's `hIH` C.3
  adjudication stands — lands with 23f.)
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
Rows 1–514 are in [`model-experiment-archive.md`](model-experiment-archive.md)
(1–189 grandfathered; 190–372 = Phase 23a + 23b; 373–434 = Phase 23c; 435–501 = Phase 23d;
502–514 = Phase 23e). This live table holds only the **active sub-phase (23f)** rows.

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 515 | 23f leaf (i) `cGv`→`w` re-key (`0093ad1`) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 151k tok / 56 tools / 16.4 min | Opus clean first pass on a P=2 named-route build (`of_eq_mul_of_row_comb` + `sum_fiberwise`), no escalation. Builder abstracted the leaf carrier-agnostic, deferring the `μ`/membership arm-coupling to the assembly — a clean slice, re-flagged in the leaf-(i) residual + Current state (verified not silently dropped). Blueprint — = leaf-level infra, no node. Coordinator re-ran below-top-rung gates: build warning-clean, full `lake lint` passed, sorry-grep clean. |
| 516 | 23f leaf (ii) `Lrow`-on-`p` reindex unit-det bridge (`2e2ab1a`) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 155k tok / 104 tools / 27.2 min | Opus clean first pass on the pinned genuinely-new bridge (`reindex` + `det_reindex_self` + landed `rowOp_isUnit_det`); 4-line proof, no escalation. Lean-quality positive: `[Finite m₁/m₂]` + `Fintype.ofFinite` dodges both the `unusedFintypeInType` linter and a non-canonical `Fintype (m₁⊕m₂)` defeq clash with `rowOp_isUnit_det`'s `instFintypeSum`. Blueprint — = leaf-level infra. Coordinator re-ran below-top-rung gates clean (build warning-clean, full lint, sorry-grep). |
| 517 | 23f leaf (iii) post-row-op corner-`hA` bridge (`ec2cdae`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 132k tok / 54 tools / 15.3 min | Opus clean first pass on the P=3 genuinely-new leaf; closer is a 4-line proof (`linearIndependent_row_of_coordEquiv` + `corner_hA'_of_gate`.comp), the mutation crux (`blockBasisOn(e_b,j₀)→ρ₀`) abstracted to the assembly as hypothesis `hAeq` — sanctioned by §(4.54), re-flagged in the leaf-(iii) residual + assembly item. Builder self-fixed 3 doc long-line warnings pre-commit (warning-clean). Blueprint — = leaf-level infra. Coordinator re-ran below-top-rung gates clean (full build, lint, sorry-grep). |
| 518 | 23f `hblock` reducer matrix backbone (`6bf40c0`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 187k tok / 77 tools / 30.5 min | Dispatched the assembly (rated 2/3/1); opus shrank it to a complete matrix-backbone sub-step (`reindex_rowOp_submatrix_eq_fromBlocks_zero₁₂`) — scope-to-fit worked, no degraded mega-commit; clean axiom-clean generic lemma. Consumer-fitness flag (coordinator, → Findings 2026-06-26): the backbone's proof REQUIRES `e` a bijection (`submatrix_mul_equiv`), but leaf-(ii)/design say the arm's `re` is a strict injection dropping the D−2 surplus rows — unreconciled. Coordinator fixed the hand-off contradiction + reframed the wrapper recon-first. Gates re-run clean. |
| 519 | 23f `re`-shape recon → §(4.55) verdict (`40c803a`) | 3/2/1 | opus | recon | clean | ✓✓——✓✓ | 290k tok / 119 tools / 23.3 min | Resolved row-518's consumer-fitness flag: verdict (b) STRICT INJECTION — a phase re-route (leaves (ii)/(iv) bijection-only, don't serve; B1/B2 owed). Opus recon, compiler-checked (4 scratch spikes, reverted). Coordinator-acceptance win: verified the load-bearing claims from SOURCE not prose — `card m₂` PINNED by cert hm₂ ⟹ option (a) structurally impossible; relation `≤` not `=`; the general-fn `re:m₁⊕m₂→p` sig + cert's own L2492 "injection drops D−2 surplus" comment. Cost high (290k/119) = a thorough read-and-spike recon, in-band for a re-route. |
| 520 | 23f geometry leaves B1/B2 strict-injection backbone (`dfdcbeb`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 174k tok / 77 tools / 15.0 min | Opus landed BOTH B1+B2 in one commit on the pinned §(4.55) strict-injection route, clean first pass. Coordinator shape-check: B2's conclusion = the cert's `hblock` operated-corner shape; B1 exports the off-image-vanishing fact B2 needs + drops the redundant rank-invariance (from `IsUnit det`) — sound refinement of the §(4.55) sketch. Supersession check: (ii)/(iv) now zero-caller orphans (soft phase-close cleanup, NOT a deletion-mandate violation — §(4.55) keeps them as the bijection special case). Below-top-rung gates re-run clean (build warning-clean, lint, sorry-grep, axiom-clean). |
| 521 | 23f cert-firing wrapper decomposition spike + banked skeleton (`5cd6db8`) | 3/2/1 | opus | recon | clean | ✓✓✓—✓✓ | 287k tok / 114 tools / 20.8 min | Compiler-checked decomposition spike (bank-don't-revert): kernel-confirmed the cert FIRING composes sorry-free → BANKED the wrapper skeleton `case_III_arm_realization_rowOp` (axiom-clean) + §(4.56) decomposing the 5 owed sub-leaves (RE/HMEQ/HB/HA/HD) with exact sigs. Coordinator re-verified the firing vs landed B1/B2/leaf-(iii): cert `A` slot = OPERATED `A−L₀C`, `mul_assoc` bridge, defeq seam `rfl`-bridgeable. RE (strict `re`, no in-tree precedent) honestly FLAGGED make-or-break — its satisfiability deferred to the next leaf, not yet built. |
| 522 | 23f sub-leaf RE corner half (`460c0e3`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 185k tok / 71 tools / 13.0 min | Build for sub-leaf RE; opus self-shrank (scope-to-fit) to the carrier-agnostic CORNER half (`cornerRowInjection` + injectivity via `sumElim`, axiom-FREE; `finScrewDimSplitCorner`) — complete + clean, matches §(4.56) RE corner spec. DISCOVERY (experiment signal): the RE BOTTOM half is W6b-coupled — the producer returns the `w`-rows as DUAL FUNCTIONALS, not `(e,j)`-indexed into `p`, so a realize-as-`p`-rows bridge is unbuilt; §(4.56) under-specified this, next leaf is research-shaped. Coordinator re-verified warning-clean/lint/axiom-free. |
| 523 | 23f RE bottom-half recon → §(4.57) sub-arc + W6b correction (`915356f`) | 3/2/1 | opus | recon | clean | ✓✓——✓✓ | 238k tok / 74 tools / 12.2 min | Compiler-checked recon (2 probes) of the RE bottom half. OVERTURNED row 522's build-agent scope-shrink diagnosis: PROBE-A kernel-read HD's `hrank` residual = `w`-FREE, so the feared 'dual-functional→`p`-row bridge' does NOT exist for HD (it's a basis-pick from full-rank R(Gab)); real W6b coupling localized to HB's `μ`-match. PROBE-B compiled the `Sum.elim` injectivity sorry-free. Decomposed into a BOT-1..BOT-4 sub-arc + ONE flagged route decision (BOT-2 free basis-pick vs BOT-3 `cGv`-containment). Episode lesson: a build agent's scope-shrink RATIONALE can be a misdiagnosis the recon catches. |
| 524 | 23f BOT-3 feasibility spike → §(4.58) route-(b) verdict (`6ed3f84`) | 3/2/1 | opus | recon | clean | ✓✓——✓✓ | 148k tok / 52 tools / 8.2 min | Compiler-checked feasibility spike adjudicating §(4.57)'s BOT-2-vs-BOT-3 flag. Route (a) REFUTED: `cGv`-support rows not stated LI (landed W6b conclusion has no LI clause on the summands), can't seed `LinearIndependent.extend`. Route (b) WINS with NO wrapper reshape (the §(4.57) fear dissolved): `hB` needs only each `B`-row ∈ span(`D`-rows), which the full-rank basis-pick `D` gives — kernel-checked (`probe_matrix_eq_mul_of_span_mem` sorry-free). BOT-3 dissolves into span-membership leaf BOT-3′. Acceptance: refutation + no-reshape both verified vs landed source. Clean spike-before-build win. |
| 525 | 23f BOT-3′ span-membership leaf (`e3462f3`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 220k tok / 74 tools / 17.2 min | Dispatched as the BOT-1 keystone build; opus SLICE-SUBSTITUTED (scope-to-fit) to BOT-3′ (`matrix_eq_mul_of_span_mem`, the §(4.58.E) leaf) — complete, axiom-clean, sig-exact, a free-standing mirror of leaf (i) (no BOT-1/2 dep). BUT the BOT-1 DEFERRAL reason is questionable: agent called BOT-1 'partly BLOCKED in matrix form' — a likely CONFLATION (BOT-1 is a span SET-identity via the landed `span_range_rigidityRowFunEdge` analogue + membership bricks, NOT the avoided matrix-equality form). Coordinator → BOT-1 kernel-check next (user directive). |
| 526 | 23f BOT-1 cross-framework spanning identity (`008bd41`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 306k tok / 108 tools / 26.8 min | Kernel-check of the BOT-1 deferral (per user directive). RESOLVED: refuted the prior agent's 'BOT-1 partly BLOCKED in matrix form' conflation (the BLOCKED thing is a matrix-EQUALITY form the project avoided; BOT-1 is a span SET-identity) → BANKED `span_range_hingeRow_crossFramework_eq_rigidityRows` (Basic.lean) axiom-clean. ALSO caught a real §(4.58.E) RHS error (`caseIIICandidate.rigidityRows` finrank too large → `R(Gab).rigidityRows`). Deferred-crux watch: BOT-1's remap/hspan/hlink₁ deferred to the wrapper — accumulating with BOT-3′/skeleton; flag a wrapper-assembly satisfiability recon. |
| 527 | 23f BOT-2 bottom basis-pick (engine + bridge) (`a90a4f7`) | 2/3/1 | opus | normal | clean | ✓✓✓—✓✓ | 250k tok / 95 tools / 20.5 min | Kernel-check/build of the bottom selection. BOT-2 BUILT sorry-free, axiom-clean (the basis-pick engine + the bridge `bottom_selection_of_crossFramework_span` → the wrapper's `hD` data). The concrete BOT-1 instantiation hit the COORDINATOR-FLAGGED `e_a` self-loop obstruction (a-shift → `ends₁ e_a=(a,a)`, `hlink₁` demands a self-loop in loopless Gab) — kernel-checked + recorded as R1 (flag-don't-force), NOT forced. Note: lean_verify gave a SPURIOUS `sorryAx` on the bridge (stale LSP) — refuted by whole-file grep + warning-clean build. |
| 528 | 23f R1 restricted-edge cross-framework span variant (`bd67f0c`) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 169k tok / 72 tools / 12.8 min | R1 landed clean first-pass (axiom-clean): the restricted-edge BOT-1 variant `span_range_hingeRow_crossFramework_eq_rigidityRows_of_off` (predicate `P` for genuine edges + `hoff` discharging off-`P` rows to zero via `hingeRow_self`), folding §(4.60.C)'s two parts (restricted variant + zero-`e_a` drop) into one lemma. Agent verified it feeds the BOT-2 bridge's `hspan_id` via a compile-checked spike (then removed) — the 'build against the literal' check, good practice. The bottom basis-pick sub-arc BOT-1→BOT-2→R1 is now complete in tree; next = BOT-4 (Sum.elim + HMEQ). |
| 529 | 23f joint-satisfiability recon → §(4.61) exclusion-steering (`024b361`) | 3/2/1 | opus | recon | clean | ✓✓✓—✓✓ | 278k tok / 93 tools / 24.0 min | Joint-satisfiability recon (coordinator pre-dispatch flag) CAUGHT A REAL SATISFIABILITY TRAP: the free BOT-2 pick can select the corner's `(e_b, j₀)` slot → breaks `re` injectivity (the `hdisj` §(4.57.D) ASSUMED is NOT derivable, kernel-confirmed). Fix = exclusion-steering; BANKED the exclusion engine `..._avoiding` (axiom-clean). CORRECTS §(4.58)'s 'free pick' verdict (exclude one redundant index, ≠ the refuted route-a containment). Broader 7-hyp firing feasibility confirmed, no other trap. Flag: `hred` is a 'stronger j₀-literal' than W6b's redundancy — deferred to BOT-2′/dispatch. |
| 530 | 23f BOT-2′ exclusion-steered bridge (`c64dee0`) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 146k tok / 58 tools / 9.4 min | BOT-2′ landed clean first-pass (axiom-clean): `bottom_selection_of_crossFramework_span_avoiding`, the exclusion-steered sibling of BOT-2 running the banked `..._avoiding` engine over `{p ≠ p₀}`, emitting `havoid : ∀ i, re i ≠ p₀` (the disjointness BOT-4 needs for `re` injectivity) + taking the `hred` j₀-literal redundancy as a hypothesis (the §(4.61)-flagged residual, deferred to the dispatch). Resolves the `(e_b, j₀)` tension at the bridge level on the pinned route. Next = BOT-4 (Sum.elim + HMEQ). |
| 531 | 23f BOT-4 `Sum.elim` strict-injection assembly (`95823e5`) | 2/2/1 | opus | normal | clean | ✓✓✓—✓✓ | 165k tok / 48 tools / 8.1 min | BOT-4 landed clean first-pass (axiom-clean): `cornerRowInjection_sumElim_injective` — the full `re`/`hre` strict-injection `Sum.elim` assembly, `hdisj` split on the corner index (`Sum.inl` panel by carried `hbot_ne_ea`, `±r` slot by BOT-2′'s `havoid`). HMEQ rides on mathlib `fromBlocks_toBlocks` (no new lemma). The RE strict injection is now COMPLETE in tree. The e_a-panel disjointness `hbot_ne_ea` is a NEW carried hyp (deferred to the dispatch) — adds to the accumulating dispatch obligations (hred/havoid/hbot_ne_ea/cross-framework/gate/hAeq), to be reconned before item 4. |
| 532 | 23f sub-leaf HA via `C=0` route (`d5a2e1d`, REVERTED by `12dc4e2`) | 2/3/1 | opus | normal | mis-targeted | ✓✓✗—✗✗ | 234k tok / 85 tools / 16.7 min | Gate-clean, axiom-clean leaf (`…toBlocks₁₁_sub_mul_toBlocks₂₁…`) discharged `hA` via `C=toBlocks₂₁=0` from a carried `hbot` (both bottom endpoints ≠ v) — but `hbot` is UNSATISFIABLE for the consumer: the same-`re` `hD` forces v-incident `e_b` fill rows into the bottom, so `C≠0`. The "ρ₀ over-engineered / HA done" prose was the propagated error. Coordinator caught at acceptance (wrapper's tautological `hbot1` + mixedBottom a-shift vs the leaf's `hbot`); recon row 533 confirmed + reverted. Deferred-hyp / coupled-hyps-over-shared-`re` trap (FRICTION). |
| 533 | 23f HA `C=0` satisfiability recon → §(4.62) + revert (`12dc4e2`) | 3/2/1 | opus | recon | clean | ✓✓✓—✓✓ | 253k tok / 99 tools / 20.1 min | Compiler-checked recon (4-part spike, sorry-free, deleted) of row-532's `C=0` route. VERDICT C≠0: `hbot` unsatisfiable — the wrapper feeds ONE `re` to both `hA` and `hD`; `hD` needs `hrank=card m₂`, unreachable by pure-`Gv` rows (span R(Gv), `Gv=G−v` deficient, finrank<card m₂), so the bottom MUST include v-incident `e_b` rows ⟹ `C≠0`. Q3 (re-steer to avoid e_b) rejected (breaks `hrank`). Corrective: removed the dead leaf, added §(4.62) + FRICTION, re-pointed HA to the designed ρ₀-route (leaf iii + `hAeq`). Gates green, axiom-clean, d=3 untouched. |
| 534 | 23f sub-leaf HD `Sum.elim`-`re` mixed-bottom block row-LI (`b41b99a`) | 2/3/1 | opus | normal | clean (pivot) | ✓✓✓—✗✓ | 205k tok / 86 tools / 13.3 min | Pivoted HA→HD (scope-to-fit: HA's ρ₀-route lands at the dispatch; HD is the cleanly-separable leaf). Landed `…toBlocks₂₂_row_sumElim_mixedBottom…` — the wrapper's `hD` for the full `re=Sum.elim(corner∘split) bottom`, a 3-line specialization of the existing producer at `m₁:=Fin(screwDim k)` (`re(Sum.inr i)=bottom i` defeq). CORRECTLY targeted (unlike C=0 HA): `hbot2`/`hbot1`/`hrank` ARE BOT-2′'s satisfiable outputs, shape = wrapper's `hD`. Coordinator re-ran below-top-rung gates clean. Left a Current-state inconsistency (HD-done vs "Next=HA") — flagged, fixed by the §(4.64) recon (notes ✗). |
| 535 | 23f item-4 dispatch joint-satisfiability recon → §(4.64) (`90a368f`) | 3/2/1 | opus | recon | clean | ✓✓——✓✓ | 246k tok / 87 tools / 14.2 min | Compiler-checked dispatch-level spike (fired the wrapper at the concrete binding, sorry-fed, deleted). Q1 JOINT-SAT=YES: HMEQ (`fromBlocks_toBlocks`)+HD close at the fire with ZERO sorry; `hA`/`hB` residuals share ONE `?L₀` metavar (the C=0 crux now sound by construction). Q2: decomposed item 4 into D1–D8 + separable CHAIN-5, exact sigs; FIRST=D1 `interior_hsplitGP`. Q3: one build-deferred decision (D4 `hred` coupling, route-(a)-feasible); item-3c `rfl`-level; no contract/motive change beyond the approved C.3 hIH. Reconciled Phase23f.md (fixed the HD/HA inconsistency). Docs-only. |
| 536 | 23f D3/D4 dispatch build (hred crux) → BLOCKED (HEAD stays `8e03871`) | 2/3/1 | opus | normal | BLOCKED | —————— | 168k tok / 28 tools / 5.0 min | Dispatched D3 (inline dispatch step); agent correctly BLOCKED: D3 isn't a standalone decl (it's `have`s in the unbuilt `chainData_dispatch`, gated on all D3–D8) and needs `hred` (D4). Diagnosed the crux at source: `blockBasisOn` (`Concrete.lean:510`) is opaque `finBasisOfFinrankEq`, so D4's `hred` for the literal `(e_b,j₀)` row has no free j₀-coordinate lever — a GENUINE open design decision, not a one-sitting leaf. Named two routes, asked for adjudication. Correct well-diagnosed BLOCKED (no forced sorry); triggered the §(4.65) recon. |
| 537 | 23f D4 `hred` route recon → §(4.65) STOP-for-human (`ee6fd67`) | 3/2/1 | opus | recon | clean (STOP) | ✓✓——✓✓ | 263k tok / 81 tools / 14.3 min | Compiler-checked spike (built literal `hred` at the concrete binding, fed the W6b widening, read the kernel residual). Route (b) REFUTED: `blockBasisOn` opaque + ρ₀ ∈ `hingeRowBlock e₀` (splitOff fresh edge) ≠ `hingeRowBlock e_b` (candidate); cert reads `blockBasisOn` at integer indices, never ρ₀. OVERTURNS §(4.61.D)/§(4.64)'s 'route-(a)-feasible' (C=0-style over-optimism). STOP for human: (α) re-shape `_zero₁₂` ±r row to read `hingeRow a b ρ₀` (KT 6.66; ~4–7 commits; dissolves hred/BOT-2′/avoiding-engine; RECOMMENDED) vs (β) re-attack the §(4.18)–(4.30) walled dual-space route. Docs-only. |
| 538 | 23f route-(α) decomposition design-pass → §(4.66) (`cf4722c`) | 3/2/1 | opus | recon | clean (re-route) | —✓——✗✓ | 273k tok / 73 tools / 18.1 min | Design-pass RE-ROUTED route (α): §(4.65.E)'s `re`-rekey prose unbuildable (no `rigidityMatrixEdge` index reads `ρ₀`) → AUGMENTED matrix (mirror of chain cert's `g`-member), eliminating the row op (B1/B2/BOT-3′/leaf iii orphaned). 3 clauses honored: PROBE A/B/C spike-verified, αE4 `hblock` residual flagged, §(4.65.F) confirmed. Coordinator verified the 'survives' claims vs landed source (backbone M-generic + bare `corner_hA'_of_gate`). Notes ✗→fixed 09f6775: compression left checklist `[ ]` HA/HB + the RECON-COMPLETE para showing the dead row-op route as live. |
| 539 | 23f αE4 `hblock` recon → §(4.66.F/G) correction (`b9891e9`) | 3/2/1 | opus | recon | clean (correction) | —✓——✓✓ | 272k tok / 95 tools / 19.3 min | Recon CAUGHT that BOTH the §(4.66) design pass (538) AND the coordinator's proposed `_zero₂₁`/`:528` fix were WRONG: route (α) STILL needs the row op (`_zero₁₂`/`:622`). Grounded in SETTLED §(4.62) (interior bottom's v-incident `e_b` rows ⟹ `C≠0`, `_zero₂₁` unavailable; `B≠0` ⟹ row op mandatory) — both design+coordinator overlooked it. Augmented matrix still needed (genuine `ρ₀`); only `(e_b,j₀)` machinery orphaned, B1/B2/leaf(iii) STAY. Lesson (→Findings): a re-route DELETING machinery must be cross-checked vs ALL settled downstream verdicts, not just named decls. |

## Findings

(accumulate episode bullets here; distill at each phase close per
the protocol)

- **23f route-(α) decomposition, rows 538–539 (the spike-before-build saved 2–3 dead leaves).** The §(4.66)
  design pass (538, opus) RE-ROUTED route (α) to an augmented matrix and claimed it eliminates the corner
  row op ("delete B1/B2/BOT-3′/leaf iii"). The coordinator accepted it after verifying the backbone's
  `M`-genericity + the bare `corner_hA'_of_gate` IN ISOLATION — and propagated the (wrong) orphaning into the
  phase note. Then the coordinator's αE4 scrutiny caught a `_zero₁₂`-vs-`_zero₂₁` shape tension and dispatched
  a correction recon (539, opus), which — reading the SETTLED §(4.62) `C=toBlocks₂₁≠0` verdict — found BOTH
  the design's "no row op" AND the coordinator's proposed `_zero₂₁` fix wrong: the interior bottom's v-incident
  `e_b` rows force `C≠0` (so `_zero₂₁` is geometrically unavailable) and `B≠0` keeps the row op mandatory. The
  augmented matrix is still correct + needed (it sources the genuine `ρ₀` corner row, dissolving the §(4.65)
  `hred`), but the row-op machinery (B1/B2/BOT-3′/leaf iii) STAYS. **Coordinator-acceptance lesson:** a recon
  that *deletes/orphans* landed machinery must be cross-checked against ALL settled downstream verdicts (here
  §(4.62)), not just the decls it names — the "build against the literal product before the interface leaves"
  constraint is what made the αE4 spike fire before αE2/αE3 baked in the wrong `hblock` shape. Candidate
  sharpening of the coordinate-phase *supersession-deletion check* at phase close.

- **23f geometry arm, rows 515–518 (all opus, all clean first-pass).** Four carrier-agnostic
  matrix-backbone leaves — (i) `cGv`→`w` re-key, (ii) `Lrow`-on-`p` reindex unit-det, (iii) post-row-op
  corner-`hA`, and the `hblock` reducer — all landed clean on pinned routes on the FIRST opus pass, no
  escalation. The common enabler: a fresh kernel-confirmed recon (§(4.54) end-to-end spike) had already
  pinned each leaf's signature, so P=2/P=3 builds ran clean. Each leaf is stated abstract, deferring its
  literal-product wiring to the wrapper. **Coordinator-verification win (rows 518):** the `hblock` reducer
  landed axiom-clean and gate-green, yet its proof method (`submatrix_mul_equiv`) silently bakes in
  `e : (m₁⊕m₂)≃p` a **bijection**, while leaf-(ii)/design framing says the arm's `re` is a strict
  **injection** (drops the D−2 surplus rows). Gates + sorry-grep + the conclusion's type all pass; only
  reading the cert's *actual* `re : m₁⊕m₂→p` signature exposed the latent consumer-fitness contradiction
  (a deferred-bridge whose *proof requirement* — not its hypothesis value — is stronger than the consumer's
  slot). Caught at acceptance, reframed the wrapper recon-first. **Resolved (rows 519/520):** the §(4.55)
  recon settled the shape = (b) strict injection (the bijection needs the un-grounded `card(m₁⊕m₂)=card p`),
  and opus landed the strict-injection siblings B1/B2 (subsuming (ii)/(iv)) clean first-pass.
  **Promoted a fresh corollary** (DESIGN.md *Constructibility recon* + the coordinate-phase command,
  2026-06-26): the 23d architecture-shape "too-strong shape" trap can **re-enter at the leaf proof-method
  level** even after the kernel/cert is correctly reshaped to tolerate the weaker shape — a leaf's proof API
  (`submatrix_mul_equiv`/`det_reindex_self`, anything needing an `Equiv`/bijective middle index) silently
  re-imposes the `card`-equality the kernel was reshaped to drop, invisible to the leaf's (correct)
  conclusion type and to gates. The 23d corollary covers the *kernel* shape; this instance shows it recurs at
  the *feeder leaves* — so it earned the sharpening, not just a "fresh instance" note.
- *(The 23e *Findings* (sessions #36–#38: the spike-before-build /
  2-leaf-trigger pattern that broke the recurring "remaining = ASSEMBLY" mis-framing, the
  deferred-crux scrutiny, the architecture-shape satisfiability check, profile×rung) are in the
  **23e close-out** in `notes/model-experiment-archive.md`. The durable cross-phase lessons live in
  the coordinate-phase command + DESIGN.md *Constructibility recon*.)*
