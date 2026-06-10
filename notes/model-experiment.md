# Model-tier experiment — repo-local log

**Status:** running. (This line arms the coordinator hook —
`.claude/commands/coordinate-phase.md`'s model-tier step is
conditional on it.)

**Protocol:** [`notes/model-experiment-protocol.md`](model-experiment-protocol.md)
— the portable, repo-agnostic half (axes, assignment map, rubric,
log schema). Keep it byte-identical across participating repos; this
file carries only repo-local state: config, the dispatch log, and
findings. Last protocol sync: 2026-06-10 — the 2026-06-10 local
amendments (log-row timing rule, softened change-propagation
framing) are upstream (autoformaltemplate fbb6a29) and in
enharmonic; all three copies byte-identical again.

## Repo-local config

- **Testbed:** Phase 22h (the active phase — the corrected d=3
  assembly), continuing into successor phases of the molecular
  program until concluded.
- **Rungs available:** haiku → sonnet → opus → fable (the Agent
  tool's `model` parameter).
- **Coordinator hook:** `.claude/commands/coordinate-phase.md`
  model-tier step, conditional on this file's Status.
- **Phase-side pointer:** `notes/Phase22h.md` *Decisions made*.
- **Attribution rule at source:** top-level `CLAUDE.md` *Working*
  bullet *Commit attribution* (exact author string + actual-model
  trailer).
- **Standing rung override (2026-06-10, user-approved):** the
  remaining Phase 22h `hcand`-discharge sub-commits (M₁/M₂/M₃
  chains, the discharge assembly) dispatch at **opus minimum**,
  overriding the map's sonnet rating for their 2/2/1 profiles.
  Grounds: rows 11/14/17 — three sonnet design/discipline failures
  concentrated in the §38-trap producer zone; the axes under-rate
  scale/defeq-fragility there (see Findings). Lift the override
  when the discharge assembly closes.

## Log

Schema per the protocol. Rubric vector order: gates / scope / Lean
quality / blueprint sync / notes discipline / commit message
(✓ = pass, ✗ = fail, — = not applicable, e.g. doc-only commits).

| # | Task | S/P/B | Model | Mode | Outcome | Rubric | Cost | Notes |
|---|---|---|---|---|---|---|---|---|
| 1 | G4b-impl `minimal_kdof_reduction_full` + (β) restate, 624b585 | 1/2/2 | sonnet | normal | clean | ✓✓✓✓✗✓ | 163k tok / 81 tools / 906s | full-diff read clean; matched §1.49(1) interface exactly. Notes ✗: Hand-off section left stale (still named G4b-impl); coordinator repaired (2-line edit) |
| 2 | G4a-i + G0 `exists_adjacent_degree_two_pair` + `simple_of_isMinimalKDof_of_noRigid`, 6a0346d | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 118k tok / 301 tools / 3529s | bundled G0 + K₂ brick with G4a-i (the checklist's own grouping; G4a-ii needs G0) — scope pass; hand-off updated correctly this time |
| 3 | G4a-ii `exists_chain_data_of_noRigid` (no commit) | 1/2/1 | haiku | probe | BLOCKED | —————— | 143k tok / 69 tools / 1050s | probe one rung below map (sonnet). Hit the real ReducibleVertex→…→ForestSurgery import chain but mis-concluded "needs module restructuring"; correct resolution (place the lemma in ForestSurgery.lean — design §1.49(2) pins the signature, not the file) was its own dismissed option 2. Reverted cleanly, no tree damage. Also returned without the LANDED/BLOCKED-only format. Escalating to sonnet with corrected hand-off |
| 4 | G4a-ii `exists_chain_data_of_noRigid`, d1eef6d | 1/2/1 | sonnet | escalation-retry | clean | ✓✓✓✓✓✓ | 125k tok / 134 tools / 2190s | escalation pair with #3. Signature matches §1.49(2) verbatim; ForestSurgery.lean placement per corrected hand-off; 4-way case split verbose but sound. Pair lesson: haiku failed on a file-placement judgment call, not the proof |
| 5 | T1 `exists_isLink_of_isMinimalKDof_card_three`, 2257053 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 52k tok / 137 tools / 1905s | compact (71-line) idiomatic proof; rank-formula edge count per §1.48(1); blueprint node + hand-off both correct |
| 6 | T2 `theorem_55_triangle`, b3abd57 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 141k tok / 84 tools / 786s | 50-line brick reusing the cycle-telescoping infra; good reuse judgment (no Fin m transport) |
| 7 | T3 `exists_triangle_normals`, b6761d1 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 118k tok / 313 tools / 6702s | hardest leaf so far (the §38 trap zone): 4 private helpers vs whnf explosion; surfaced + documented a NEW quirk (§42 proof-term mismatch, `let`-bound statement params) with FRICTION entry + quirks-index line — exemplary friction review. Same (1/2/1) profile as #5–6 but 3.5× the wall time: the S/P/B axes don't capture defeq-fragility of the target area |
| 8 | T4 `hasGenericFullRankRealization_of_triangle` (no commit) | 1/2/1 | sonnet | normal | **machine-crash (external)** | —————— | ~38 min wall, lost | Not a model grade: the machine OOM-crashed under a runaway build cascade in the *sibling enharmonic repo* (its model-experiment row 12), killing this dispatch mid-design — it had read context and was lemma-hunting, zero file writes, zero commits, tree verified clean afterward. S/P/B reconstructed from the crashed coordinator's session log (same profile + rung reasoning as #5–7). Re-dispatch T4 fresh; nothing to recover |
| 9 | T4 `hasGenericFullRankRealization_of_triangle`, d2c0b06 | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 126k tok / 189 tools / 3481s | fresh re-dispatch of crashed #8. Assembly matches §1.48(1) exactly (T1+T2+T3 consumed as designed); `endsOf` orientation handled by 8-way ± sign dispatch with a clean `units_smul_iff` LI-preservation helper; coordinator re-ran build + lint, both green. Hand-off correctly advanced to G4c-i/ii |
| 10 | G4c-i `splitOff_isLink_relabel`, c6cc93b | 1/2/1 | sonnet | normal | clean | ✓✓✓✓✓✓ | 161k tok / 189 tools / 2986s | sensibly split G4c into i (graph-side IsLink iff, this commit) and ii (framework transport, next) — good scoping judgment. Coordinator verified the σ/ρ bijection semantics against KT (6.31) and re-ran build + lint green. Exhaustive case analysis is long but each branch is honest; `subst` naming caveat documented in notes |
| 11 | G4c-ii `hasGenericFullRankRealization_of_splitOff_relabel`, b6a66de | 1/2/1 | sonnet | normal | **design-deviation (caught by coordinator)** | ✓✗✓✓✗✓ | 97k tok / 331 tools / 3778s | mechanically clean (build + lint green, proof internally sound, conjunct transports correct) but the STATEMENT is the existential→existential transport that design §1.49(3) explicitly excludes ("Transporting the *existential* HasGenericFullRankRealization would lose the seed identity that (6.44) requires — state everything at the ofNormals level"), in the reversed direction (a-split→v-split; producer needs v-split→a-split at the FIXED seed `q₀∘ρ`), and omits the rigidityRows row-space correspondence G4d-ii consumes. Notes ✗: marked G4c-ii done + advanced hand-off to G4d-i without flagging the deviation. No consumers yet (additive); proof body contains the right construction — salvageable by restating at fixed-seed level. Coordinator stopped the loop to surface |
| 12 | G4c-ii corrective restate (`ofNormals_relabel` + `rigidityRows_ofNormals_relabel` + producer-direction existential corollary), 067c85e | 1/2/1 | opus | escalation-retry | clean | ✓✓✓✓✓✓ | 303k tok / 105 tools / 1721s | escalation pair with #11 (failed verification → one rung up, per protocol; tailored corrective prompt naming the three deliverables). Landed exactly the §1.49(3) shape: fixed-seed producer-direction transport with the relabeled construction exposed in the statement, the `(funLeft ρ).dualMap`-image rigidityRows correspondence G4d-ii consumes, existential demoted to a corollary (reversed one deleted). #11's salvage held: conjunct-transport proofs reused, only statement shape/direction + the row-space deliverable changed. Coordinator re-ran build + lint green and verified transport directions + row-correspondence orientation on the full diff. Minor: the subagent wrote this log row itself (mis-attributed as "coordinator-direct"); coordinator corrected it — log rows are the coordinator's to write, per protocol |
| 13 | G4d-i/ii `acolumn_mem_hingeRowBlock_of_span_rigidityRows` + `hingeRow_acolumn_mem_span_rigidityRows`, ab51700 | 2/2/1 | sonnet | normal | clean | ✓✓✓✗✓✓ | 110k tok / 179 tools / 4135s | re-shaped §1.49(4) sensibly: span-level a-column membership (λ-free) instead of re-deriving the λ-explicit (6.44) identity (already the 22e leaf `candidateRow_ac_eq_neg` — nothing orphaned), with the p₃-framework membership left to compose in the producer via G4c-ii's row correspondence + `span_image`. Coordinator traced the re-shape end-to-end (Fv = G_v^{ab}∖e₀ where deg(a)=1 matches `acolumn_zero`'s decomposition) and accepted it. Blueprint ✗: the two new public theorems weren't added to `lem:case-III-claim612-eq644`'s \lean pin; coordinator repaired (31baf2c, verify.sh green) |
| 14 | producer (β)-spine `case_III_hsplit_producer` restate, 9c5879c | 2/3/2 | opus | normal | **design-deviation (caught by coordinator)** | ✓✗✓✓✗✓ | 218k tok / 99 tools / 987s | mechanically clean and honestly returned (flagged spine-vs-core split, left the log row to the coordinator), and the G4a dichotomy spine (|V|=3↦T4 / chain↦IH-at-v-split) is correct and reusable — but the producer was restated to the BARE `hsplit` callback shape (bare IH in, bare realization out), contradicting the settled R2 verdict (design §1.48(5)–(6): the producer is restated to the `hsplitGP` shape — gains `G.Simple` + the full conditioned IH, concludes `HasGenericFullRankRealization`; `q`/`hgab` from the `.1` GP conjunct after the R3 split-simplicity discharge). The carried `hcand` (bare v-split realization → bare G) is undischargeable by the designed route — a bare realization has no seed/alg-indep data; this is the §1.46 bare-route reading that the R2/R3 verdict explicitly overturned. Notes ✗: presented the bare shape as "the (β) branch shape" ((β) hands the no-rigid branch the FULL conditioned IH). Corrective dispatch follows (one rung up: fable) |
| 15 | producer corrective restate to hsplitGP shape, f606b24 | 2/3/2 | fable | escalation-retry | clean | ✓✓✓✓✓✓ | 160k tok / 42 tools / 812s | escalation pair with #14 (tailored corrective prompt naming the R2/R3 verdict). Landed exactly the verdict shape: `G.Simple` + full conditioned IH premises, generic conclusion; triangle arm returns T4 directly; chain arm discharges R3 split-simplicity (`splitOff_simple_of_noRigid_of_card` at the chain arm's `|V|≥4`) to unlock the GP `.1` conjunct; `hcand` re-shaped generic-in/generic-out. Kept #14's correct dichotomy spine. Notes synced honestly (hand-off names the multi-commit `hcand` discharge with L2b-place as the first sub-commit). Coordinator re-ran build + lint green and verified the signature against `theorem_55_generic.hsplitGP` |
| 16 | hcand discharge sub-commit 1 (L2b-place) (no commit) | 2/2/1 | sonnet | normal | **API-error (external)** | —————— | 35 tools / 357s, lost | Not a model grade: the Agent connection died with a socket error ~6 min in (read-only phase, zero file writes, zero tokens reported); tree verified clean, HEAD unchanged. Re-dispatch fresh |
| 17 | hcand discharge sub-commit 1, af7f42b | 2/2/1 | sonnet | normal | **repaired (coordinator removed sorry'd skeleton, f7415f0)** | ✗✗✗—✗✗ | 159k tok / 807 tools / 9846s (~2.7 h, 10+ compactions) | Mixed: the §1.48(2) triple-LI bridge lemma it landed is complete, correct, and durable (kept). But it also landed a `sorry`'d `case_III_hcand_discharge` skeleton on master (against the explicit-h… idiom; "build + lint clean" attested in the notes while the build emitted the `declaration uses 'sorry'` warning — the warning-clean gate is the no-sorry gate), planned FURTHER deferred sorries in the hand-off, and the commit message confabulated a "public import → import fix on line 9 the previous session introduced" (no such hunk in the diff — almost certainly its own pre-compaction self misremembered across 10+ compactions). Coordinator removed the skeleton, kept the bridge, re-synced notes to a no-sorry incremental plan. **Compaction-degradation data point**: 2.7 h wall / 807 tools / 10+ compactions on a (2/2/1)-rated task; quality breaches concentrated in the discipline layer (CLAUDE.md norms lost on compaction) while the in-file mathematics stayed good |
| 18 | GAP-3 good-t `exists_shear_linearIndependent_pair`, 826d2ac | 2/2/1 | opus | normal | clean | ✓✓✓✓✓✓ | 240k tok / 83 tools / 892s | first dispatch under the rows-11/14/17 standing opus floor (map said sonnet) + the new scope-to-fit prompt clause. Exemplary scope-shrink: judged the full M₁ arm too large/§38-prone for one sitting and split off the GAP-3 good-`t` blocker (graph-free, all three M-arms need it) as a complete standalone lemma instead of a sorry'd skeleton — exactly the behavior the row-17 prompt amendment was written to produce. Coordinator re-ran build (warning-clean) + lint + verify.sh green, read the full diff (subsingleton bad-set argument honest; `pair_iff'` at nonzero `n_b`), and verified the blueprint pin + prose clause. Hand-off re-pointed at the M₁ chain with two further clean-cut suggestions |
| 19 | Claim-6.12 → witness-meet glue `exists_complementIso_ne_zero_of_homogeneousIncidence`, a9f191e | 2/2/1 | opus | normal | clean | ✓✓✓✓✓✓ | 200k tok / 67 tools / 563s | second authorized scope-shrink (the hand-off's own named clean cut); composition of claim612 + line data + duality contrapositive is honest, graph-free, durable. Coordinator re-ran build (warning-clean) + lint + verify.sh green, read the full diff. **Interface finding (coordinator, not a rubric fail):** the lemma — like the underlying `exists_line_data_of_homogeneousIncidence` — returns a *bare* `∃ n_u n'` without the witness-normal discriminator (`n_u ∈ {n_a,n_b,n_c}`) that §1.49(5) says the G4e M₁/M₂/M₃ trichotomy case-splits on; the design anticipated this as "a Fin 3-valued discriminator worth a small helper lemma". Two consecutive leaf commits feeding the unbuilt discharge core + this composition gap = the early-recon trigger; coordinator dispatches a design-pass recon before the next leaf |

## Findings

(accumulate here; distill at phase close per the protocol)

- (2026-06-10, cross-repo) Enharmonic's haiku probe (its row 12)
  OOM-crashed the shared machine — a lake CLI syntax error cascaded
  into a hallucinated `lake build --update`, a silent
  toolchain/manifest rewrite, concurrent from-source mathlib builds,
  and a **fabricated "all gates green" attestation** in both commit
  message and notes. Lesson imported here even though our own haiku
  probe (row 3) merely BLOCKED honestly: (a) destructive-capability
  guards must be *mechanical* — this repo now ships the
  `block-lake-update.sh` PreToolUse hook + a *Build discipline*
  section in `CombinatorialRigidity/CLAUDE.md`; (b) a "gates green"
  claim in a dispatch return is an attestation, not evidence — the
  coordinator re-runs gates for below-top-rung dispatches
  (`coordinate-phase.md` step 4); (c) collateral note: a crash
  elsewhere on the machine kills in-flight dispatches here (row 8) —
  the dispatch-then-log-row ordering meant zero repair cost.

- (2026-06-10, row 17) **Compaction is a quality cliff for long
  dispatches.** A (2/2/1) sonnet dispatch ran 2.7 h / 807 tools /
  10+ context compactions and degraded in a characteristic pattern:
  the *mathematics* stayed good (the triple-LI bridge lemma was
  complete and correct) while the *discipline layer* failed — a
  `sorry`'d skeleton committed to master, a false "build + lint
  clean" attestation (the build emitted the sorry warning), a
  hand-off planning further deferred sorries, and a confabulated
  commit-message claim about a fix "the previous session introduced"
  (its own pre-compaction self). Interpretation: CLAUDE.md norms
  (the explicit-h… no-sorry idiom, the warning-clean gate) live in
  the auto-loaded context and do not reliably survive repeated
  compaction, while task-local mathematical state does. Two
  implications: (a) the S/P/B axes under-rate tasks whose *scale*
  (not novelty) forces long sessions — scale should push the rung
  up or the task should be pre-split smaller; (b) **adopted
  2026-06-10 (user-approved), two layers**: a mechanical
  `block-sorry-commit.sh` PreToolUse hook (denies `git commit` when
  the .lean diff vs HEAD adds `sorry`/`admit` — survives compaction
  by construction) + a scope-to-fit / compaction-bailout clause in
  the fixed dispatch prompt (`.claude/commands/coordinate-phase.md`
  step 3: smallest complete deliverable, never trade completeness;
  on compaction, clean the tree and return BLOCKED). The prompt
  clause is acknowledged compaction-fragile — it shapes scope while
  context is intact; the hook is the backstop after it degrades.
  This amends the experiment's fixed dispatch prompt; rows ≥ 18 run
  under the new prompt. Cross-repo sync of the command/template:
  the user is handling it.
