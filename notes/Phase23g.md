# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** CLOSED (2026-07-02; opened 2026-07-01). The `ENTRY` sub-phase of the Case III
general-`d` program: CHAIN-5 (the C.0-trio dispatch reshape) plus the full E1–E5 ENTRY leaf
ladder, all landed axiom-clean, `d=3` fully green throughout. The two Case-III general-`n`
green-modulo hypotheses now have dischargers — `hextract` is **discharged** at general `n` (E3)
and `hcycle` has its brick (E5, `PanelHingeFramework.cycle_realization`) — but the
producer/spine sites still *carry* them as binders (the `d=3` wrappers fill them); wiring is
23h. Authoritative scoping: `notes/Phase23-design.md` §C.0–C.6 (the frozen CHAIN↔ENTRY
contract, untouched) + §(4.107)/(4.108) (compressed to verdicts at close). Program map:
`notes/MolecularConjecture.md`.

## Hand-off / next phase

**23h (ASSEMBLY) opened 2026-07-02** — the live work log is `notes/Phase23h.md`; this section
stays as the frozen hand-off record. Its work, per `notes/MolecularConjecture.md` §Phase 23:

- **Producer-site rewire:** consume `Graph.chainData_extract` (fills `hextract`) and
  `PanelHingeFramework.cycle_realization` (fills `hcycle`) at the four producer/spine sites
  (`case_III_hsplit_producer_all_k` + wrapper in `Arms.lean`, `case_III_realization_all_k` in
  `Realization.lean`, `theorem_55_minimalKDof_k_all_k` in `Theorem55.lean`), dropping the
  green-modulo binders; the `d=3` wrappers keep working via `chainData_extract_d3`.
- Then the spine assembly: Thm 5.5 → re-green `prop:rigidity-matrix-prop11` → Thm 5.6 →
  Conjecture 1.2.
- **Carried forward:** GAP 6 (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
  orthogonal to the cert); the two `d=3`-era orphan decls under *OUT-OF-SCOPE* below
  (delete-or-keep sweep); the coordinator-owned `notes/model-experiment.md` archive step for
  23g's rows (not done in the close commit — the dispatch log is coordinator-owned).

## Lemma checklist (the §(4.107.D) ENTRY ladder — all landed 2026-07-01/02)

- [x] **CHAIN-5** (`74bd9003`) — the C.0 lockstep reshape + router wire-up: the 23f router
  `chainData_dispatch` *discharges* the Case-III chain dispatch at general `k` inside
  `case_III_realization_all_k`
- [x] **E1** `Graph.CycleData` + `vertexSet_ncard`/`range_vtx` (`Operations.lean`)
- [x] **E4** the shape-2 `hextract`/`hcycle` binder reshape at the four producer/spine sites;
  `d=3` wrappers refilled (`Or.inl ∘ chainData_extract_d3` + vacuous `hcycle`), zero-regression
- [x] **E2** `Graph.chainData_or_cycleData_of_noRigid` — KT Lemma 4.6, the genuinely-new
  combinatorial leaf, split along the §(4.107.D)/(4.107.G.5) sub-leaves (one commit each):
  E2a min-degree/connectivity (`Deficiency.lean`); E2b degree-2 existence (`Reduction.lean`;
  KT-expositional, not an assembly input per (G.7)); E2c the general cycle→proper-rigid-subgraph
  (`isKDof_zero_of_cycle` + `cycle_isProperRigidSubgraph`); E2d-1…7 the capped-trichotomy
  walk-builder + determinism + charging + the (4.8)/(4.9) arithmetic close (the new
  `ForestSurgery/ChainExtraction.lean`); E2e `kt_lemma_46_linking` + `le_bodyBarDim`;
  E2-assembly (`by_contra` → all-starts-terminated → E2d-7)
- [x] **E3** `Graph.chainData_extract` (`ChainExtraction.lean`) — discharges `hextract` at
  general `n`; purely additive (no producer site touched)
- [x] **E5** `PanelHingeFramework.cycle_realization` — KT Lemma 5.4 (Crapo–Whiteley 1982
  Prop. 3.4 / Whiteley 1999 Prop. 3, verified from the PDFs), discharging `hcycle`:
  E5a `exists_cycle_normals` (`PanelLayer.lean`); E5b `theorem_55_cycle` (`Pinning.lean`);
  E5c the assembly (`CaseIII/Arms.lean`) + `CycleData.range_vtx` + the blueprint pins

## Decisions made (one-line verdicts; reasoning in git, the design §§, and the Lean source)

- **CHAIN-5:** dispatch *discharged* (not carried) at general `k`; `hdispatch` DROPPED, `hn` +
  `hextract` ADDED; the `cd.vtx ⟨i, by omega⟩` `Fin.mk` form (not OfNat) → FRICTION *[idiom]
  carried-hypothesis field indexing*; the §C.4 `d=3` adapter `chainData_of_exists_chain_data`.
- **ENTRY satisfiability (design §(4.107)):** OD-1 = shape 2 forced (chain-only unsatisfiable at
  general `n`); `d_eq : d = n` source-faithful; Lemma 5.4 load-bearing; `hD` floor lift
  dissolves (honest leaf floor `3 ≤ bodyBarDim n`, spine keeps 6).
- **E1:** `link` field uses `vtx (i + ⟨1, by omega⟩)` (OfNat needs `NeZero`, unavailable in a
  field type) → FRICTION (recurrence of the CHAIN-5 `Fin.mk` deviation).
- **E4:** one-commit zero-regression lockstep across the four sites; blueprint untouched.
- **E2a/E2b:** compositions over the landed Phase-20/22i stacks (2EC → min-degree 2 +
  connectivity; `exists_degree_le_two` + E2a → degree-2 existence). Zero friction.
- **E2c:** explicit-data signatures (`vtx` injectivity NOT needed for the count); the
  boundary-index injection parts ↪ crossing edges; `Fin m` scoped-ring arithmetic →
  TACTICS-QUIRKS § 70 (+ addendum: `abel` needs `[NeZero m]` locally in scope).
- **E2d ladder + E2e:** package `WList`/`IsPath` walk-builder, one-shot `Fin`-record boundary
  conversion; charging via `Set.ncard_le_ncard_of_injOn` (not the pinned fiberwise sum);
  subtraction-avoiding additive reshape + `nlinarith` for the close → TACTICS-QUIRKS §§ 48
  (broadened), 71, 72; FRICTION entries per leaf. Unused `[DecidableEq]` instances dropped,
  `_`-named unused binders (below-contract, cosmetic).
- **E2-assembly:** exactly the design sketch (`by_contra` + `chainWalk_trichotomy` at every
  incidence + `chainWalk_terminated_contradiction`); E2b not consumed. Zero friction.
- **E3:** pinned signature verbatim; reads the interior fields at `i = ⟨1, _⟩` in the pin's
  literal `(a, b) = (vtx 0, vtx 2)` order (no `splitOff_swap_ab` reconciliation, contrast the
  `d=3` adapter); `rcases` can't unwrap `Nonempty X ∨ Y` in one step → FRICTION *[idiom]*.
- **E5 recon (design §(4.108)):** 3-commit triangle-patterned ladder; keep-in-23g
  (user-sanctioned); the landed extensor existence gives free *pairs* — unusable for the
  shared-panel seed, hence E5a.
- **E5a:** standard-basis witness along `Fin.castLE`; `[NeZero m]` binder added (OfNat);
  `ι`-injectivity via regular `AddCommGroup (Fin m)` cancellation (no scoped-ring needed) →
  FRICTION ×2 (`Pi.smul_apply'`; `lt_or_gt_of_ne`).
- **E5b:** verbatim adaptation of the two green `Fin m`-body telescoping lemmas onto `S ∘ vtx`;
  **no `vtx` injectivity**. Zero friction.
- **E5c:** §(4.107.D) pin by type (`_hk1`/`_hV4` underscore-named); `n = k + 1` inline
  (`d_eq_kAdd` pattern); the `▸`-under-binder revert failure → TACTICS-QUIRKS § 73; the
  goal-changing-`show` linter → FRICTION *[idiom]* (term-mode `extend_apply`).
- **Blueprint:** `lem:cycle-realization` pinned + green, caveat rewritten (only the
  independent⟹rigid CW direction is consumed); minted `lem:cycle-normals`, `def:cycle-data`,
  `def:chain-data`, `lem:chain-cycle-dichotomy`, `lem:chain-data-extract` (the E1–E3 sync);
  E5b joined `lem:cycle-realization-rigid`'s `\lean` group (no new node); exposition-ledger
  entry for the Lemma-4.6 dichotomy written at close (`notes/BlueprintExposition.md`).

## LIVE — DO NOT delete / DO NOT plan to delete
- `caseIIICandidate` + its API — the honest engine consumes it via `case_III_realization_of_rank`
  ← `case_III_arm_realization`.
- The non-aug edge-path helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in
  `RigidityMatrix/Concrete.lean`.

(Distinct from the retired `_aug` fork, fully deleted across 23f's four deletion commits.)

## OUT-OF-SCOPE `d=3`-era orphans (inherited by the 23h sweep)
- `interior_hsplitGP` (`CaseIII/Realization.lean`).
- `case_III_realization_of_line` (`CaseIII/Arms.lean`).
