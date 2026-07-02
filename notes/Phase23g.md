# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** in progress (opened 2026-07-01). The `ENTRY` sub-phase of the Case III
general-`d` program. **CHAIN-5 landed 2026-07-01** (`74bd9003`) — the 23f router
`chainData_dispatch` now *discharges* the Case-III chain dispatch at general `k`; the single
remaining Case-III green-modulo hypothesis is the **ENTRY extractor** `hextract` (design §C.2),
discharged at `n=3` today. `d=3` stays fully green throughout. Authoritative scoping:
`notes/Phase23-design.md` §C.0–C.6 (frozen CHAIN↔ENTRY contract) + **§(4.107)** (the ENTRY
satisfiability verdict + the E1–E5 leaf ladder; supersedes §C.2's chain-only reading); the `d=3`
map is §C.4. Program map: `notes/MolecularConjecture.md`. `ASSEMBLY` = **23h** (later sub-phase).

## Current state

Next concrete build step: **E2c — `cycle_isProperRigidSubgraph`** (the next §(4.107.D) sub-leaf;
see *Hand-off*). **E2b landed 2026-07-01**: degree-2 existence
(`exists_degree_eq_two_of_noRigid`, `ForestSurgery/Reduction.lean`) — composes the already-general
Phase-20 `exists_degree_le_two` (the `no_rigid_edge_count` + handshake counting core, floor
`3 ≤ bodyBarDim n`) with E2a's `two_le_degree_of_isKDof_zero` to pin the vertex's degree to
exactly `2`, without an explicit `TwoEdgeConnected` premise (matching E2's hypothesis list).
**E2a landed 2026-07-01**: min-degree ≥ 2 (`two_le_degree_of_isKDof_zero`) and the
connectivity companion (`preconnected_of_isKDof_zero`), both compositions of the already-landed
`twoEdgeConnected_of_isKDof_zero`/`two_le_degree_of_twoEdgeConnected` (Phase 22i) plus the new
general `preconnected_of_twoEdgeConnected` (`Molecular/Deficiency.lean`). E2 (KT Lemma 4.6, the
chain/cycle dichotomy leaf, the long pole) is now assessed to **split along its scoped sub-leaves
E2a–E2e (§(4.107.D)), one sub-leaf per commit** — see the *Lemma checklist*. **E4 landed
2026-07-01**: the `hextract`/`hcycle` binder reshape at the four
producer/spine sites (`Arms.lean` ×2 / `Realization.lean` / `Theorem55.lean`) is a zero-regression
lockstep — `hextract`'s conclusion is now the §(4.107.D) shape-2 disjunction
(`… ∨ ∃ cy : G.CycleData, cy.m ≤ n`) and the new green-modulo `hcycle` (E5's Lemma-5.4 brick) rides
alongside; the `d = 3` wrappers fill `hextract` via `Or.inl ∘ chainData_extract_d3` and `hcycle`
vacuously (`cy.vertexSet_ncard` + `cy.m ≤ 3 < 4 ≤ |V|` → `omega`). **E1 landed 2026-07-01**:
`Graph.CycleData` + `CycleData.vertexSet_ncard` (`Operations.lean`). ENTRY satisfiability SETTLED
(design §(4.107)): the `d = n` chain shape is source-faithful, but the chain-only `hextract` is
unsatisfiable at general `n` — **OD-1 settled = shape 2** (Lemma 5.4 load-bearing). ENTRY is the
pinned leaf ladder **E1 → E4 → E2 → E3 → E5** (exact signatures in §(4.107.D)); the two interface
leaves (E1, E4) are now landed, pinning the shape-2 disjunction in Lean before the long-pole
combinatorics. CHAIN-5 is done (dispatch discharged at general `k`); `hextract`/`hcycle` are
discharged at `n=3`; everything below the contract is landed (the `ChainData` record with
`d_eq : d = n` + `d_eq_kAdd`, the geometry arm, the `chainData_dispatch` router, the C.4 adapter).

## Lemma checklist (the §(4.107.D) ENTRY ladder)

- [x] **E1** `Graph.CycleData` record + `CycleData.vertexSet_ncard` (`Operations.lean`) — landed
  2026-07-01
- [x] **E4** the `hextract` binder reshape to the shape-2 disjunction + the new green-modulo
  `hcycle` at the four producer/spine sites (`Arms.lean` ×2 / `Realization.lean` / `Theorem55.lean`);
  `d=3` wrappers: `Or.inl ∘ chainData_extract_d3` + vacuous `hcycle` (`omega`) — landed 2026-07-01,
  zero-regression
- [ ] **E2** `Graph.chainData_or_cycleData_of_noRigid` — KT Lemma 4.6, the genuinely-new
  combinatorial leaf (the long pole); **SPLITS along its §(4.107.D) sub-leaves, one commit each**:
  - [x] **E2a** min-degree ≥ 2 + connectivity companion — `two_le_degree_of_isKDof_zero` /
    `preconnected_of_isKDof_zero` (`Molecular/Deficiency.lean`) — landed 2026-07-01
  - [x] **E2b** degree-2 existence — `exists_degree_eq_two_of_noRigid`
    (`ForestSurgery/Reduction.lean`) — landed 2026-07-01
  - [ ] **E2c** `cycle_isProperRigidSubgraph` (the general `triangle_isProperRigidSubgraph`)
  - [ ] **E2d** the maximal-chain walk-builder + KT (4.6)–(4.9) counting contradiction
  - [ ] **E2e** the numeric linking identity (`bodyBarDim n = n(n+1)/2`)
  - [ ] **E2-assembly** compose E2a–E2e into `chainData_or_cycleData_of_noRigid` itself
- [ ] **E3** `Graph.chainData_extract` — compose E2 + the landed Lemma-4.8 stack; discharges
  `hextract` at general `n`
- [ ] **E5** `PanelHingeFramework.cycle_realization` — the Lemma 5.4 brick discharging `hcycle`
  (risk #4, genuine new panel content: Crapo–Whiteley realization + the GAP-2-style genericity
  upgrade). Own detailed recon at build; candidate own-letter split at contact.

## Hand-off / next phase

**Smallest concrete next build commit: E2c — `cycle_isProperRigidSubgraph`** (the general
`triangle_isProperRigidSubgraph`: an induced cycle on `m ≤ bodyBarDim n` vertices inside a strictly
larger `G` is a proper rigid subgraph, via the deficiency count `isKDof_zero_of_cycle` generalizing
`isKDof_zero_of_triangle`; load-bearing for `vtx_inj`, §(4.107.D)). **E2 SPLITS along its
scoped sub-leaves E2a–E2e, one commit each** (assessed 2026-07-01, per the sizing-prologue
dispatch); **E2a landed** (`two_le_degree_of_isKDof_zero` / `preconnected_of_isKDof_zero`), **E2b
landed** (`exists_degree_eq_two_of_noRigid`, see *Decisions made*). After E2c: **E2d** the
maximal-chain walk-builder + the KT (4.6)–(4.9) counting contradiction, **E2e** the numeric linking
identity (`nlinarith` in `bodyBarDim n = n(n+1)/2`), then **E2-assembly** (compose E2a–E2e into
`Graph.chainData_or_cycleData_of_noRigid` itself). After E2: **E3**
(`Graph.chainData_extract`, composition of E2 + the landed Lemma-4.8 stack; discharges `hextract`
at general `n`), then **E5** (`PanelHingeFramework.cycle_realization`, the Lemma-5.4 brick
discharging `hcycle`; own detailed recon at build, candidate own-letter split).

The E4 interface is now in place: `hextract` returns the shape-2 disjunction and `hcycle` is carried
green-modulo, so E2/E3 land the chain-extractor discharge and E5 lands the cycle brick without
further binder churn.

**ENTRY satisfiability — SETTLED (2026-07-01, design §(4.107)).** KT Lemma 4.6 yields a chain of
length **exactly** `d = n` (never shorter — `d_eq : d = n` is right), OR a cycle on `≤ n`
vertices; the cycle branch is reachable under `hextract`'s premises at `n ≥ 4` (cycles
`4 ≤ |V| ≤ n`), so OD-1 = shape 2 is forced and `hcycle`/E5 is a genuine deliverable. The `hD`
floor lift dissolves (§(4.107.E): honest leaf floor `3 ≤ bodyBarDim n`, spine keeps 6).

## Frozen contract + tracking (do NOT change in 23g)

- **The frozen contract is §C.0–C.6** (invariant). No motive/IH change (§C.6): the chain data is
  purely combinatorial; the base `(G₁,q₁)` is the existing `HasGenericFullRankRealization` premise
  from the same 0-dof IH conjunct; the `d`-candidate splits `Gᵢ` are *smaller* minimal-0-dof graphs
  at the same dof — no higher-dof `G_v` pattern.
- **Carry forward GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
  orthogonal to the cert; tracked separately). ASSEMBLY = 23h; not opened here.

## Decisions made

### E2b — LANDED (2026-07-01)
`exists_degree_eq_two_of_noRigid` (`ForestSurgery/Reduction.lean`), at the honest floor
`3 ≤ bodyBarDim n`. Composes two already-landed pieces rather than re-deriving the count: the
general Phase-20 `exists_degree_le_two` (`no_rigid_edge_count`'s `davg < 3` count + the multigraph
handshake, already stated for any `IsMinimalKDof n k`, unifying `k := 0`) supplies `degree v ≤ 2`;
E2a's `two_le_degree_of_isKDof_zero` rules out `≤ 1`. The delta from the existing (older, more
general) `exists_degree_eq_two` is dropping its explicit `htec : TwoEdgeConnected` binder in favor
of deriving it from `hG : IsMinimalKDof n 0` directly (`hG.1`), matching E2's target hypothesis
list (no explicit 2EC premise, per §(4.107.B)). Zero friction: pure composition, first-try build.

### E2a — LANDED (2026-07-01)
Two compositions in `Molecular/Deficiency.lean`, both `IsKDof n 0 → …` at the honest floor
`1 ≤ bodyBarDim n` (§(4.107.E) discipline, not the ambient 3/6-floor): `two_le_degree_of_isKDof_zero`
(min-degree ≥ 2) and `preconnected_of_isKDof_zero` (connectivity companion). Both compose the
already-landed `twoEdgeConnected_of_isKDof_zero` (Phase 22i) with, respectively, the landed
`two_le_degree_of_twoEdgeConnected` and the new general `preconnected_of_twoEdgeConnected` (the
connected-component cut argument — mirrors `mulTilde_preconnected_of_isKDof_zero`'s cut-deficiency
technique for plain `G`, no `Fin (bodyHingeMult n)` edge-copy indexing needed). Zero friction: the
`TwoEdgeConnected`/`ConnBetween`/`cutEdges` infrastructure was already in place from Phase 22i.

### E4 — LANDED (2026-07-01)
The §(4.107.D) `hextract`/`hcycle` binder reshape — a CHAIN-5-style zero-regression lockstep in ONE
commit across the four producer/spine sites (`case_III_hsplit_producer_all_k` + its `k=2` wrapper,
`Arms.lean`; `case_III_realization_all_k`, `Realization.lean`; `theorem_55_minimalKDof_k_all_k`,
`Theorem55.lean`). `hextract`'s conclusion → `(⟨chain ∃⟩) ∨ ∃ cy : G.CycleData, cy.m ≤ n`; new
green-modulo `hcycle` (E5's Lemma-5.4 brick) rides alongside. `case_III_hsplit_producer_all_k`'s
chain arm: `obtain` → `rcases … | ⟨cy, hcym⟩` (right = `hcycle hV4' cy hcym`). `d=3` wrappers fill
`hextract` via `Or.inl ∘ chainData_extract_d3`, `hcycle` vacuously (`cy.vertexSet_ncard` → `omega`).
Blueprint untouched (`lem:case-III` → `case_III_realization` keeps its statement). Zero friction.

### E1 — LANDED (2026-07-01)
`Graph.CycleData` + `CycleData.vertexSet_ncard` (`Operations.lean`, own `/-! ##` section after
`end ChainData`; no decidability instances needed). Fields exactly the §(4.107.D) pinned list;
`vertexSet_ncard` via `Set.ncard_range_of_injective` + `Nat.card_fin` on `range vtx = V(G)`.
- **Below-contract deviation from the literal §(4.107.D) sketch:** the `link` field's cyclic
  successor is `vtx (i + ⟨1, by omega⟩)` (mod-`m` `Fin` add; `hm` in scope for the `by omega`),
  NOT the sketch's `vtx (i + 1)` — the OfNat `(1 : Fin m)` needs `NeZero m`, unavailable in a
  structure-field type. Same root cause as CHAIN-5's `Fin.mk` deviation → FRICTION *[idiom]
  carried-hypothesis field / `∃`-bundle indexing `cd.vtx ⟨2,_⟩`* (recurrence noted there).

### ENTRY satisfiability + OD-1/OD-2/OD-3 — SETTLED (2026-07-01, docs-only design pass)
Design §(4.107) is the full record. One-line verdicts: `d_eq : d = n` source-faithful (Lemma 4.6
chain branch = length exactly `d`); chain-only `hextract` (OD-1 shape 1) refuted at general `n`
(short-cycle counterexamples) → **shape 2 forced, Lemma 5.4 load-bearing** (`hcycle`/E5); KT 4.8(i)
already landed general (`splitOff_isMinimalKDof`), KT 4.6 not subsumed (new leaf E2); `hD` floor
lift dissolves. ENTRY re-scoped to the E1–E5 ladder (checklist above).

### CHAIN-5 — LANDED (`74bd9003`, 2026-07-01)
The C.0 lockstep reshape (`hcand`/`hdispatch` → the C.3 `(cd : G.ChainData n) (hd2 : 2 ≤ cd.d)`
shape across `case_III_hsplit_producer_all_k`/`case_III_hsplit_producer` (`Arms.lean`),
`case_III_realization_all_k` (`Realization.lean`), `theorem_55_minimalKDof_k_all_k` (`Theorem55.lean`))
+ the router wire-up composed in ONE commit. **Stronger than a pure reshape:** the dispatch is
*discharged* (not carried) via `fun cd hd2 hdef hsplitGP => chainData_dispatch cd hd2 hk1 hn hG hV3
hSimple hIH hG.1 hdef hsplitGP` inside `case_III_realization_all_k`, so 23f's router is now LIVE.
Signature deltas (all below §C.0–C.6, no motive/IH change): DROPPED `hdispatch`; ADDED
`hn : bodyBarDim n = screwDim k` (threaded from the spine) + `hextract`. The `d=3` wrappers
(`case_III_realization` / `theorem_55_minimalKDof_k`) fill `hextract` via `chainData_extract_d3`.
- **Below-contract deviation from the literal §C.3 shape:** the field uses `cd.vtx ⟨i, by omega⟩`
  (the router's `Fin.mk` form) + an explicit `hd2` binder, NOT the literal `cd.vtx 1` (OfNat) —
  `(1 : Fin (cd.d+1))` is not defeq to `⟨1,_⟩` at general `cd.d`. → FRICTION *[idiom]
  carried-hypothesis field / `∃`-bundle indexing `cd.vtx ⟨2,_⟩`*.
- **§C.4 `d=3` adapter** `chainData_of_exists_chain_data` (`Reduction.lean`, landed `9b65f960`):
  packages the `d=3` 4-tuple into a `ChainData` (`vtx = ![b,v,a,c]`, `edge = ![e_b,eₐ,e_c]`,
  `d_eq : 3 = n`); `chainData_extract_d3` then transports the `v₁`-split facts across the `a,b`-swap
  (`splitOff_swap_ab`).

## LIVE — DO NOT delete / DO NOT plan to delete
- `caseIIICandidate` + its API — the honest engine consumes it via `case_III_realization_of_rank`
  ← `case_III_arm_realization`.
- The non-aug edge-path helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in
  `RigidityMatrix/Concrete.lean`.

(Distinct from the retired `_aug` fork, fully deleted across 23f's four deletion commits.)

## OUT-OF-SCOPE `d=3`-era orphans (later sweep / 23g housekeeping)
- `interior_hsplitGP` (`CaseIII/Realization.lean`).
- `case_III_realization_of_line` (`CaseIII/Arms.lean`).
