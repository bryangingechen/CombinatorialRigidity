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

Next concrete build step: **E1, the `CycleData` record** (see *Hand-off*). The ENTRY
satisfiability check ran 2026-07-01 (design §(4.107)): the `d = n` chain shape is source-faithful,
but the chain-only `hextract` is unsatisfiable at general `n` — **OD-1 settled = shape 2** (the
§C.5 disjunction; Lemma 5.4 is load-bearing). ENTRY is now the pinned leaf ladder
**E1 → E4 → E2 → E3 → E5** (exact signatures in §(4.107.D)). CHAIN-5 is done (dispatch discharged
at general `k`); `hextract` is discharged at `n=3` by `Graph.chainData_extract_d3`
(`Reduction.lean`); everything below the contract is landed (the `ChainData` record with
`d_eq : d = n` + `d_eq_kAdd`, the geometry arm, the `chainData_dispatch` router, the C.4 adapter).

## Lemma checklist (the §(4.107.D) ENTRY ladder)

- [ ] **E1** `Graph.CycleData` record + `CycleData.vertexSet_ncard` (`Operations.lean`) — small
- [ ] **E4** the `hextract` binder reshape to the shape-2 disjunction + the new green-modulo
  `hcycle` at the three sites (`Arms.lean`/`Realization.lean`/`Theorem55.lean`); `d=3` wrappers:
  `Or.inl ∘ chainData_extract_d3` + vacuous `hcycle` (`omega`) — zero-regression
- [ ] **E2** `Graph.chainData_or_cycleData_of_noRigid` — KT Lemma 4.6, the genuinely-new
  combinatorial leaf (sub-leaves E2a–E2e scoped in §(4.107.D); the long pole)
- [ ] **E3** `Graph.chainData_extract` — compose E2 + the landed Lemma-4.8 stack; discharges
  `hextract` at general `n`
- [ ] **E5** `PanelHingeFramework.cycle_realization` — the Lemma 5.4 brick discharging `hcycle`
  (risk #4, genuine new panel content: Crapo–Whiteley realization + the GAP-2-style genericity
  upgrade). Own detailed recon at build; candidate own-letter split at contact.

## Hand-off / next phase

**Smallest concrete next build commit: E1 — the `CycleData` record** (`Operations.lean`, next to
`ChainData`; the §(4.107.D) field list is the pinned shape, plus the `vertexSet_ncard` accessor
that makes the `d=3` `hcycle` fill vacuous). Then E4 (the lockstep binder reshape, CHAIN-5-style,
zero-regression), then E2 (the long pole — assess whether E2 is one session or splits along
E2a–E2e once E4 closes), then E3, then E5.

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
