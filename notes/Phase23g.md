# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** in progress (opened 2026-07-01). The `ENTRY` sub-phase of the Case III
general-`d` program. **CHAIN-5 landed 2026-07-01** (`74bd9003`) — the 23f router
`chainData_dispatch` now *discharges* the Case-III chain dispatch at general `k`; the single
remaining Case-III green-modulo hypothesis is the **ENTRY extractor** `hextract` (design §C.2),
discharged at `n=3` today. `d=3` stays fully green throughout. Authoritative scoping:
`notes/Phase23-design.md` §C.0–C.6 (frozen CHAIN↔ENTRY contract) + §C.2/§C.5; the `d=3` map is
§C.4. Program map: `notes/MolecularConjecture.md`. `ASSEMBLY` = **23h** (later sub-phase).

## Current state

Next concrete build step: **ENTRY** — discharge the carried `hextract` at general `n` (see
*Hand-off*). CHAIN-5 is done: the C.0 lockstep reshape + router wire-up composed in one commit,
so the Case-III dispatch is no longer a carried hypothesis. The only Case-III green-modulo
hypothesis left is `hextract` (§C.2 ENTRY interface: a per-`G` producer of a length-`n`
`ChainData` witness + the `v₁`-split's minimality/simplicity/measure), discharged at `n=3` by
`Graph.chainData_extract_d3` (`Reduction.lean`). Everything else below the contract is landed: the
`ChainData` record (`Operations.lean`, `d_eq : d = n` + the `d_eq_kAdd` bridge), the geometry arm,
the `chainData_dispatch` router, and the C.4 adapter `chainData_of_exists_chain_data`.

## Hand-off / next phase

**Smallest concrete next build commit: ENTRY — discharge the carried `hextract` at general `n`.**
`hextract` (design §C.2) is carried on `case_III_hsplit_producer_all_k` (`Arms.lean`) /
`case_III_realization_all_k` (`Realization.lean`) and `theorem_55_minimalKDof_k_all_k`
(`Theorem55.lean`), discharged at `n=3` by `chainData_extract_d3` (`Reduction.lean`). Its interface
(§C.2, below-contract): `4 ≤ |V(G)| → hnoRigid → ∃ (cd : G.ChainData n) (hd2 : 2 ≤ cd.d), (the
v₁-split's IsMinimalKDof/Simple/measure facts)`. It isolates the whole ENTRY obligation as one
named hypothesis, so ENTRY is a self-contained leaf: build the general-`n` extractor, thread it
into `hextract`, no dispatch/contract changes.

- Reshape `exists_chain_data_of_noRigid` (`Reduction.lean` — general-`n` signature but length-3
  4-tuple output today) → the general-`n` `ChainData` producer (design §C.2): KT **Lemma 4.6**
  (chain-or-cycle) + **Lemma 4.8** (split-off minimality) + the **Lemma 5.4** cycle branch per
  §C.5's OD-1. Then build the general-`n` `chainData_extract_*` (the analog of `chainData_extract_d3`)
  and point `hextract` at it, dropping the `n=3` restriction.
- The `hD` floor lift: the `d=3` `6 ≤ bodyBarDim n` is the `d=3` regime; the general floor is the
  body-bar-dim ↔ chain-length relation (a separate ENTRY obligation, §C.2 / §"CHAIN"(d)).

**OD-1 (C.5, ENTRY-build decision):** the extractor owns the chain/cycle dichotomy (Lemma 4.6).
Two honest shapes — (1) chain-only, cycle base-folded (the contract's *default*, as `d=3` dodged
5.4); (2) a disjunction routing the cycle disjunct to a Lemma 5.4 short-cycle realization brick.
CHAIN-5's dispatch only ever sees a `ChainData` under either; ENTRY picks the shape at build.

⚠️ **ENTRY satisfiability — confirm as the FIRST ENTRY step.** `hextract` asks for a length-`n`
chain (`cd.d = n` via `ChainData.d_eq`), but the landed extractor produces only a length-3 config.
The `d=n` chain shape is design-settled (§C.1/§C.2, source-verified vs KT §6.4.2 + adjudicated by a
diverse-lens pair, design §(4.11)/(4.32)) — but before building, re-confirm KT Lemma 4.6 actually
yields a length-`n` chain at general `n` (a satisfiability check against the real object; if it
yields a *shorter* chain the `d_eq : d = n` field is too strong and the interface needs revisiting).

## Frozen contract + tracking (do NOT change in 23g)

- **The frozen contract is §C.0–C.6** (invariant). No motive/IH change (§C.6): the chain data is
  purely combinatorial; the base `(G₁,q₁)` is the existing `HasGenericFullRankRealization` premise
  from the same 0-dof IH conjunct; the `d`-candidate splits `Gᵢ` are *smaller* minimal-0-dof graphs
  at the same dof — no higher-dof `G_v` pattern.
- **Carry forward GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
  orthogonal to the cert; tracked separately). ASSEMBLY = 23h; not opened here.

## Decisions made

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
