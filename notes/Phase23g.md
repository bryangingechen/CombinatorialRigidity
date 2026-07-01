# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** in progress (opened 2026-07-01, docs-only). The `ENTRY` sub-phase of
the Case III general-`d` program. 23f closed the chain dispatch: the router
`PanelHingeFramework.chainData_dispatch` (`CaseIII/Realization.lean`) + both branches
(`chainData_dispatch_{interior,floor}_of_discriminator`) + the firing producer
`chainData_fire_discriminator` all landed axiom-clean — but **unused**: the C.0-trio
`hcand`/`hdispatch` field is still the `d=3` 8-tuple and no `ChainData` *value* exists at
general `d`. 23g gives the router a live consumer. `d=3` stays fully green throughout via
the untouched honest `k=2`-spine engine. Authoritative scoping: `notes/Phase23-design.md`
§C.0–C.6 (the frozen CHAIN↔ENTRY contract) + §C.2/§C.5; the `d=3` map is §C.4. Program map:
`notes/MolecularConjecture.md`. `ASSEMBLY` = **23h** (later sub-phase).

## Current state

Next concrete build step: the §C.4 `d=3` `ChainData`-constructor adapter (see *Hand-off*).
Everything below the contract is landed: the `ChainData` record (`Operations.lean:1301`,
matching C.1, with the adopted `d_eq : d = n` field per design §(4.11)/(4.32) + the
`ChainData.d_eq_kAdd` bridge), the whole geometry arm, and the `chainData_dispatch` router
(which already takes `cd : G.ChainData n`). What is NOT yet done is the reshape that connects
them: the C.0 lockstep trio still carries the `d=3` 8-tuple premise bundle, and
`exists_chain_data_of_noRigid` still returns only the `d=3` 4-tuple.

## Layer plan — two coupled pieces (CHAIN-5 + ENTRY)

Per §C.0 the reshape is **THREE decls changing in lockstep**, all carrying the identical
premise bundle (verified byte-identical): the ENTRY extractor / the producer
`case_III_hsplit_producer_all_k.hcand` (`Arms.lean:853`, `931`) / the consumer
`case_III_realization_all_k.hdispatch` (`Realization.lean:2674`) +
`theorem_55_minimalKDof_k_all_k.hdispatch` (`Theorem55.lean:2548`). Changing the
consumer `hdispatch` *type* forces the producer `hcand` and the ENTRY output to typecheck
against the same shape in the same build. **CHAIN-5 and ENTRY are therefore coupled.**

### CHAIN-5 (contract §C.3 consumer reshape + §C.4 `d=3` wrapper)
- [ ] Reshape the 8-tuple `hcand`/`hdispatch` premise-bundle field → a single
  `(cd : G.ChainData n)` (C.3 shape), wiring the LANDED-but-unused router
  `chainData_dispatch` into the `hdispatch` slot. C.3 target shape (design §C.3):
  `hdispatch : ∀ (cd : G.ChainData n), (G.splitOff (cd.vtx 1) (cd.vtx 0) (cd.vtx 2) cd.e₀).deficiency n = 0
  → HasGenericFullRankRealization k n (G.splitOff (cd.vtx 1) (cd.vtx 0) (cd.vtx 2) cd.e₀)
  → HasGenericFullRankRealization k n G`.
- [ ] The §C.4 `d=3` zero-regression wrapper: the record↔tuple map (design §C.4 table).
  `G₁ = splitOff (vtx 1) (vtx 0) (vtx 2) e₀ = splitOff v b a e₀ = splitOff v a b e₀`
  (`splitOff` symmetric in its `a,b` args, `splitOff_isLink`). `(vtx 0,1,2,3) = (b,v,a,c)`;
  `(edge 0,1,2) = (e_b, eₐ, e_c)`; `deg_two` at `i=1`/`i=2` = the `hclv`/`hcla` closures.
  `d=3` proof unchanged — an adapter from the 4-tuple to the `ChainData` projection; the
  wrappers fill `hdispatch` from the existing `case_III_candidate_dispatch` via this map.

### ENTRY (contract §C.2)
- [ ] Reshape `exists_chain_data_of_noRigid` (`Induction/ForestSurgery/Reduction.lean:383`,
  returns only the `d=3` 4-tuple today) → the general-`d` extractor producing `G.ChainData n`.
  Content: KT **Lemma 4.6** (chain-or-cycle) + **Lemma 4.8** (split-off minimality) + the
  **Lemma 5.4** cycle branch per §C.5's OD-1 division of labor. Target signature = design §C.2.
- [ ] The `hD` floor lift: the `d=3` extractor's `6 ≤ bodyBarDim n` (Reduction.lean:385) is
  the `d=3` regime; the general floor is the body-bar-dim ↔ chain-length relation (a separate
  ENTRY obligation, §C.2 / §"CHAIN"(d)).

**OD-1 (C.5, ENTRY-build decision, not now):** the extractor owns the chain/cycle dichotomy
(Lemma 4.6). Two honest shapes — (1) chain-only, cycle branch base-folded (the contract's
*default*, as `d=3` dodged 5.4); (2) a disjunction routing the cycle disjunct to a Lemma 5.4
short-cycle realization brick. **CHAIN-5's `hdispatch` only ever sees a `ChainData`** under
either shape; the dispatch signature is invariant. ENTRY picks the shape at build.

## Frozen contract + tracking (do NOT change in 23g)

- **The frozen contract is §C.0–C.6** (invariant). No motive/IH change (§C.6): the chain data is
  purely combinatorial; the base `(G₁,q₁)` is the existing `HasGenericFullRankRealization`
  premise pulled from the same 0-dof IH conjunct; the `d`-candidate splits `Gᵢ` are *smaller*
  minimal-0-dof graphs at the same dof — no higher-dof `G_v` pattern.
- **The C.3 `hIH` consume-shape add** (approved, lands with the router) is the general
  `(k':ℤ)` IH already in scope at the spine — NOT a motive/IH-strength change.
- **Carry forward GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
  orthogonal to the cert; tracked separately). ASSEMBLY = 23h; not opened here.

## Blockers / open questions

- **Leaf-most ordering (build-time confirm).** The §C.4 `d=3` `ChainData`-constructor adapter
  is purely additive (builds a new value from `exists_chain_data_of_noRigid`'s output; no
  signature change) so it compiles on the still-green tree without triggering the three-decl
  lockstep — the recommended first commit (see *Hand-off*). Whether it is *strictly* leaf-most
  vs. landing the CHAIN-5 consumer reshape first cannot be confirmed without a build: the
  lockstep coupling means the type reshape itself can't land partially. Check by building the
  adapter first; if the `d=3` map has a hidden dependency on the reshaped `hdispatch` type,
  fall back to landing the C.3 consumer type + adapter in one commit.

## Hand-off / next phase

**Smallest concrete first build commit: the §C.4 `d=3` `ChainData`-constructor adapter.**
Build a helper (in `Operations.lean` beside the record, or `Reduction.lean` beside the
extractor) that packages the `d=3` `exists_chain_data_of_noRigid` 4-tuple output
(`v,a,b,c,eₐ,e_b,e_c` + links + degree-2 closures) into a `d=3` `ChainData` value via the C.4
map (`d := 3`, `vtx = ![b,v,a,c]`, `edge = ![e_b,eₐ,e_c]`, `deg_two` from `hclv`/`hcla`,
`d_eq : 3 = n` from the ambient `n = 3` regime). Purely additive, gate-verified
(build + lint + axiom-clean), no signature change to the C.0 lockstep trio — it proves the
`d=3` record↔tuple map in isolation and de-risks the CHAIN-5 reshape that consumes it.

*Why this and not the CHAIN-5 consumer reshape first:* the reshape changes the `hdispatch`
*type* on the C.0 trio, which per §C.0 forces the producer `hcand` and (eventually) the ENTRY
output to move in lockstep — a larger, coupled commit. The adapter is the one piece that lands
green *without* touching a signature, so it is the leaf-most step (modulo the build-time
confirm above).

## LIVE — DO NOT delete / DO NOT plan to delete

- `caseIIICandidate` + its API — the honest engine consumes it via
  `case_III_realization_of_rank` ← `case_III_arm_realization`.
- The non-aug edge-path helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in
  `RigidityMatrix/Concrete.lean`.

(These are distinct from the retired `_aug` fork, fully deleted across 23f's four deletion commits.)

## OUT-OF-SCOPE `d=3`-era orphans (later sweep / 23g housekeeping)

Two self-only orphans flagged for a later sweep (NOT the `_aug` fork — self-referential only):
- `interior_hsplitGP` (`CaseIII/Realization.lean:814`).
- `case_III_realization_of_line` (`CaseIII/Arms.lean:568`).
