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

Next concrete build step: the CHAIN-5 consumer reshape (the C.3 `hdispatch` type change wiring
the LANDED `chainData_dispatch` router into the C.0 lockstep trio — see *Hand-off*). The §C.4 `d=3`
`ChainData`-constructor adapter is now LANDED: `Graph.chainData_of_exists_chain_data`
(`Reduction.lean:567`, right after the `d=3` extractor `exists_chain_data_of_noRigid`) packages the
`d=3` 4-tuple output + a fresh `e₀ ∉ E(G)` into a `G.ChainData n` value via the C.4 map
(`d := 3`, `vtx := ![b, v, a, c]`, `edge := ![e_b, eₐ, e_c]`, `d_eq : 3 = n` from `hn : n = 3`),
axiom-clean, purely additive (no signature change to the C.0 trio). This proves the C.4 record↔tuple
map in isolation, de-risking the CHAIN-5 reshape that consumes it.

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
- [x] The §C.4 `d=3` zero-regression wrapper (the record↔tuple map, design §C.4 table): LANDED as
  `Graph.chainData_of_exists_chain_data` (`Reduction.lean:567`). `(vtx 0,1,2,3) = (b,v,a,c)`;
  `(edge 0,1,2) = (e_b, eₐ, e_c)`; `deg_two` at `i=1`/`i=2` = the `hclv`/`hcla` closures (both
  closed by defeq — `![…] (⟨i,_⟩:Fin 3).castSucc` reduces to the vertex without simp);
  `d_eq : 3 = n` from `hn : n = 3`. `edge_inj` needs `e_b ≠ e_c` (derived here via
  `IsLink.eq_and_eq_or_eq_and_eq` + `b ≠ a`/`b ≠ c`, since the extractor gives only `eₐ ≠ e_b`/
  `eₐ ≠ e_c`). `e₀` is a wrapper argument (the extractor does not produce it — the `d=3` producer
  picks it fresh via `hfresh`). STILL TODO: wire this adapter into the `hdispatch` slot alongside
  the CHAIN-5 consumer reshape (`splitOff v a b e₀ = splitOff v b a e₀` by `splitOff` `a,b`-symmetry
  bridges the C.4 `splitOff (vtx 1) (vtx 0) (vtx 2)` to the landed bundle's `splitOff v a b`).

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

- **Leaf-most ordering — RESOLVED.** The §C.4 `d=3` `ChainData`-constructor adapter landed purely
  additively (a new `def` building a value from the extractor's 4-tuple output + a fresh `e₀`; no
  signature change), gate-verified green on the still-C.0-8-tuple tree — confirming it is strictly
  leaf-most, no hidden dependency on the reshaped `hdispatch` type. The CHAIN-5 consumer reshape can
  now proceed as its own (coupled, C.0-lockstep) commit.

## Hand-off / next phase

**Smallest concrete next build commit: the CHAIN-5 consumer reshape (C.3).** Reshape the 8-tuple
`hdispatch`/`hcand` premise-bundle field on the C.0 lockstep trio (the ENTRY extractor / the
producer `case_III_hsplit_producer_all_k.hcand` `Arms.lean:853` + `931` / the consumer
`case_III_realization_all_k.hdispatch` `Realization.lean:2674` + `theorem_55_minimalKDof_k_all_k.hdispatch`
`Theorem55.lean:2548`) to a single `(cd : G.ChainData n)` in the C.3 shape (design §C.3), wiring the
LANDED-but-unused router `chainData_dispatch` into the `hdispatch` slot. Per §C.0 the three decls
move in lockstep (changing the consumer `hdispatch` *type* forces the producer `hcand` and the ENTRY
output), so this is one coupled commit. The `d=3` wrappers keep zero-regression by filling
`hdispatch` from the existing `case_III_candidate_dispatch` **through the now-landed C.4 adapter**
`chainData_of_exists_chain_data`: the adapter turns the `d=3` extractor 4-tuple into a `ChainData`,
and `splitOff v a b e₀ = splitOff v b a e₀` (`splitOff` `a,b`-symmetry, `splitOff_isLink`) bridges the
C.3 `splitOff (cd.vtx 1) (cd.vtx 0) (cd.vtx 2) cd.e₀` to the bundle's `splitOff v a b e₀`.

*If the coupled reshape is too large for one sitting,* the fallback per §C.0 is to land the C.3
consumer `hdispatch` type + the `d=3` wrapper adapter-consumption in one commit and let the producer
`hcand` / ENTRY output follow — but the lockstep means the type reshape cannot land *partially*
(a half-reshaped trio will not typecheck), so shrink by *scope* (defer ENTRY's general-`d` extractor
to a later commit, keeping the `d=3` wrapper), not by leaving a signature half-changed.

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
