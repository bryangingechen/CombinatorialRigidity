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

**CHAIN-5 is LANDED (the dispatch is now discharged at general `k`).** The C.0 lockstep reshape +
the router wire-up composed in one commit. The Case-III chain dispatch is no longer a carried
`hdispatch` hypothesis: the router `chainData_dispatch` DISCHARGES the reshaped C.3 `hcand`/`hdispatch`
inside `case_III_realization_all_k` (`Realization.lean`) via
`fun cd hd2 hdef hsplitGP => chainData_dispatch cd hd2 hk1 hn hG hV3 hSimple hIH hG.1 hdef hsplitGP`.
The single remaining green-modulo hypothesis is now the **ENTRY extractor** `hextract` (design §C.2):
a per-`G` producer of a length-`n` `ChainData` witness + the `v₁`-split's
minimality/simplicity/measure data. The `d=3` line stays zero-regression: `hextract` is discharged at
`n=3` by the new `Graph.chainData_extract_d3` (`Reduction.lean`, the landed `d=3` extractor
`exists_chain_data_of_noRigid` + the C.4 adapter `chainData_of_exists_chain_data` + the
`splitOff_swap_ab` `(a,b)`-bridge). Whole chain builds sorry-free + axiom-clean
(`propext`/`Classical.choice`/`Quot.sound` only).

Next concrete build step: **ENTRY** — discharge the carried `hextract` at general `n` (see *Hand-off*).

Key signature deltas (all below the frozen contract §C.0–C.6; no motive/IH change):
- `case_III_hsplit_producer_all_k` (`Arms.lean`): `hcand` reshaped to the C.3 `ChainData` shape
  (`(cd) (hd2 : 2 ≤ cd.d) → hdef → hsplitGP → …`); NEW carried `hextract` (§C.2 ENTRY interface,
  before `hcand`); the chain arm's body now `obtain`s `cd`+bundle from `hextract` and feeds the
  reshaped `hcand`. `hfresh` no longer consumed here (ENTRY owns freshness) → renamed `_hfresh`.
- `case_III_realization_all_k` (`Realization.lean`): DROPPED `hdispatch`; ADDED `hn : bodyBarDim n =
  screwDim k` + `hextract`; fills the producer's `hcand` via the router.
- `theorem_55_minimalKDof_k_all_k` (`Theorem55.lean`): its carried `hdispatch` → `hextract` (per-`G`);
  passes `hn` (already carried) + `hextract` down.
- `d=3` wrappers `case_III_realization` / `theorem_55_minimalKDof_k`: fill `hextract` via
  `chainData_extract_d3` (deriving `n=3` from `hn`); no `case_III_candidate_dispatch` re-discharge.

Everything below the contract is landed: the `ChainData` record (`Operations.lean:1301`, with
`d_eq : d = n` + the `d_eq_kAdd` bridge), the geometry arm, the `chainData_dispatch` router, and the
C.4 adapter `chainData_of_exists_chain_data`.

## Layer plan — two coupled pieces (CHAIN-5 + ENTRY)

Per §C.0 the reshape is **THREE decls changing in lockstep**, all carrying the identical
premise bundle (verified byte-identical): the ENTRY extractor / the producer
`case_III_hsplit_producer_all_k.hcand` (`Arms.lean:853`, `931`) / the consumer
`case_III_realization_all_k.hdispatch` (`Realization.lean:2674`) +
`theorem_55_minimalKDof_k_all_k.hdispatch` (`Theorem55.lean:2548`). Changing the
consumer `hdispatch` *type* forces the producer `hcand` and the ENTRY output to typecheck
against the same shape in the same build. **CHAIN-5 and ENTRY are therefore coupled.**

### CHAIN-5 (contract §C.3 consumer reshape + §C.4 `d=3` wrapper) — LANDED
- [x] Reshape the 8-tuple `hcand`/`hdispatch` premise-bundle field → the C.3 `(cd : G.ChainData n)
  (hd2 : 2 ≤ cd.d)` shape and DISCHARGE it via the router `chainData_dispatch` inside
  `case_III_realization_all_k` (no longer a carried hypothesis). **Deviation from the design's literal
  §C.3 shape (below-contract, adopted to dodge a defeq wall):** the field uses `cd.vtx ⟨i, by omega⟩`
  (the router's `Fin.mk` form) + an explicit `hd2` binder, NOT the literal `cd.vtx 1` (OfNat) — the
  spike proved `(1 : Fin (cd.d+1))` is not defeq to `⟨1,_⟩` at general `cd.d` (FRICTION *[idiom] …
  `cd.vtx ⟨2,_⟩` needs `2 ≤ cd.d` in scope …*). `hn`/`hd2` sourcing: `hn` added to
  `case_III_realization_all_k`'s signature (threaded from the spine, below-contract); `hd2` comes from
  the ENTRY extractor's bundle.
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

- **CHAIN-5 ordering — RESOLVED (LANDED).** The reshape composed in one commit: the router discharges
  the reshaped dispatch, the `d=3` line stays green via `chainData_extract_d3`. The only remaining
  green-modulo hypothesis is the ENTRY extractor `hextract` (below).
- **`hn` reachability at ASSEMBLY (23h) — RESOLVED here.** CHAIN-5 already threaded `hn` down to
  `case_III_realization_all_k` and wired the router, so the dispatch is discharged at general `k`
  *now*, not deferred to ASSEMBLY. ASSEMBLY's remaining job is to discharge the carried producers
  (base/cut/Case-I/M4/`hextract`) at general `k`, not to wire the Case-III dispatch.

## Hand-off / next phase

**Smallest concrete next build commit: ENTRY — discharge the carried `hextract` at general `n`.**
The Case-III chain dispatch is landed (CHAIN-5 done); the single Case-III green-modulo hypothesis is
now `hextract` (design §C.2), carried on `case_III_hsplit_producer_all_k` / `case_III_realization_all_k`
(`Realization.lean`) and `theorem_55_minimalKDof_k_all_k` (`Theorem55.lean`), and discharged at `n=3`
by `chainData_extract_d3` (`Reduction.lean`). ENTRY replaces the `n=3` discharge with the genuinely-new
general-`n` extractor:
- Reshape `exists_chain_data_of_noRigid` (`Reduction.lean`, returns only the `d=3` 4-tuple today) →
  the general-`n` `ChainData` producer (design §C.2), content = KT **Lemma 4.6** (chain-or-cycle) +
  **Lemma 4.8** (split-off minimality) + the **Lemma 5.4** cycle branch per §C.5's OD-1 division of
  labor. Then build the general-`n` `chainData_extract_*` (the analog of `chainData_extract_d3`) and
  point the carried `hextract` at it, dropping the `n=3` restriction.
- The `hD` floor lift: the `d=3` extractor's `6 ≤ bodyBarDim n` (Reduction.lean) is the `d=3` regime;
  the general floor is the body-bar-dim ↔ chain-length relation (a separate ENTRY obligation).

The `hextract` interface shape (§C.2, below-contract): `4 ≤ |V(G)| → hnoRigid → ∃ (cd) (hd2 : 2 ≤ cd.d),
(the v₁-split's IsMinimalKDof/Simple/measure facts)`. It already isolates the whole ENTRY obligation as
a single named hypothesis, so ENTRY is a self-contained leaf: build the general-`n` extractor, thread
it into `hextract`, no dispatch/contract changes.

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
