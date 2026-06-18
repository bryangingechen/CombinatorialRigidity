# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 are CLOSED.** CHAIN-4 is in progress: two bricks now landed —
`exists_independent_perp_pair_gen` (the general-`d` second-normal-through-a-line) and, this commit
(2026-06-18), the general-`d` kept-points tabulation `omitTwoExtensor_eq_extensor_kept_gen`
(`RigidityMatrix/Claim612.lean`), with both `Fin 4` lemmas (`omitTwoExtensor_eq_extensor_kept`,
`omitTwoExtensor_homogenize_eq_extensor_kept`) re-derived as `e := 2` wrappers (no blueprint pin,
both callers unchanged). CHAIN-1 = the `ιc`-block candidate augment +
`…candidateBlock_swap` (`RigidityMatrix/Basic.lean`), graph-free over `ScrewSpace k`. CHAIN-3 = the
general-`d` per-line join=meet duality `extensor_join_proportional_complementIso_meet`
(`MeetHodge.lean`), the `⋀^{d−1}W`-is-a-line route (full per-leaf detail in *Decisions made* +
`notes/Phase23-design.md` §"CHAIN"(f)/(h); the d=3 `complementIso_smul_eq_extensor_join` stays the
GREEN d=3 wrapper). **CHAIN-2/4(rest)/5 remain** (CHAIN-5 gated by the ENTRY-contract reshape). The
integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase
boundary; codes-until-open).

**Orientation.** This is the **23b (CHAIN layer)** sub-phase work log — the
*rolling* state + hand-off for the active layer only. The cross-phase
**plan/guidance** (sub-phase division, sequence, open decisions, sources) is the
canonical job of `notes/Phase23-design.md`; the **detailed leaf-level recon of
CHAIN** is its §"CHAIN — detailed leaf-level recon" ((a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions). The
program map is `notes/MolecularConjecture.md`. **Sub-phase naming convention:**
the layers are tracked by stable **codes** — `CARRIER`(=23a, closed), `CHAIN`(=
this 23b), `ENTRY`, `ASSEMBLY`; a letter + work log is minted when a layer
opens, so a later split costs no renumber-churn. `23b` is the minted letter for
CHAIN; ENTRY/ASSEMBLY stay code-only until their turn.

## Current state

**Next build = CHAIN-4a** (`exists_homogeneousIncidence_of_normals_gen` at `Fin (k+1) → Fin (k+2)`,
`RigidityMatrix/Claim612.lean`): the OD-4 sub-leaf, a **clean lift** of the d=3 body
(`Claim612.lean:427`) — `(k+1) × (k+2)` row-matrix surjectivity (`LinearIndependent.rank_matrix` ⟹
`mulVecLin` surjective ⟹ preimages of the `k+1` standard targets) gives the incidence pattern, the
nonzero common-perp `pbar 0` from the **already-general** `exists_ne_zero_dotProduct_eq_zero` (m=k+1),
and LI of `pbar` by the triangular pairing argument. **No genericity device, no alg-independence**
(OD-4 verdict below). Exact signature + the three remaining CHAIN-4 leaves (4b/4c/4d) in
`notes/Phase23-design.md` §(j); `Fin 4` lemma becomes the `k:=2` wrapper.

**OD-4 — RESOLVED this commit (2026-06-18, design-pass): existence/homogeneous route, alg-independence
NOT forced** (full verdict + KT p.698-vs-landed-source reasoning in `notes/Phase23-design.md` §(i);
Decisions-made below). The eq.-(6.67) `dim span ⋃ C(Lᵢ) = D` finish lifts as a mechanical numeral
generalization of the green d=3 bricks — `span_omitTwoExtensor_eq_top` (already general-`k`, only hyp
`LinearIndependent ℝ pbar`, via Lemma 2.1) drives the D-span off **linear** independence of `d+1`
**homogeneous** vectors, never KT's *affine*-independent points / `(d−j)`-flat-in-union (the
alg-independence consequence KT states is on the route the formalization sidesteps, §1.42 R1-affine).
The row #106 cross-product construction (whose non-generalization motivated the prior "forced" lean)
is **dead — zero live call sites**. No new `AlgebraicIndependent` lemma needed; site (b)/eq.-(6.67)
is **not** an alg-independence site (only site (a), the nested seed-rank transfer, stays live,
unchanged). One build-time residual flagged (the per-join panel-membership must close combinatorially
from the orthogonality hyps — CHAIN-4b's job).

**Prior CHAIN-4 brick — LANDED 2026-06-18: the general-`d` kept-points tabulation.**
`omitTwoExtensor_eq_extensor_kept_gen` (`RigidityMatrix/Claim612.lean`): ambient `Fin (e+2)`
(`d = e+1`), for the omitted pair `q` the join `omitTwoExtensor pbar (ne_of_lt q.2)` is the point-join
`extensor (fun k => pbar (emb k))` of the `e = d−1` increasing complement indices
`emb : Fin e ↪o Fin (e+2)`, each `≠ q.1, q.2` (KT p. 698; at `d=3`, `e=2`, the two-point pair). Both
`Fin 4` lemmas re-derived as `e := 2` wrappers; no blueprint pin, callers unchanged.

**Prior CHAIN-4 brick (2026-06-18): the general-`d` "second normal through a line".**
`exists_independent_perp_pair_gen` (`RigidityMatrix/Claim612.lean`): ambient `Fin (k+2)` (`k = d−1`),
`2 ≤ k`, two points of a line both `⬝ᵥ`-⊥ to one normal `n_u ≠ 0` ⟹ a second independent normal `n'`
(rank–nullity on the two-functional kernel `≥ k ≥ 2 > 1`, proper superspace via `SetLike.exists_of_lt`
+ `LinearIndependent.pair_iff'`). `Fin 4` `exists_independent_perp_pair` = the `k := 2` wrapper.

**CHAIN-1 — CLOSED** (2026-06-18): the `ιc`-block candidate augment
(`linearIndependent_sum_pinned_block_augment_block` + `…_augment_candidateRow_block`) + the eq.-6.62
row-correspondence swap (`…candidateBlock_swap`), all `RigidityMatrix/Basic.lean`, graph-free over
`ScrewSpace k`; the single-`Unit` predecessors re-derived as `ιc := Unit` corollaries (blueprint pins
unmoved). Full detail in *Decisions made*.

**CHAIN-3 is CLOSED** (2026-06-17): the general-`d` per-line join=meet duality
`extensor_join_proportional_complementIso_meet` (`MeetHodge.lean`), `∃ c, c • complementIso(j:=2)
⟨extensor n,_⟩ = ⟨extensor p,_⟩` — the `⋀^{d−1}W`-is-a-line route (`W = {n 0,n 1}^⊥`, both point-join
and panel-meet in the line `range(⋀^k W ↪)`, proportionalized off the nonzero panel-meet). Full
per-leaf detail (h-0…h-4) in *Decisions made* + `notes/Phase23-design.md` §"CHAIN"(f)/(h); the d=3
`complementIso_smul_eq_extensor_join` stays the GREEN d=3 wrapper.

CHAIN-3's closure ALSO unblocks **CHAIN-4** (the `Fin (d+1)` incidence + Claim-6.12 discriminator
`exists_complementIso_ne_zero_of_homogeneousIncidence`, which consumes (h-4)'s duality) and the
**four-producer tail** (OD-7: `hforget_k` routes through (h-4), then `hbase_k`/`hcut_k`/
`hcontract_k`) — any of these is a valid next leaf. See *Hand-off*.

**Prior-commit recaps (one-line; full OD-8 route-(α) leaf chain h-0…h-3 LANDED, CHAIN-3 finished by
(h-4) in the prior commit):** (h-0) `screwAlgebraTopEquiv_map_eq_det_smul`; (h-1)
`complementIso_map_orthogonal_eq` (O(n)-equivariance); (h-2) `exists_orthonormalBasis_span_pair_eq`
(Gram–Schmidt span-control) + transport bridge `EuclideanSpace.{inner_eq_basisFun_toDual,
toDualOrthogonal_ofLinearIsometryEquiv}` (mirror); (h-3)-input `exists_smul_extensor_eq_of_mem_span_
range` + `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`); (h-3) assembly
`complementIso_extensor_mem_range_map_subtype` (panel-meet range-membership crux, `MeetHodge.lean`).

**Architectural constraint (standing).** The metric-using Hodge leaves live in `MeetHodge.lean`, never
`Meet.lean`: importing `Mathlib.Analysis.InnerProductSpace.PiL2` into the metric-free `Meet.lean`
regresses `complementIso_smul_eq_extensor_join` to a `whnf` timeout (TACTICS-QUIRKS § 59). Pure
`EuclideanSpace`↔`toDual` glue stays in the `Mathlib/` mirror; (h-4) also belongs in `MeetHodge.lean`.

**CHAIN orientation (standing).** The recon (`notes/Phase23-design.md` §"CHAIN", source-verified
against KT §6.4.2 eqs. 6.46–6.67 + the landed tree) found **the arm-realization engine is already
general-`k`** (the M₁/M₂/M₃ closers `case_III_arm_realization` / `_M2` / `_M3` in
`CaseIII/{Arms,Relabel}.lean` were authored `(k:ℕ)`); the genuinely-`d=3` surface is **only the
dispatch** (`case_III_candidate_dispatch`, `Realization.lean:201`) — its fixed-3-candidate count +
the `⋀²ℝ⁴` discriminator (`exists_homogeneousIncidence_of_normals` / `…complementIso…` in
`Claim612.lean`, the `Meet.lean`/`MeetHodge.lean` duality lemmas). CHAIN's job: replace that
dispatch with the `d`-candidate chain dispatch + the `⋀^{d−1}(ℝ^{d+1})` duality finish (now LANDED).

**The load-bearing flag (recon (b)) — SETTLED 2026-06-17.** The 23a-carried
`hdispatch` (`Theorem55.lean:2225`) takes a **fixed `v,a,b,c` 4-tuple**, faithful
at `d=3` (the chain `v₀v₁v₂v₃` *is* `b—v—a—c`) but **too short at `d≥4`** — KT's
general-`d` Lemma 6.13 needs the whole length-`d` chain. The CHAIN↔ENTRY
chain-data contract is now **frozen** (`notes/Phase23-design.md` §"CHAIN↔ENTRY
contract"): a `G.ChainData n` `structure` (length-`d` chain `vtx`/`edge`/`e₀` +
degree-2 closures) is the shared shape; the reshape is **three decls in
lockstep** — the ENTRY extractor (`exists_chain_data_of_noRigid` → a `ChainData`
producer), the producer `case_III_hsplit_producer_all_k.hcand` (which calls the
extractor inline, C.0), and the CHAIN-5 dispatch `hdispatch`. **No motive/IH
change forced** (clause (ii), C.6): the chain data is combinatorial, the base
`(G₁,q₁)` stays the existing general-`k` realization premise from the same 0-dof
IH conjunct, the `d` candidate splits are smaller 0-dof graphs. CHAIN-5's
signature is now authorable; the `d=3` line is a zero-regression wrapper (C.4).

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)). Five leaves, **one** sub-phase (OD-6).
**CHAIN-1 + CHAIN-3 are CLOSED**. CHAIN-4 + the four-producer tail are unblocked
(consume CHAIN-3); CHAIN-2 is buildable now (consumes CHAIN-1); CHAIN-5 is gated
by the (b) flag (its signature is the CHAIN↔ENTRY contract).

- [x] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks + the Hodge panel-meet membership**
      (`Meet.lean` + `MeetHodge.lean`). **CLOSED 2026-06-17** (rows 193–210; full per-leaf detail in
      *Decisions made* below). Route = the **`⋀^{d−1}W`-is-a-line** one (CHAIN-3-finish recon,
      `notes/Phase23-design.md` §"CHAIN"(f)/(g)/(h)), NOT the withdrawn d=3-only `Φ̃` route. Landed:
      the three grade bricks (`extensor_mem_range_map_subtype_of_mem_grade` /
      `exists_smul_eq_of_mem_range_map_subtype_grade` /
      `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`), then the OD-8 route-α chain — (h-0)
      `screwAlgebraTopEquiv_map_eq_det_smul` → (h-1) `complementIso_map_orthogonal_eq` (the Hodge
      O(n)-equivariance) → (h-2) the metric transport bridge (mirror `Mathlib/…/PiL2.lean`) +
      Gram–Schmidt `exists_orthonormalBasis_span_pair_eq` (`MeetHodge.lean`) → (h-3)
      `complementIso_extensor_mem_range_map_subtype` (the panel-meet membership crux) → (h-4)
      `extensor_join_proportional_complementIso_meet` (the join=meet duality, closes CHAIN-3).
      - [~] **Cleanup-round candidates (forward, low-priority):** (1) the lifted `wedgeFixedLeft`
        block + `inf_range_wedgeFixedLeft` (ambient `{d}`) served the `Φ̃` route the CHAIN-3-finish
        recon **withdrew** (`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp`
        do NOT generalize — `dim Ω = C(d−1,2) = 1` only at `d=3`; the d=3 lemmas stay GREEN, **do NOT
        touch**) — revert the lifted infra to `Fin 4`. (2) The `finrank {n}^⊥ = k` metric transport is
        duplicated between (h-3) and (h-4) — factor a shared `finrank_toDualPerp_pair_eq` helper.
- [x] **CHAIN-1 — the `d`-fold candidate machinery** (`RigidityMatrix/Basic.lean`). **CLOSED
      2026-06-18** (rows 211–212). Graph-free over `ScrewSpace k`; no `d=3` content. Two bricks:
      (1) the row-correspondence swap (KT eq. 6.62) `linearIndependent_sumElim_candidateBlock_swap`
      + mirror `linearIndependent_sumElim_block_swap`; (2) the `ιc`-block candidate augment
      `linearIndependent_sum_pinned_block_augment_block` + `linearIndependent_sum_augment_candidateRow_block`,
      the `+|ιc|` count lift (the single-`Unit` `…_augment{,…_candidateRow}` re-derived as the
      `ιc := Unit` corollaries; blueprint pins unmoved). The per-candidate column-op heterogeneity of
      the heterogeneous chain is CHAIN-2's bookkeeping (the augment fires one body at a time).
- [~] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`RigidityMatrix/Claim612.lean`). Consumes CHAIN-3. **Two bricks LANDED
      2026-06-18:** `exists_independent_perp_pair_gen` (the general-`d` "second
      normal through a line", ambient `Fin (k+2)`, `2 ≤ k`) and
      `omitTwoExtensor_eq_extensor_kept_gen` (the general-`d` kept-points
      tabulation, ambient `Fin (e+2)`); both `Fin 4` lemmas now `e:=2`/`k:=2`
      wrappers. **OD-4 RESOLVED 2026-06-18** (existence/homogeneous, not
      alg-independence — Decisions-made + design §(i)). **Remaining = four leaves
      with exact signatures in design §(j),** dependency-ordered:
      - [ ] **CHAIN-4a** `exists_homogeneousIncidence_of_normals_gen` at `Fin (k+1)
            → Fin (k+2)` (the OD-4 sub-leaf, **clean lift** — row-matrix
            surjectivity, no genericity). **First buildable; the next build.**
      - [ ] **CHAIN-4b** `exists_line_data_of_homogeneousIncidence_gen` (clean
            lift; carries the §(i) one residual — per-join `Πᵢ`-membership iff
            `i+1∈{a,b}` must close combinatorially from the orthogonality hyps).
            Consumes 4a + landed `omitTwoExtensor_eq_extensor_kept_gen` +
            `exists_independent_perp_pair_gen`.
      - [ ] **CHAIN-4c** `case_III_claim612_gen` (the span-`D` existential; **pure
            numeral lift** of the already-general `span_omitTwoExtensor_eq_top` +
            `eq_zero_of_annihilates_span_top`). Buildable now in parallel with 4a.
      - [ ] **CHAIN-4d** `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
            at `ScrewSpace k`/`Fin (k+1)` candidates, `complementIso (k:=k)(j:=2)`
            (the §(f)/§(i) `(j:=2)` correction — a line has 2 normals at every
            `d`). The capstone: consumes 4b + 4c + the **landed CHAIN-3 (h-4)**
            join=meet duality.
- [ ] **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`).
      The per-candidate-`i` reduction of `R(G,pᵢ)` to `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)`
      + the ±r chain (6.66). Reuses Claim 6.11 `exists_redundant_panelRow_…`
      (general & GREEN). Heaviest mechanical leaf ("exactly the same as `d=3`").
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
      Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature now FROZEN** by the CHAIN↔ENTRY contract (`notes/Phase23-design.md`
      §"CHAIN↔ENTRY contract" C.3): `hdispatch` consumes a `G.ChainData n` record
      (the length-`d` chain) + the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0
      fact + the IH-generic base realization on that split. Keep the `d=3` dispatch
      as a `k=2`/length-3 wrapper (no `d=3` regression — C.4 zero-regression map).
- [ ] **CHAIN tail — lift the four 23a-carried producers** (OD-7 fold). After
      CHAIN-3: `hforget_k` (M4 forget, `exists_extensor_eq_panelSupportExtensor`
      routes through CHAIN-3's duality), then through it `hbase_k`/`hcut_k`/
      `hcontract_k`. Direct corollary of CHAIN-3 + numeral pass — caveat (e)
      OD-7: confirm the *only* genuinely-`d=3` reach-in is the duality at build.

## Blockers / open questions

The OD resolutions (full text in `notes/Phase23-design.md` §"CHAIN"(e)/(g)):

- **OD-8 — RESOLVED 2026-06-17.** The panel-meet range-membership
  `complementIso(j:=2)⟨n_u∧n',_⟩ ∈ range(⋀^k W ↪)` for `W = {n_u,n'}^⊥` is CLOSED via route α
  (the entire leaf chain h-0…h-3 LANDED): `complementIso` IS the Hodge `⋆`, O(n)-natural; the
  target transports the standard-frame membership along an orthogonal change of frame. Route β
  stays **rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count
  `= C(d−1,2) > 1` for `d≥4`). Full text `notes/Phase23-design.md` §"CHAIN"(h); landed leaf in
  *Decisions made* below.
- **OD-6 — DECIDED: five leaves within ONE sub-phase 23b** (no separate duality
  letter). The arm-realization engine they feed is already general-`k`, so
  neither hard core stands alone as a deliverable. Split at contact only if
  CHAIN-2's index bookkeeping proves larger than estimated.
- **OD-7 — DECIDED: the four 23a-carried producers fold into CHAIN's tail**
  (after CHAIN-3), not a dedicated successor — the M4-forget reach-in *is*
  CHAIN-3's duality, and the conditioned-pair producers route through M4.
  Caveat: confirm at build that the duality is their *only* `d=3` reach-in.
- **OD-4 — RESOLVED 2026-06-18 (design-pass): existence/homogeneous route,
  alg-independence NOT forced.** Verdict + reasoning: Decisions-made below +
  `notes/Phase23-design.md` §(i). KT eq. (6.67) phrases the `d+1`-points step via
  alg-independence (p. 698 verbatim, confirmed against the `.refs/` PDF), but the
  landed d=3 formalization sidesteps it: the D-span runs off the already-general
  `span_omitTwoExtensor_eq_top` (only hyp `LinearIndependent ℝ pbar`, via Lemma
  2.1), driven by **linear** independence of `d+1` **homogeneous** vectors, not
  KT's affine points / `(d−j)`-flat fact. The row #106 cross-product construction
  is **dead (zero live call sites)**. CHAIN-4 lifts as a numeral generalization of
  green bricks; one build-time residual (per-join panel-membership, CHAIN-4b).
- **(b) producer-shape mismatch — SETTLED 2026-06-17** (the docs-only
  contract-settle pass). The CHAIN↔ENTRY interface is frozen in
  `notes/Phase23-design.md` §"CHAIN↔ENTRY contract": a `G.ChainData n` `structure`
  (length-`d` chain `vtx : Fin (d+1) → α`, `edge : Fin d → β`, `e₀`, the deg-2
  closures) is the shared shape. **No motive/IH change forced** (C.6): the chain
  data is purely combinatorial, the base `(G₁,q₁)` is the existing general-`k`
  `HasGenericFullRankRealization` premise pulled from the same 0-dof IH conjunct,
  the `d` candidate splits are smaller 0-dof graphs (no higher-dof `G_v` GAP-6).
  The reshape is **three decls in lockstep** (extractor / producer-`hcand` /
  dispatch-`hdispatch`); the `d=3` line is a zero-regression wrapper (C.4 map:
  chain `v₀v₁v₂v₃ = b—v—a—c`). CHAIN-5's signature is now authorable.
- **OD-1 (re-confirmed for CHAIN/ENTRY).** KT Lemma 5.4 short-cycle base is a
  real branch of the general-`d` chain entry (unlike `d=3`'s inline triangle
  floor); whether CHAIN's dispatch assumes the chain branch (ENTRY discharging
  the cycle branch) is an ENTRY-contract question.

## Hand-off / next phase

**CHAIN-1 + CHAIN-3 are CLOSED; CHAIN-4 is in progress** (two bricks landed:
`exists_independent_perp_pair_gen` + `omitTwoExtensor_eq_extensor_kept_gen`; **OD-4 resolved this
commit**). **Next build = CHAIN-4a** — the OD-4 verdict (existence/homogeneous route) made concrete.
Independent next leaves, all buildable now:

- **CHAIN-4a (the next build) — `exists_homogeneousIncidence_of_normals_gen`** at `Fin (k+1) →
  Fin (k+2) → ℝ` (`RigidityMatrix/Claim612.lean`; exact signature in `notes/Phase23-design.md` §(j)).
  A **clean lift** of the d=3 body (`Claim612.lean:427`): the `(k+1)×(k+2)` row-matrix surjectivity
  (`LinearIndependent.rank_matrix` → `mulVecLin` surjective → preimages of the `k+1` standard targets)
  gives the incidence pattern; `pbar 0` is the nonzero common-perp from the already-general
  `exists_ne_zero_dotProduct_eq_zero` (m=k+1); LI of `pbar` is the triangular pairing argument. **No
  genericity device, no alg-independence (OD-4 verdict).** `Fin 4` lemma → `k:=2` wrapper. Then off it:
  CHAIN-4b `exists_line_data_…_gen` (clean lift; carries the §(i) one residual), CHAIN-4c
  `case_III_claim612_gen` (pure numeral lift of the general `span_omitTwoExtensor_eq_top` + Lemma 2.1
  — buildable now in parallel), CHAIN-4d `exists_complementIso_ne_zero_…_gen` at `ScrewSpace k`/
  `Fin (k+1)`, `complementIso (k:=k)(j:=2)` (the §(f)/§(i) `(j:=2)` correction), consuming the landed
  CHAIN-3 (h-4) join=meet duality the way the d=3
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` consumes `complementIso_smul_eq_extensor_join`.
  CHAIN-2 (consuming CHAIN-1) is an independent alternative.
- **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`), consuming CHAIN-1's two
  bricks. The per-candidate-`i` reduction of `R(G,pᵢ)` to `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)` + the ±r chain
  (6.66): the index-heavy generalization of the `caseIIICandidate`/`case_III_old_new_blocks`/
  `case_III_rank_certification` chain (now `q : α × Fin 4`-shaped) to a `Fin d`-indexed candidate
  family. This is where the **per-candidate column-op heterogeneity** lives (each candidate `i` applies
  its own `Φᵢ` before the CHAIN-1 augment fires one body at a time). Reuses Claim 6.11
  `exists_redundant_panelRow_…` (general & GREEN). Heaviest mechanical leaf ("exactly the same as
  `d=3`"); may split on contact.
- **The four-producer tail (OD-7)** is also unblocked: `hforget_k` (M4 forget) routes through (h-4)'s
  duality, then `hbase_k`/`hcut_k`/`hcontract_k` through it. Fold into CHAIN, not a successor.

Re-pointing the d=3 discriminator at (h-4)'s `k=2` instance (h-5) is a CHAIN-4 decision, not forced —
the d=3 `complementIso_smul_eq_extensor_join` stays the green d=3 wrapper meanwhile. **Route β stays
rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count). The CHAIN-3-finish
geometry (the `⋀^{d−1}W`-is-a-line route, NOT the withdrawn d=3-only `Φ̃` route) lives canonically in
`notes/Phase23-design.md` §"CHAIN"(f)/(h); the join=meet duality KT leaves implicit is captured in the
BlueprintExposition ledger (the CHAIN-3 entry).

**The CHAIN↔ENTRY contract is now settled** (`notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", 2026-06-17) — the (b) build-recon gate is discharged:
CHAIN-5's `hdispatch`/`hcand` signature is frozen against the `G.ChainData n`
record (C.1/C.3), so it is now authorable. CHAIN-2 + the CHAIN-4 remainder remain
buildable independently of the contract (CHAIN-1/3 closed, CHAIN-4 started);
CHAIN-5 is unblocked once CHAIN-2/4 land **and** ENTRY's extractor is reshaped.

**ENTRY obligation — PINNED (signature frozen; minted/built when its turn
comes).** ENTRY reshapes `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`)
from the fixed `v,a,b,c` 4-tuple to the `G.ChainData n` producer
`exists_chainData_of_noRigid` (contract C.2 — KT Lemma 4.6 chain + Lemma 4.8
split-off minimality at general `d`, the "new combinatorial leaf" of the
OD-2/OD-3 verdict), and lifts the `6 ≤ bodyBarDim n` floor to the general
chain-length floor. The chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4)
is **ENTRY's to resolve at build** (contract C.5): the dispatch always consumes
a `ChainData` and never sees the cycle branch, so ENTRY's choice between
"chain-only extractor + cycle folded into base" (default) vs. "disjunction +
Lemma 5.4 short-cycle realization brick" is invariant for CHAIN-5's signature.
**The producer `case_III_hsplit_producer_all_k` (`Arms.lean:777`) is the chain
extractor's only consumer** (it calls the extractor inline at the `|V|≥4` arm,
Arms.lean:828–857) — its `hcand` slot is the third lockstep decl (C.0).

**Green-modulo boundary CHAIN hands downstream** (`notes/Phase23-design.md`
§"CHAIN"(d)): CHAIN discharges the general-`k` `hdispatch` (now against the frozen
`ChainData` contract) and lifts the four producers (OD-7). **ASSEMBLY** composes
the honest general-`d` Theorem 5.5, re-greens `prop:rigidity-matrix-prop11` +
`hub`, derives Thm 5.6, states Conjecture 1.2.

## Decisions made during this phase

(Phase-local choices land here as CHAIN leaves build. The opening recon's
decisions — OD-6/OD-7 resolved, OD-4 + (b) flagged — live in
`notes/Phase23-design.md` §"CHAIN"(e); the chain-data contract lives in its
§"CHAIN↔ENTRY contract".)

### Phase-local choices and proof techniques

Settled entries are one-line verdicts (decision + Lean name); proof techniques live
in git + `notes/FRICTION.md` + the design doc §"CHAIN"(f)/(g)/(h) + §"CHAIN↔ENTRY
contract". The forward detail (route to close the open leaves) is in *Current state*
/ *Hand-off* above.

**Recons / design decisions (detail in `notes/Phase23-design.md`):**
- **Opened on a leaf-level recon, not a build** — found the arm-engine already
  general-`k`, only the dispatch `d=3`; surfaced flag (b) → §"CHAIN"(a)–(e).
- **CHAIN↔ENTRY chain-data contract settled** — `G.ChainData n` structure +
  producer/`hdispatch` signatures; no motive/IH change forced (clause ii) →
  §"CHAIN↔ENTRY contract" C.0–C.6.
- **CHAIN-3-finish recon: the `⋀^{d−1}W`-is-a-line route, NOT the d=3 `Φ̃` route**
  (a line has **2** normals at every `d`, **d−1** points); `finrank_sup_range_wedgeFixedLeft`
  / `extensor_toDual_extensor_eq_zero_of_perp` **withdrawn** (dead d=3-only, kept green
  as the d=3 wrapper) → §"CHAIN"(f). KT-route-checked (the join=meet duality KT leaves
  implicit) → §"CHAIN"(f) *Coordinator KT-route check*.
- **OD-8 RESOLVED: route α (`complementIso` O(n)-equivariance); β rejected** — the whole
  leaf chain h-0…h-3 landed, the panel-meet range-membership is closed. `complementIso` IS the
  Hodge `⋆`; β rests on the withdrawn `dim Φ̃` count → §"CHAIN"(h).
- **OD-4 RESOLVED 2026-06-18: existence/homogeneous route, alg-independence NOT forced**
  (overturns the prior "forced" lean). The landed d=3 N3a works homogeneously (§1.42 R1-affine):
  the eq.-(6.67) D-span runs off `span_omitTwoExtensor_eq_top` (already general-`k`, only hyp
  `LinearIndependent ℝ pbar`, via Lemma 2.1) — **linear** independence of `d+1` **homogeneous**
  vectors, never KT's affine points / `(d−j)`-flat-in-union (the alg-independence consequence is on
  the route the formalization sidesteps). Source-verified: KT p.698 verbatim (`.refs/` PDF) vs. the
  landed bodies; the row #106 cross-product construction is **dead (zero live call sites)**. No new
  `AlgebraicIndependent` lemma; site (b) is not a site (only site (a), nested seed-rank, stays live).
  Per-join panel-membership generalizes combinatorially (join `{a,b}`⊂`Πᵢ` iff `i+1∈{a,b}`). One
  build residual flagged (CHAIN-4b). CHAIN-4 decomposed into 4a–4d → §"CHAIN"(i)/(j).

**Landed CHAIN-3 bricks** (all keep the `d=3` name as a `(d:=3)` instance or unify
`d=3` by defeq; no blueprint pin moved; the `_grade` lifts are verbatim — the route is
general mathlib, grade enters nothing):
- membership `extensor_mem_range_map_subtype_of_mem_grade`; proportionality
  `exists_smul_eq_of_mem_range_map_subtype_grade` + the count
  `finrank_exteriorPower_self_eq_one` / `exteriorPower_map_subtype_injective_grade`;
  `toDual=Gram` `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`.
- `wedgeFixedLeft` block (`def`+`coe`/`ker`/`finrank_range`, range count 3→d) +
  `inf_range_wedgeFixedLeft` — ambient-generic verbatim, implicit `{d}`, no instance
  (no external consumers). **Dead-route machinery** (the `Φ̃` count the CHAIN-3-finish
  recon withdrew): harmlessly over-general (d=3 instances still used) — **cleanup-round
  candidate to revert to `Fin 4`**.
- OD-8 route-α sub-leaves: base case `complementIso_exteriorPower_basis_eq_smul_compl`
  (complement of a coordinate blade = the complementary blade) → coordinate-`W`
  membership `complementIso_exteriorPower_basis_mem_range_map_subtype` → (h-0)
  `exteriorPower.topEquiv_map_eq_det_smul` (mirror) + `screwAlgebraTopEquiv_map_eq_det_smul`
  → (h-1a) `wedgeProd_map`/`wedgePairing_map` (volume/join half, on mirror
  `map_coe_eq_exteriorAlgebra_map`) → (h-1b) `exteriorPower_basis_toDual_map_orthogonal_eq` (the
  dot-product Gram-O-invariance: through the N3b-recon Gram determinant `pairingDual_ιMulti_ιMulti`,
  `hO` collapses each entry, lifted off decomposables by a double `LinearMap.ext_on` over the `ιMulti`
  generators; grade-/ambient-generic, no new mathlib fact) → (h-1) `complementIso_map_orthogonal_eq`
  (the O(n)-equivariance: assembled from h-1a+h-1b by `(b.exteriorPower (k+2−j)).toDual`-injectivity,
  `O` orthogonal ⟹ injective ⟹ surjective ⟹ `map O` surjective; grade-generic `{j}`). The
  general-decomposable case (h-3) is NOT a GL-equivariance corollary (`complementIso` is Hodge, O(n)-
  not GL-natural) — the remaining route is (h-2) frame alignment + (h-3) the assembly.
- (h-2) **metric→`toDual` transport bridge** (new mirror
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`): `EuclideanSpace.inner_eq_basisFun_toDual` (L²
  inner = standard-basis `toDual` dot-product pairing through `EuclideanSpace.equiv`) +
  `EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` (an L²-`LinearIsometryEquiv` transports to
  a `toDual`-orthogonal equiv of `ι → ℝ` — the `hO`-feeder for (h-1)). Axiom-clean, self-contained
  (no exterior-algebra dep, copy-paste-promotable). The metric-vs-algebraic "orthogonal"
  reconciliation.
- (h-2) **Gram–Schmidt span-control existence** `exists_orthonormalBasis_span_pair_eq` (new
  downstream file `Molecular/MeetHodge.lean`): an `OrthonormalBasis` of `EuclideanSpace ℝ (Fin (k+2))`
  whose first two vectors span an independent pair `{n₀,n₁}`. `gramSchmidtOrthonormalBasis` on the
  zero-extended family; the span chain runs `{b 0,b 1} → gramSchmidtNormed f '' Iic 1` (nonzero via
  `gramSchmidtNormed_unit_length_coe`) `→ span(gramSchmidt f '' Iic 1)` (`span_gramSchmidtNormed`)
  `→ span(f '' Iic 1)` (`span_gramSchmidt_Iic`) `→ span{n₀,n₁}`. Per-index nonzero hyp from
  `LinearIndepOn ℝ f (Iic 1)` = `hn` reindexed (`linearIndepOn_range_iff` on `![0,1]` +
  `linearIndependent_restrict_iff`). `MeetHodge.lean` wired into `CombinatorialRigidity.lean`.
- (h-3) **input proportionality** `exists_smul_extensor_eq_of_mem_span_range` + prerequisite
  `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`). `extensor n` matched up-to-scalar to
  the `2`-extensor of the orthonormal frame pair (line-is-1-dim idiom `finrank_exteriorPower_self_eq_one`
  at grade 2); prerequisite **decouples** the grade `j` from the ambient `d` in `…_of_mem_grade`
  (`_grade` re-derived as the `j := d−1` instance, callers untouched). Both metric-free.
- (h-3) **assembly** `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`, this commit) —
  the OD-8 crux. `complementIso (j:=2) ⟨extensor n,_⟩ ∈ range(⋀^k W ↪)`, `W = {n 0,n 1}^⊥`. The
  orthogonal change-of-frame: `b := exists_orthonormalBasis_span_pair_eq` aligns `span{n 0,n 1}` to the
  coordinate plane, `O := ofLinearIsometryEquiv b.repr.symm` (`toDual`-orthogonal via the transport
  bridge) sends the coordinate complement into `W` and the coordinate blade to `extensor ![bf 0,bf 1]`
  (∝ `extensor n`); push the LANDED standard-frame membership through `O` by (h-1)
  `complementIso_map_orthogonal_eq` + the new metric-free **range-pushforward**
  `exteriorPower_map_mem_range_map_subtype_of_mapsTo` (`Meet.lean`,
  `LinearMap.subtype_comp_codRestrict` + `exteriorPower.map_comp`). `W = {n 0,n 1}^⊥` dimension step:
  `W ≤ Q` (the `toDual`-perp), both `k`-dim (`Q` via `finrank_add_finrank_orthogonal` transported across
  `EuclideanSpace.equiv` by `inner_eq_basisFun_toDual` + `real_inner_comm`), so `W = Q`. Two FRICTION
  idioms surfaced (`span_induction` on an applied subject; `EuclideanSpace.equiv` is a CLE). No
  blueprint pin (intermediate brick; the duality node `lem:case-III-claim612-line-in-panel-union`
  stays green via its d=3 route until (h-4) lands the general one).
- (h-4) **assembly — closes CHAIN-3** `extensor_join_proportional_complementIso_meet`
  (`MeetHodge.lean`, this commit). The general-`d` per-line join=meet duality
  `∃ c, c • complementIso(j:=2)⟨extensor n,_⟩ = ⟨extensor p,_⟩` (`n : Fin 2` normals, `p : Fin k`
  points, `hperp`). `W := {n 0,n 1}^⊥` (`finrank = k` via the (h-3) metric transport reused: `W ≤ Q`,
  both `k`-dim, `W = Q`); point-join + panel-meet both `∈ range(⋀^k W ↪)` (the (h-3) leaf +
  `extensor_mem_range_map_subtype_of_mem_grade (d:=k+1)`); panel-meet `≠ 0` (`complementIso` injective
  + `extensor n ≠ 0`), so `exists_smul_eq_of_mem_range_map_subtype_grade (d:=k+1)` proportionalizes;
  orient `(panel-meet)↦(point-join)` by inverting the nonzero scalar (`inv_smul_eq_iff₀`, GOLF § 19).
  Both `hp` and `hpair` load-bearing. No blueprint pin (intermediate; the duality node stays green via
  its d=3 route — re-point is a CHAIN-4 call, h-5). **Cleanup-round candidate:** the `finrank {n}^⊥ = k`
  metric transport is re-derived here near-verbatim from the (h-3) leaf — extract a shared
  `finrank_toDualPerp_pair_eq` helper once both are green and stable.

**Landed CHAIN-4 bricks** (CHAIN-4 in progress; `RigidityMatrix/Claim612.lean`):
- `omitTwoExtensor_eq_extensor_kept_gen` (2026-06-18) — the general-`d` kept-points tabulation,
  ambient `Fin (e+2)` (`d = e+1`): for the omitted pair `q`, `omitTwoExtensor pbar (ne_of_lt q.2) =
  extensor (fun k => pbar (emb k))` with `emb : Fin e ↪o Fin (e+2)` the increasing complement of
  `{q.1,q.2}`, each `≠ q.1,q.2`. Proof is `refine ⟨…, rfl⟩` (omit-two extensor is *by definition* the
  complement-enumeration extensor) + the `orderEmbOfFin_mem`/`mem_compl` chain hoisted from the `Fin 4`
  body. Both `Fin 4` lemmas (`omitTwoExtensor_eq_extensor_kept`, `…_homogenize_…`) re-derived as `e:=2`
  wrappers (`emb 0 < emb 1`, `heq.trans` a `![…]`-vs-`fun` `funext`); no pin, callers untouched.
- `exists_independent_perp_pair_gen` (2026-06-18) — the general-`d` "second normal through a line",
  ambient `Fin (k+2)` (`k = d−1`), `2 ≤ k`: two points of a line both `⬝ᵥ`-⊥ to `n_u ≠ 0` ⟹ a second
  independent normal `n'`. Verbatim lift of the `Fin 4` body (rank–nullity on the two-functional kernel
  `≥ k ≥ 2 > 1`, proper-superspace + `LinearIndependent.pair_iff'`; `finrank_pi` via `simp` at the
  variable dim). `Fin 4` `exists_independent_perp_pair` = the `k := 2` wrapper. Axiom-clean.

**Landed CHAIN-1 bricks** (closes CHAIN-1; all in `RigidityMatrix/Basic.lean`, graph-free over
`ScrewSpace k`, axiom-clean, both single-`Unit` predecessors re-derived as the `ιc := Unit`
corollaries so blueprint `\lean{…}` pins are unmoved):
- the `Fin d` chain row-correspondence (KT eq. 6.62) `linearIndependent_sumElim_candidateBlock_swap`
  — swapping a candidate **block** `cand : ιc → Dual` by base-span members
  `cand' i - cand i ∈ span(range(Sum.elim rn ro))` preserves LI; the block generalization of the
  single-`Unit` `…candidateRow_swap` (reassociate `(ιn⊕ιc)⊕ιo → (ιn⊕ιo)⊕ιc`, then the new mirror
  `linearIndependent_sumElim_block_swap`: quotient route `M ⧸ span(range base)` +
  `LinearIndependent.sumElim_of_quotient`). See FRICTION [mirrored] *`…sumElim_block_swap`…*.
- the `ιc`-block candidate augment (2026-06-18, this commit) — `linearIndependent_sum_pinned_block_
  augment_block` (the abstract pin-a-body `+|ιc|` augment: a whole pinned candidate block `wc : ιc →
  Dual` joins the new `va`-block via `linearIndependent_sum_pinned_block` on `Sum.elim rn wc`) +
  `linearIndependent_sum_augment_candidateRow_block` (the column-operated form: `wc` becomes pure-`v`
  under the shared `Φ = columnOp hva`, transports back through `Φ.dualMap`). Mechanical `ιc`-lift of
  the single-`Unit` `…_augment{,…_candidateRow}` (`Unit → wc`, `funext;cases;rfl` over `ιn ⊕ ιc`); no
  new tactic friction. The chain's per-candidate column-op heterogeneity (each `i` has its own `Φᵢ`)
  is **CHAIN-2's** bookkeeping — the augment fires one body at a time at the chosen split body `v`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *The `⧸` quotient notation (`M ⧸ P`) needs a direct `import Mathlib.LinearAlgebra.Quotient.Basic`
  even when `Submodule.mkQ` resolves by name (a notation must be imported, not merely reachable) —
  or drop the type ascription and let `set π := P.mkQ` infer the codomain* → TACTICS-QUIRKS § 60 /
  FRICTION [mirrored] *`linearIndependent_sumElim_block_swap`…* (Gotcha).
- *To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard` `default` index,
  surface `↑default = univ` with a `rfl`-`have` first (it won't `simp` out on its own)*
  → FRICTION [idiom] *To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard`…*.
- *A `-/` inside a docstring word (`grade-/ambient`) closes the doc comment early
  → "unexpected identifier; expected 'lemma'" inside the prose* → TACTICS-QUIRKS § 57.
- *After lifting an in-place numeral-pinned `def` to implicit `{d}`, a numeral
  consumer's `omega` mis-atomizes the `(d:=3)`-vs-numeral elaborations of one term
  (free-variable counterexample, never reads the bridging hyp) — use `linarith` /
  `simpa using h`* → TACTICS-QUIRKS § 58 / FRICTION [idiom] *Generalizing an in-place
  numeral-pinned `def`…*.
- *`Set.powersetCard.compl` inside a hypothesis (no expected `powersetCard _ m` type)
  leaves the target cardinality `m` a stuck metavariable — pin `(m := …)` explicitly*
  → FRICTION [idiom] *`Set.powersetCard.compl` inside a hypothesis…*.
- *`set b := e` folds `e` out of the goal too, so a later `rw`/`simp only [lib_lemma]`
  whose LHS pattern mentions `e` silently fails (`simp only` reports args "unused") —
  the goal-side / library-lemma variant of the `set` fold; drop the `set`* →
  TACTICS-QUIRKS § 43 (goal-side / library-lemma variant).
- *A new `InnerProductSpace`/`EuclideanSpace` import poisons a pre-existing exterior-algebra proof
  in the same file to a `whnf` timeout (the `PiLp 2` instances become defeq-visible to `⋀`-term
  elaboration) — keep the bridge in a `Mathlib/` mirror, house metric-using leaves in a downstream
  file* → TACTICS-QUIRKS § 59 / FRICTION [mirrored] *`EuclideanSpace.inner_eq_basisFun_toDual`…*.
- *`induction h using Submodule.span_induction` fails on an applied membership subject (`n j`) —
  hoist a `∀ y ∈ span, …` helper, induct on the bound `y`* → FRICTION [idiom] *`induction h using
  Submodule.span_induction` fails …*.
- *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`, not a `LinearEquiv` — round-trips need the
  `ContinuousLinearEquiv.*` forms (a `LinearEquiv.apply_symm_apply` `simp only` no-ops)* → FRICTION
  [idiom] *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`…*.
- *Re-orienting a proportionality `c • x = y` into `c⁻¹ • y = x` — use `inv_smul_eq_iff₀ hcne` on the
  goal, not `rw [← hc, smul_smul]` (the nested-`•` `rw` chain fails on `⋀`-subtype elements)* →
  TACTICS-GOLF § 19.
