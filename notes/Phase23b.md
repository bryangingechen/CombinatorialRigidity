# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 are CLOSED.** The OD-7 four-producer tail is **open**
but advancing: both M4 halves are general-`k`, the **full base producer `hbase_k`** is general-`k`,
the **`hcut_k` bare conjunct** is general-`k`, and, **this commit (2026-06-18)**, the **`hcut_k` GP
conjunct is now general-`k`** — `case_cut_edge_realization_gp_gen` (`Theorem55.lean`), a verbatim
numeral pass over the d=3 GP body (`Fin 4 → Fin (k+2)` for the `q₀ᵢ` seeds + the combined
`exists_injective_algebraicIndependent_real` seed type, `BodyHingeFramework 2 → … k`,
`exists_generalPosition_polynomial (k := 2) → (k := k)`, `screwDim 2 → screwDim k`, dof `k → c`);
all reach-ins (`ofNormals`, `exists_generalPosition_polynomial`,
`exists_rankPolynomial_of_le_finrank_linking`, the two swap/recordsLinks bricks, the cut
decomposition, B2) were already grade-parametric. **`hcut_k` is now fully general-`k`.** The d=3
`case_cut_edge_realization_gp` is now its `k:=2` wrapper (blueprint pin
`lem:case-cut-edge-realization-gp` unmoved). **Remaining tail: only `hcontract_k`** (the Case-I
dispatch). **CHAIN-4 was closed by the CHAIN-4d commit**
(`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`, the discriminator capstone = assembly of
CHAIN-4c + CHAIN-4b + CHAIN-3 (h-4)). **Remaining: CHAIN-2 + CHAIN-5 + the producer `hcontract_k`
(`Theorem55.lean`; `hbase_k`/`hcut_k`/`hforget_k` done).** CHAIN-1 = the
`ιc`-block candidate augment + `…candidateBlock_swap`
(`RigidityMatrix/Basic.lean`), graph-free over `ScrewSpace k`. CHAIN-3 = the general-`d` per-line
join=meet duality `extensor_join_proportional_complementIso_meet` (`MeetHodge.lean`), the
`⋀^{d−1}W`-is-a-line route (the d=3 `complementIso_smul_eq_extensor_join` stays the GREEN d=3
wrapper). **CHAIN-5 gated by the ENTRY-contract reshape.** The integer Phase 23 stays **in progress**
— ENTRY / ASSEMBLY remain (coordinator owns the sub-phase boundary; codes-until-open).

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

**Next build = `case_I_realization_nonsimple_gen`** — the 2nd leaf of the `hcontract_k` decomposition
(recon 2026-06-18, design §(k): 5 leaves, 6 if h65 splits; numeral pass + one `_perp_grade` swap). The
1st leaf **`case_I_realization_all_k_gen` is LANDED (this commit)** — verbatim numeral pass, the d=3
`case_I_realization_all_k` now its `k:=2` wrapper. The *one* genuinely-new piece in the tail is LEAF-0
`linearIndependent_normals_of_algebraicIndependent_triple` (consumed by `h65`). Or **CHAIN-2**,
or **CHAIN-5/ENTRY**. CHAIN-1/3/4 are CLOSED; the **four-producer tail (OD-7) is open** but advancing: both
M4 halves are general-`k` (the reach-in `exists_extensor_eq_panelSupportExtensor_gen`
(`PanelLayer.lean`) + the consumer `hasPanelRealization_of_generic` (`GenericityDevice.lean`)), **the
full base producer `hbase_k` is general-`k`** (the trichotomy dispatch `theorem_55_base_producer_gen`
assembling the five `_gen` arms), and — as of 2026-06-18 — **`hcut_k` is FULLY general-`k`** (the bare
conjunct `case_cut_edge_realization_gen` + the GP conjunct `case_cut_edge_realization_gp_gen`, both
verbatim numeral passes; detail in *Decisions made* → *Landed OD-7 bricks*; d=3 lemmas are `k:=2`
wrappers, blueprint pins unmoved). **What remains in the tail: `hcontract_k`'s 4 remaining leaves**
(`nonsimple`/LEAF-0/`h65`/`dispatch`, design §(k); `all_k` LANDED this commit); `hforget_k`'s `k=2`
filler is already general-`k`. The `d=3` consumers (`theorem_55_minimalKDof_k`, etc.) resolve `k:=2` by
unification, unchanged. The other buildable leaves: **CHAIN-2**
(the chain matrix bookkeeping, eqs. 6.59–6.64, `CaseIII/`; consumes CHAIN-1, buildable now, heaviest
mechanical leaf). **CHAIN-5** (the `d`-chain dispatch assembly, `CaseIII/Realization.lean`) has a
frozen signature (the CHAIN↔ENTRY contract) but is gated on CHAIN-2/4 landing **and** ENTRY's extractor
reshape. See *Hand-off* for the per-leaf detail.

**CHAIN-4d — LANDED the prior commit (2026-06-18): the discriminator capstone, closing CHAIN-4.**
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`RigidityMatrix/Claim612.lean`): from
`r ≠ 0`, LI `pbar : Fin (k+2) → Fin (k+2) → ℝ`, LI normals `n : Fin (k+1) → Fin (k+2) → ℝ`, and the
off-one-panel incidence (`h0`/`hi`), produces a discriminating index `u : Fin (k+1)` + second normal
`n'` with `r(complementIso (j:=2) ⟨extensor ![n u, n'],_⟩) ≠ 0`. The assembly of **CHAIN-4c** (witness
join `r⟨omitTwoExtensor pbar,_⟩ ≠ 0`) + **CHAIN-4b** (per-join line data: `u`, `n'`, the `k` kept points
`p` LI ⊥ both, `omitTwoExtensor pbar = extensor p`) + **CHAIN-3 (h-4)** (the `∃ c, c • complementIso(…)
= extensor p` proportionality, the `k`-form). Contrapositive: `r(complementIso) = 0` ⟹ `r(extensor p)
= c • 0 = 0` ⟹ `r` kills the witness join, contradicting CHAIN-4c. Wired to CHAIN-4b's `_gen` directly
(it carries `hpbar` → concludes `LinearIndependent ℝ p`, which CHAIN-3 (h-4) needs). The `MeetHodge`
import did **not** regress the file's `⋀²ℝ⁴` proofs to a §59 whnf timeout (full build clean). Axiom-clean.
**OD-4 verdict held end-to-end: no alg-independence / genericity surfaced** (only LI of `pbar`).

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
- [x] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`RigidityMatrix/Claim612.lean`). **CLOSED 2026-06-18** (4a–4d all landed).
      Consumes CHAIN-3. **OD-4 RESOLVED + CONFIRMED** (existence/homogeneous, not
      alg-independence; CHAIN-4b's build closed the last residual — Decisions-made +
      design §(i)). The four sub-leaves (exact signatures in design §(j)):
      - [x] **CHAIN-4a** `exists_homogeneousIncidence_of_normals_gen` at `Fin (k+1)
            → Fin (k+2)`. **LANDED 2026-06-18** (the OD-4 sub-leaf, clean lift —
            row-matrix surjectivity, no genericity). Detail in *Decisions made*.
      - [x] **CHAIN-4b** `exists_line_data_of_homogeneousIncidence_gen` at
            `Fin (k+2)`. **LANDED 2026-06-18** — confirmed the §(i) per-join
            membership combinatorially (the uniform two-case dispatch on `0 ∈ {a,b}`,
            via the new `pbar_dotProduct_eq_zero_of_ne_succ` + `k`-point perp helper
            `exists_independent_perp_family`). **Two faithful divergences from the
            d=3 lemma** (so the d=3 body stays its own green lemma, not a wrapper):
            off-one-panel incidence hyp, and the conclusion carries
            `LinearIndependent ℝ p` (needs the new `hpbar` hyp CHAIN-4d supplies).
            Detail in *Decisions made*.
      - [x] **CHAIN-4c** `case_III_claim612_gen`. **LANDED 2026-06-18** — the span-`D`
            existential, **verbatim numeral lift** of the d=3 body (both bricks
            `span_omitTwoExtensor_eq_top` + `eq_zero_of_annihilates_span_top` already
            `{k:ℕ}`). The d=3 `case_III_claim612` re-derived as the `k:=2` wrapper.
            Axiom-clean; no friction. Detail in *Decisions made*.
      - [x] **CHAIN-4d** `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`.
            **LANDED 2026-06-18 — closes CHAIN-4.** The discriminator capstone at
            `ScrewSpace k`/`Fin (k+1)`, `complementIso (k:=k)(j:=2)`. Assembly of 4b
            (line data) + 4c (witness join) + CHAIN-3 (h-4) (join=meet duality);
            contrapositive of the d=3 `…eq_zero_of_complementIso…` lifted to `Fin k`
            points. `MeetHodge` import did NOT trigger a §59 whnf regression on the
            file's `⋀²ℝ⁴` proofs. Detail in *Decisions made*. Axiom-clean.
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
- [~] **CHAIN tail — lift the four 23a-carried producers** (OD-7 fold). After
      CHAIN-3: `hforget_k` (M4 forget), then through it `hbase_k`/`hcut_k`/
      `hcontract_k`. **Landed (full per-brick detail in *Decisions made* →
      *Landed OD-7 bricks*):** both M4 halves general-`k`
      (`exists_extensor_eq_panelSupportExtensor_gen`, `PanelLayer.lean`, the reach-in
      through CHAIN-3 (h-4), confirming caveat (e); `hasPanelRealization_of_generic`,
      `GenericityDevice.lean`, the consumer); **the full base producer `hbase_k`**
      (all three bare arms `theorem_55_base_producer_{empty,single_edge,parallel_pair}_gen`,
      both working GP arms `theorem_55_base_producer_{empty,single_edge}_gp_gen`, the
      **trichotomy dispatch** `theorem_55_base_producer_gen`); and **the full `hcut_k`** —
      the bare conjunct `case_cut_edge_realization_gen` plus, this commit, the GP conjunct
      `case_cut_edge_realization_gp_gen` (`Theorem55.lean`, verbatim numeral passes; all
      reach-ins already grade-parametric). All d=3 lemmas now their `k:=2` wrappers,
      blueprint pins unmoved. **Remaining: `hcontract_k`** (the Case-I dispatch),
      **decomposed** (recon 2026-06-18, design §(k)) into **5 leaves** (6 if h65 splits):
      `case_I_realization_all_k_gen` (1st, verbatim numeral pass — **LANDED this commit**, the
      d=3 `case_I_realization_all_k` now its `k:=2` wrapper) → `case_I_realization_nonsimple_gen`
      (next; numeral pass + `_perp_grade` swap) → **LEAF-0
      `linearIndependent_normals_of_algebraicIndependent_triple`** (the *one* genuinely-new
      piece — fixed-3-row LI at `Fin (k+2)`; `…_general` gives `k+1` rows, h65 has only 3
      vertices) → `case_I_realization_h65_gen` (consumes LEAF-0) → `case_I_dispatch_gen` +
      `hcontract_k` wire-up. `hforget_k`'s filler already general-`k`.

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

**CHAIN-1 + CHAIN-3 + CHAIN-4 are CLOSED** (CHAIN-4 closed by CHAIN-4d, the discriminator capstone
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`). **The four-producer tail (OD-7) is open**
but nearly done: both M4 halves are general-`k` (the reach-in
`exists_extensor_eq_panelSupportExtensor_gen` + the consumer `hasPanelRealization_of_generic`), the
full base producer `hbase_k` is general-`k` (the trichotomy dispatch `theorem_55_base_producer_gen`),
and **`hcut_k` is FULLY general-`k`** — the bare conjunct
`case_cut_edge_realization_gen` plus the GP conjunct `case_cut_edge_realization_gp_gen`, both verbatim
numeral passes (see *Current state* + *Decisions made*). **`hcontract_k` remains in the tail**,
decomposed (recon 2026-06-18, design §(k)) into **5 leaves** (6 if h65 splits) — the 1st leaf
`case_I_realization_all_k_gen` is **LANDED this commit** (the d=3 `case_I_realization_all_k` now its
`k:=2` wrapper). The *one* genuinely-new piece is LEAF-0
`linearIndependent_normals_of_algebraicIndependent_triple` (a fixed-3-row LI at `Fin (k+2)`, needed by
h65 since the landed `…_general` only gives `k+1` rows); the remaining producers
(`nonsimple`/`h65`/`dispatch`) are numeral passes (one `_perp_grade` swap in `nonsimple`).
**Next build = `case_I_realization_nonsimple_gen`** (the 2nd leaf — numeral pass + `_perp_grade`
swap), then LEAF-0/`h65`/`dispatch` per design §(k); or CHAIN-2
(heaviest mechanical leaf), or CHAIN-5/ENTRY (CHAIN-5 gated on CHAIN-2 + ENTRY's extractor reshape).

- **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`), consuming CHAIN-1's two
  bricks. The per-candidate-`i` reduction of `R(G,pᵢ)` to `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)` + the ±r chain
  (6.66): the index-heavy generalization of the `caseIIICandidate`/`case_III_old_new_blocks`/
  `case_III_rank_certification` chain (now `q : α × Fin 4`-shaped) to a `Fin d`-indexed candidate
  family. This is where the **per-candidate column-op heterogeneity** lives (each candidate `i` applies
  its own `Φᵢ` before the CHAIN-1 augment fires one body at a time). Reuses Claim 6.11
  `exists_redundant_panelRow_…` (general & GREEN). Heaviest mechanical leaf ("exactly the same as
  `d=3`"); may split on contact.
- **The four-producer tail (OD-7) — both M4 halves general-`k`; the full base producer `hbase_k`
  general-`k`; `hcut_k` FULLY general-`k` (both conjuncts, as of 2026-06-18).** The reach-in
  `exists_extensor_eq_panelSupportExtensor_gen` and the consumer `hasPanelRealization_of_generic`
  (`GenericityDevice.lean`) are lifted; `hforget_k`'s `k=2` filler is *already* general-`k`. The base
  producer (three bare arms + two GP arms + the trichotomy dispatch `theorem_55_base_producer_gen`) is
  general-`k`; `hcut_k` is now both the bare conjunct `case_cut_edge_realization_gen` and (this commit)
  the GP conjunct `case_cut_edge_realization_gp_gen` (`Theorem55.lean`). All d=3 lemmas are now `k:=2`
  wrappers, blueprint pins unmoved. `hcontract_k`'s 1st leaf `case_I_realization_all_k_gen` is
  **LANDED this commit** (the d=3 lemma now its `k:=2` wrapper). **Smallest next step:**
  `case_I_realization_nonsimple_gen` — the 2nd of the 5-leaf `hcontract_k` decomposition (recon
  2026-06-18, design §(k)): a numeral pass + the `_perp_grade` swap. The decomposition's *one*
  genuinely-new piece is LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (needed by
  `h65`); the rest are numeral passes. Fold into CHAIN, not a successor.

Re-pointing the d=3 discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence` at CHAIN-4d's
`k:=2` instance (h-5) is now an available but **not-forced** simplification — the d=3 body + its
`complementIso_smul_eq_extensor_join` wrapper stay green meanwhile; defer to ASSEMBLY/cleanup. **Route β
stays rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count). The CHAIN-3-finish
geometry (the `⋀^{d−1}W`-is-a-line route, NOT the withdrawn d=3-only `Φ̃` route) lives canonically in
`notes/Phase23-design.md` §"CHAIN"(f)/(h); the join=meet duality KT leaves implicit is captured in the
BlueprintExposition ledger (the CHAIN-3 entry).

**The CHAIN↔ENTRY contract is now settled** (`notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", 2026-06-17) — the (b) build-recon gate is discharged:
CHAIN-5's `hdispatch`/`hcand` signature is frozen against the `G.ChainData n`
record (C.1/C.3), so it is now authorable. CHAIN-2 remains buildable independently
of the contract (CHAIN-1/3/4 all closed); CHAIN-5 is unblocked once CHAIN-2 lands
**and** ENTRY's extractor is reshaped.

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
- **OD-7 `hcontract_k` decomposition (recon 2026-06-18, read-only Plan + coordinator source-verify):**
  5 leaves (6 if h65 splits) — `all_k`/`nonsimple`/`h65`/`dispatch` numeral passes (one `_perp_grade`
  swap; `_all_k` is all-*dof* not all-grade, a trap), the *one* genuinely-new piece LEAF-0
  `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI at `Fin (k+2)`; landed
  `…_general` gives `k+1` rows, h65 has only 3 vertices). No motive/IH change → §"CHAIN"(k).

**Landed CHAIN-3 bricks** (all keep the `d=3` name as a `(d:=3)` instance or unify
`d=3` by defeq; no blueprint pin moved; the `_grade` lifts are verbatim — the route is
general mathlib, grade enters nothing):
CHAIN-3 is CLOSED; its leaf names + route + the two forward cleanup-candidates are in the *CHAIN leaf
checklist* `[x]` entry above (the canonical leaf-status home), and the construction internals live in
git + `notes/Phase23-design.md` §"CHAIN"(f)/(h) + the BlueprintExposition CHAIN-3 entry. The duality
KT leaves implicit (`extensor_join_proportional_complementIso_meet`) is the CHAIN-3 ledger entry.

**Landed OD-7 (four-producer tail) bricks** (`Theorem55.lean`/`PanelLayer.lean`/`Extensor.lean`/`GenericityDevice.lean`):
- `case_I_realization_all_k_gen` (2026-06-18, the `hcontract_k` 1st leaf, general grade — opens the
  Case-I dispatch decomposition). Verbatim numeral pass over the d=3 `case_I_realization_all_k`:
  `screwDim 2 → screwDim k`, `HasGenericFullRankRealization 2 → … k` (signature + the `hQcf`
  ascription), dof `k → c` (the integer-deficiency binder + the `hKmin`/`hQcf`/coupler-`k'` arg). All
  four reach-ins were already grade-parametric — `couple_geometry_of_isProperRigidSubgraph`
  (grade-free), `hasGenericRealization_transport_ends` (`Fin (k+2)`), `exists_rankPolynomial_of_IH_
  relabel_linking_set_proj` + the block-triangular coupler `…_couple_blockTriangular_ofNormals_set_kdof`
  (both `extProj (k:=k)`/`screwDim k`/`HGFRR k`). No `[NeZero k]`/`hk:1≤k` needed (none threaded). The
  d=3 `case_I_realization_all_k` is now its `k:=2` wrapper (blueprint pin `lem:case-I-realization`
  unmoved — the d=3 dispatch consumers at `:2308`/`:2484` resolve through it). Axiom-clean; no new
  friction (TACTICS-QUIRKS §58 numeral-lift; same dof-`k`→`c` rename as `hcut_k`).
- `case_cut_edge_realization{,_gp}_gen` (2026-06-18, **completes `hcut_k`** — both conjuncts) — verbatim
  numeral passes over the d=3 bodies (grade `2→k`, `Fin 4 → Fin (k+2)`, `ScrewSpace/screwDim 2 → k`,
  `exists_extensor_in_two_panels → …_grade`, dof `k → c`); all reach-ins already grade-parametric, no
  `[NeZero k]` (no slot-0 rescale). d=3 lemmas now `k:=2` wrappers, blueprint pins unmoved. §58 idiom.
- `theorem_55_base_producer_gen` + the five `_gen` arms
  `theorem_55_base_producer_{empty,single_edge,parallel_pair}{,_gp}_gen` (2026-06-18, completes
  `hbase_k`) — trichotomy dispatch (`isMinimalKDof_ncard_le_two_trichotomy`) over verbatim numeral lifts
  of the d=3 arms (grade `2→k`, dof `k→c`; parallel-pair is the only geometric arm, its GP conjunct
  vacuous). d=3 lemmas all now `k:=2` wrappers, blueprint pins unmoved.
- `hasPanelRealization_of_generic` (M4 consumer) + `exists_extensor_eq_panelSupportExtensor_gen` (the
  M4-forget meet-decomposition reach-in), both 2026-06-18, `[NeZero k]` — the decomposition routes
  through the CHAIN-3 (h-4) duality `extensor_join_proportional_complementIso_meet` (confirming caveat
  (e): the duality *is* the only M4-forget d=3 reach-in), with slot-0 rescale `extensor_update_smul`
  (new, `Extensor.lean`). d=3 lemmas now `k:=2` wrappers; both M4 halves general-`k`.

**Landed CHAIN-4 bricks** (CHAIN-4 CLOSED 2026-06-18, `RigidityMatrix/Claim612.lean`; leaf names + per-leaf
verdicts are the *CHAIN leaf checklist* `[x]` CHAIN-4a–4d entries above — the canonical home; construction
internals in git + `notes/Phase23-design.md` §(i)/(j); all axiom-clean). Two settled cross-cutting notes:
4d's `MeetHodge` import did NOT regress the file's `⋀²ℝ⁴` proofs to a §59 whnf timeout; 4b has two faithful
divergences from the d=3 body (off-one-panel hyp + `LinearIndependent ℝ p` conclusion via the new `hpbar`),
so the d=3 lemma stays its own green body, not a `k:=2` wrapper.

**Landed CHAIN-1 bricks** (CHAIN-1 CLOSED 2026-06-18, `RigidityMatrix/Basic.lean`, graph-free over
`ScrewSpace k`, axiom-clean; both single-`Unit` predecessors re-derived as `ιc := Unit` corollaries,
blueprint pins unmoved): the eq.-6.62 row-correspondence swap `linearIndependent_sumElim_candidateBlock_swap`
(+ mirror `…_block_swap`) and the `ιc`-block candidate augment `linearIndependent_sum_pinned_block_augment_block`
(+ `…_augment_candidateRow_block`). The per-candidate column-op heterogeneity (each `i` its own `Φᵢ`) is
**CHAIN-2's** bookkeeping (augment fires one body at a time).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Lifting a `Fin (k+2)`-point-family lemma to general `k` may need `[NeZero k]` (the `0 : Fin k`
  literal in a slot-`0` rescale; the statement is genuinely false at `k=0`) — carry the hypothesis,
  don't fight the `OfNat (Fin k) 0` synthesis* → FRICTION [idiom] *Lifting a `Fin (k+2)`-point-family
  lemma to general `k`…*.
- *`map_update_smul` on `ExteriorAlgebra.ιMulti` at general grade: `(M := Fin (d+1) → ℝ)` annotation +
  the `have … := …map_update_smul v i c (v i)` term form (not `rw`, which leaves `Module ℝ …`
  un-synthesized) + `Function.update_eq_self` to clear the `update v i (v i)` residual* → FRICTION
  [idiom] *`ExteriorAlgebra.ιMulti ℝ n` needs `(M := ...)`…* (Phase 23b reuse).
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
- *Recovering a permuted-incidence `Fin n` wrapper from a general `_gen` lemma — feed `_gen` the
  reordered indexed family (`n ∘ ![…]`, LI via `hn.comp _ (by decide)`) and read the pairings back
  through the (definitional) reorder, rather than re-proving the d=3 body* → FRICTION [idiom]
  *Recovering a permuted-incidence `Fin n` wrapper…*.
- *Pushing a functional through `c • x` on an `abbrev`'d carrier (`ScrewSpace k = ⋀^k …`): `rw
  [map_smul]` (even a concrete `rw [hsmul]`) mis-fires on the smul instance — close with `exact
  (r.map_smul c _).trans …`* → TACTICS-GOLF § 19 (companion) / FRICTION [idiom] *Pushing a functional
  through a `c • x` on an `abbrev`'d carrier…*.
