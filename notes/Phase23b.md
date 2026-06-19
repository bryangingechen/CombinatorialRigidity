# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 are CLOSED, and OD-7 (the four-producer tail) is
CLOSED** — all four 23a-carried producers (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + both M4
halves are general-`k`. The last OD-7 leaf, **`case_I_dispatch_gen` + the `hcontract_k` wire-up**,
**landed 2026-06-18** (a verbatim numeral pass over the d=3 `case_I_dispatch` `by_cases` plumbing,
feeding the three already-landed `_gen` producers; plus `case_I_hcontract_gen`, the general-`k` filler
for the carried `hcontract_k` slot, lifting the d=3 wrapper's `c=0`/`c>0` split — the d=3
`case_I_dispatch` is now its `k:=2` wrapper and `theorem_55_minimalKDof_k`'s inline `hcontract_k`
filler is `case_I_hcontract_gen (k:=2)`, blueprint pins unmoved). **Remaining: CHAIN-2 + CHAIN-5.**
**CHAIN-4 was closed by the CHAIN-4d commit**
(`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`, the discriminator capstone = assembly of
CHAIN-4c + CHAIN-4b + CHAIN-3 (h-4)). CHAIN-1 = the
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

**Next = the discriminator half of the per-`i` gate-producer (now scoped INTO CHAIN-2c — see finding
below) + CHAIN-2a-ii `chainData_split_realization`.** **The W6b half of CHAIN-2a-i —
`chainData_split_w6b_gates` — LANDED 2026-06-18** (`CaseIII/Realization.lean`, axiom-clean): the
first of the design's "two producer calls". A `{k}`-general flat-tuple producer lifting the d=3
dispatch's W6b region (`case_III_candidate_dispatch` steps 3–4, lines 376–434) verbatim — from an
interior chain split `(v,a,b)` + a fresh `e₀` + the IH-generic base `hsplitGP` on
`Gab = splitOff v a b e₀` + the `∀ ends q` carry-shaped `h622lb`, it calls
`exists_candidateRow_bottomRows_of_rigidOn` once and emits the **chain-order-normalized** W6b gate
bundle: `ρ`/`w` + `ρ≠0` + `hρe₀` (`ρ(C(ab))=0`) + `hρGv` (`hingeRow a b ρ ∈ span R(Gᵥ)`) + `hw`/`hwmem`,
plus the base `IsGeneralPosition` + `Gᵥ`-link-recording the consumer needs. The `(a,b)`-vs-`(b,a)`
sign-swap (W8 pattern) is absorbed. `{k}`-general (`two_le_screwDim hk1`, no `d=3` reach-in).

**Finding from the build (the §(m) sub-leaf boundary, refined): CHAIN-2a-i is NOT a single complete
leaf — its discriminator half belongs in CHAIN-2c.** The design's §(m) sketch had
`chainData_split_arm_gates` emit the *full* bundle including `hLn`/`hρgate` (the transversal gates).
But the discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` needs the
`Fin (k+1)` chain-panel-normal family `n` (LI) and *picks an arbitrary panel `u`* — and `hρgate` is
about `n u`, NOT about the specific candidate `i`'s normal `na = q(a,·)`. Matching the discriminator's
pick `u` to the candidate `i` IS the `Fin d` family disjunction (Phase23b line 50 / §(m) line 1808
already assign "discriminator-picks-`i` glue" to CHAIN-2c). So the discriminator half cannot be a
single-`i` producer; it threads through the family. **The W6b half is the complete, contract-free,
single-`i` piece** — landed; the discriminator half folds into CHAIN-2c where the index match lives.
The "two producer calls" are NOT both single-`i`: one (W6b) is, one (discriminator) is family-level.

**The genuinely-new `Fin d` *infrastructure* (±r chain, the `d`-candidate family + per-candidate `Φᵢ`
heterogeneity + discriminator-picks-`i` glue) lives in CHAIN-2b/2c.** One clause-(ii) flag for 2a-ii
(build-time wiring, not a blocker): which arm form (`_realization` vs `_M3` relabel) the interior
split uses + the `h622lb`/`hIH` instantiation at the `vᵢ`-split — settled by the d=3 template at build
(§(m)). Then CHAIN-2b/2c; or **CHAIN-5/ENTRY** (CHAIN-5 gated on the rest of CHAIN-2 + ENTRY's
extractor reshape). **The `G.ChainData n` `structure` + its
interior-split accessors LANDED 2026-06-18** (`Induction/Operations.lean`, the zeroth CHAIN-2 leaf —
the length-`d` chain record `vtx`/`edge`/`e₀` + `vtx_inj`/`link`/`edge_inj`/`deg_two`/`e₀_fresh`;
`deg_two` settled via `0 < (i:ℕ)` interior guard + the predecessor edge `edge ⟨(i:ℕ)-1, _⟩`, d=3-map
verified `vtx 1=v`/`vtx 2=a`, closures `edge 0=e_b`/`edge 1=eₐ`/`edge 2=e_c`). **The interior-split
geometry accessors LANDED 2026-06-18** — `ChainData.{pred_succ_eq_castSucc, isLink_pred_edge,
isLink_succ_edge, succ_ne_pred_castSucc, deg_two_split}` (alongside the earlier `pred_edge_ne` /
`isLink_edge`): for an interior index `i` (`0 < (i:ℕ)`) they expose the chain geometry in the
`(v,a,b,e_a,e_b)` shape `case_III_rank_certification` consumes — split body `vtx i.castSucc`, the two
chain edges `edge i` / `edge ⟨(i:ℕ)-1,_⟩` *oriented out of* the split body (`isLink_{succ,pred}_edge`,
the latter via `pred_succ_eq_castSucc` + `.symm`), their distinct neighbors (`succ_ne_pred_castSucc`),
and the degree-2 closure re-oriented (`deg_two_split`, `Or.symm` of the field). So CHAIN-2a's
signature can bind `cd : G.ChainData n` *and* reach the per-`i` split tuple directly.
**OD-7 is now CLOSED** — the last leaf `case_I_dispatch_gen` + the
`hcontract_k` wire-up landed 2026-06-18 (a verbatim numeral pass over the d=3 `case_I_dispatch`
`by_cases hSimple`/inner-`by_cases hd` plumbing, feeding the three landed `_gen` producers +
`hasPanelRealization_of_generic`; plus `case_I_hcontract_gen`, the general-`k` filler for the carried
`hcontract_k` slot, lifting the d=3 wrapper's `c=0`→`case_I_dispatch_gen` / `c>0`→manual-dispatch
split). The d=3 `case_I_dispatch` is now its `k:=2` wrapper, and `theorem_55_minimalKDof_k`'s inline
`hcontract_k` filler is `case_I_hcontract_gen (k:=2)`; blueprint pins unmoved (both new decls are
dispatch-internal, the pinned `lem:case-I-dispatch` → `case_I_realization_h65` stays green). All four
23a-carried producers are now general-`k`: `hbase_k` (`theorem_55_base_producer_gen`), `hcut_k`
(`case_cut_edge_realization{,_gp}_gen`), `hcontract_k` (`case_I_hcontract_gen`), `hforget_k`
(`hasPanelRealization_of_generic`), plus both M4 halves. The `d=3` consumers
(`theorem_55_minimalKDof_k`, etc.) resolve `k:=2` by unification, unchanged. CHAIN-1/3/4 CLOSED. The
remaining buildable leaves: **CHAIN-2** — the `Fin d`-indexed candidate-reduction layer (eqs.
6.59–6.64, `CaseIII/`), **decomposed** at recon into 2a/2b/2c on top of the *already-general* (recon
§(l) corrected §(c)) certification chain + closed CHAIN-1, after authoring the `ChainData` record
(3–5 commits). **CHAIN-5** (the `d`-chain dispatch assembly, `CaseIII/Realization.lean`) has a frozen
signature (the CHAIN↔ENTRY contract) but is gated on CHAIN-2 landing **and** ENTRY's extractor reshape.
See *Hand-off* for the per-leaf detail.

**CHAIN-1/3/4 — all CLOSED** (2026-06-17/18; per-leaf detail in *Decisions made* → *Landed
CHAIN-{1,3,4} bricks* + `notes/Phase23-design.md` §(f)/(h)/(i)/(j) + git):
- **CHAIN-3** = the general-`d` per-line join=meet duality `extensor_join_proportional_complementIso_meet`
  (`MeetHodge.lean`, the `⋀^{d−1}W`-is-a-line route; OD-8 leaf chain h-0…h-4); the d=3
  `complementIso_smul_eq_extensor_join` stays the GREEN d=3 wrapper.
- **CHAIN-1** = the `ιc`-block candidate augment + the eq.-6.62 row-correspondence swap
  (`RigidityMatrix/Basic.lean`, graph-free over `ScrewSpace k`).
- **CHAIN-4** = the Claim-6.12 discriminator capstone
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean`, assembling
  CHAIN-4c+4b+CHAIN-3 (h-4); **OD-4 held end-to-end** — only LI of `pbar`, no alg-independence).
- Forward: **CHAIN-2** consumes CHAIN-1; **CHAIN-5** consumes CHAIN-3/4 (gated on CHAIN-2 + ENTRY).

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
`notes/Phase23-design.md` §"CHAIN"(c)/(l)/(m)). **CHAIN-1 + CHAIN-3 + CHAIN-4 + the four-producer
tail (OD-7) are CLOSED.** Remaining: **CHAIN-2** (buildable — next leaf CHAIN-2a-i, design §(m)) and
**CHAIN-5** (signature frozen by the CHAIN↔ENTRY contract; gated on the rest of CHAIN-2 + ENTRY's
extractor reshape).

- [x] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks + Hodge panel-meet membership**
      (`Meet.lean` + `MeetHodge.lean`). **CLOSED 2026-06-17** (route = `⋀^{d−1}W`-is-a-line, NOT the
      withdrawn d=3-only `Φ̃`; the OD-8 route-α leaf chain h-0…h-4 closing on the join=meet duality
      `extensor_join_proportional_complementIso_meet`). Detail: design §"CHAIN"(f)/(g)/(h) + git +
      *Decisions made* → *Landed CHAIN-3 bricks*.
      - [~] **Cleanup-round candidates (forward, low-priority):** (1) the lifted `wedgeFixedLeft`
        block + `inf_range_wedgeFixedLeft` (ambient `{d}`) served the `Φ̃` route the CHAIN-3-finish
        recon **withdrew** (`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp`
        do NOT generalize — `dim Ω = C(d−1,2) = 1` only at `d=3`; the d=3 lemmas stay GREEN, **do NOT
        touch**) — revert the lifted infra to `Fin 4`. (2) The `finrank {n}^⊥ = k` metric transport is
        duplicated between (h-3) and (h-4) — factor a shared `finrank_toDualPerp_pair_eq` helper.
- [x] **CHAIN-1 — the `d`-fold candidate machinery** (`RigidityMatrix/Basic.lean`). **CLOSED
      2026-06-18.** Graph-free over `ScrewSpace k`, no `d=3` content: the eq.-6.62 row-correspondence
      swap + the `ιc`-block candidate augment (the per-candidate column-op heterogeneity is CHAIN-2's
      bookkeeping). Detail: *Decisions made* → *Landed CHAIN-1 bricks* + git.
- [x] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`RigidityMatrix/Claim612.lean`). **CLOSED 2026-06-18** (4a–4d all landed; consumes CHAIN-3;
      OD-4 RESOLVED — existence/homogeneous, not alg-independence). Capstone = the discriminator
      `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (assembly of 4b line-data + 4c
      witness-join + CHAIN-3 (h-4)). Detail: design §(i)/(j) + git + *Decisions made* → *Landed
      CHAIN-4 bricks*.
- [ ] **CHAIN-2 — the `Fin d`-indexed candidate-reduction layer (eqs. 6.59–6.64)** (`CaseIII/`).
      **Decomposed (design §(l), which corrected §(c)'s framing — the named chain is already
      general-`k`):** the `Fin d` reduction layer on top of the reused-verbatim certification chain +
      closed CHAIN-1 → CHAIN-2a (per-`i` reduction) / CHAIN-2b (±r chain 6.66) / CHAIN-2c (family
      assembly). Reuses Claim 6.11 `exists_redundant_panelRow_…` (GREEN). **Zeroth leaf — the
      `G.ChainData n` `structure` (settling `deg_two`) + the interior-split geometry accessors —
      LANDED 2026-06-18** (`Induction/Operations.lean`; contract C.1 record, d=3-map verified, +
      `ChainData.{pred_edge_ne, isLink_edge, pred_succ_eq_castSucc, isLink_pred_edge, isLink_succ_edge,
      succ_ne_pred_castSucc, deg_two_split}` — the last five expose the per-`i` `(v,a,b,e_a,e_b)` split
      tuple `case_III_rank_certification` consumes). The indexing + geometry prereq is discharged.
      **CHAIN-2a design-pass LANDED 2026-06-18 (design §(m)): VERDICT = re-index, not construct.**
      CHAIN-2a = a `case_III_arm_realization` (general-`k`) re-index off the accessors, with the per-`i`
      gates threaded from two general-`k` producers (W6b `exists_candidateRow_bottomRows_of_rigidOn` +
      CHAIN-4d discriminator). **W6b half LANDED 2026-06-18** — `chainData_split_w6b_gates`
      (`CaseIII/Realization.lean`, axiom-clean), the first producer call: a `{k}`-general flat-tuple
      lift of the d=3 dispatch's W6b region producing the chain-order `hρe₀`/`hρGv`/`hw`/`hwmem` bundle.
      **Build finding: the discriminator half is NOT single-`i`** (it picks an arbitrary panel `u`;
      matching `u` to candidate `i` is the family glue) → folds into **CHAIN-2c**, not a 2a-i sub-leaf.
      Remaining: **CHAIN-2a-ii `chainData_split_realization`** (the per-`i` reduction core = the
      `case_III_arm_realization` re-index, consuming `chainData_split_w6b_gates` + a CHAIN-2c-supplied
      transversal gate). Then CHAIN-2b/2c. ~3 build commits remaining.
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
      Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature now FROZEN** by the CHAIN↔ENTRY contract (`notes/Phase23-design.md`
      §"CHAIN↔ENTRY contract" C.3): `hdispatch` consumes a `G.ChainData n` record
      (the length-`d` chain) + the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0
      fact + the IH-generic base realization on that split. Keep the `d=3` dispatch
      as a `k=2`/length-3 wrapper (no `d=3` regression — C.4 zero-regression map).
- [x] **CHAIN tail — lift the four 23a-carried producers (OD-7 fold). CLOSED 2026-06-18.** After
      CHAIN-3, all four 23a-carried producers (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + both M4
      halves are general-`k`; the *one* genuinely-new piece was LEAF-0
      `linearIndependent_normals_of_algebraicIndependent_triple`. Detail: design §(k) + git +
      *Decisions made* → *Landed OD-7 bricks*.

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
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`), **and OD-7 (the four-producer tail) is
CLOSED** — all four 23a-carried producers + both M4 halves are general-`k` (see *Current state* +
*Decisions made* → *Landed OD-7 bricks*). The last OD-7 leaf, `case_I_dispatch_gen` + the
`hcontract_k` wire-up, landed 2026-06-18.

**Next = CHAIN-2a-ii `chainData_split_realization` (the per-`i` reduction core, the
`case_III_arm_realization` re-index) — or CHAIN-2b/2c.** **The W6b half of the gate-producer LANDED
2026-06-18** — `chainData_split_w6b_gates` (`CaseIII/Realization.lean`, axiom-clean): the first of
the design's two producer calls, a `{k}`-general flat-tuple lift of the d=3 dispatch's W6b region
emitting the chain-order W6b gate bundle (`ρ`/`w` + `hρe₀`/`hρGv`/`hw`/`hwmem` + the base
genericity/link-recording). **Build finding refining §(m): the discriminator half of the gate-producer
is NOT single-`i`** — `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` needs the `Fin (k+1)`
chain-panel-normal family and *picks an arbitrary panel `u`*; matching `u` to candidate `i` is the
family disjunction, so the discriminator half folds into **CHAIN-2c** (the "discriminator-picks-`i`
glue" §(m)/line 50 already names), not a 2a-i sub-leaf. CHAIN-2a-ii then re-indexes
`case_III_arm_realization` off the landed interior-split accessors, feeding it
`chainData_split_w6b_gates` (W6b half) + a CHAIN-2c-supplied transversal gate (`hLn`/`hρgate`). The
`ChainData` record + accessors are landed, so 2a-ii can bind `cd : G.ChainData n` and reach the split
tuple directly. Then CHAIN-2b/2c; or **CHAIN-5/ENTRY** (CHAIN-5 gated on the rest of CHAIN-2 + ENTRY's
extractor reshape). The one clause-(ii) flag (§(m)) is build-time wiring (which arm form + the
`h622lb`/`hIH` instantiation at the `vᵢ`-split), not a motive/carried-hypothesis change.

- **CHAIN-2 — the `Fin d`-indexed candidate-reduction layer (eqs. 6.59–6.64)** (`CaseIII/`),
  **decomposed at recon (design §(l)), which corrected the §(c) framing:** the `caseIIICandidate` /
  `case_III_old_new_blocks` / `case_III_rank_certification` chain is **already general-`k`** (the only
  `d=3`-pin in `CaseIII/` is the `Realization.lean` dispatch shell = CHAIN-5). CHAIN-2 builds the
  `Fin d`-indexed reduction LAYER *on top of* that (reused-verbatim) chain + the closed CHAIN-1
  `ιc`-block augment: **CHAIN-2a** (per-candidate single-`i` reduction — design-pass §(m) verdict: a
  `case_III_arm_realization` re-index, gates threaded from two producers; **W6b half LANDED** as
  `chainData_split_w6b_gates`, the discriminator half folded into CHAIN-2c per the build finding;
  remaining 2a-ii `chainData_split_realization` re-indexes the arm closer) → **CHAIN-2b**
  (the ±r chain, eq. 6.66; genuinely-new structure) → **CHAIN-2c** (the `Fin d` family assembly +
  the discriminator-picks-`i` glue; consumes CHAIN-1 + the CHAIN-4d discriminator). ~3 build commits
  (the zeroth `ChainData` leaf + interior-split accessors + W6b-half are done; the 2a design-pass is
  done). **Zeroth-leaf
  prerequisite DISCHARGED:** the `G.ChainData n` `structure` (contract C.1, `Induction/Operations.lean`)
  LANDED 2026-06-18 — the ~15-field length-`d` chain record with `deg_two` settled (`0 < (i:ℕ)` interior
  guard; predecessor edge `edge ⟨(i:ℕ)-1, _⟩`; d=3-map verified per C.4); the **interior-split geometry
  accessors** `ChainData.{pred_succ_eq_castSucc, isLink_pred_edge, isLink_succ_edge,
  succ_ne_pred_castSucc, deg_two_split}` (alongside `pred_edge_ne`/`isLink_edge`) then expose, for an
  interior index `i` (`0 < (i:ℕ)`), the per-`i` `(v,a,b,e_a,e_b)` split tuple in the exact shape
  `case_III_rank_certification` consumes — split body `vtx i.castSucc`, the two chain edges `edge i` /
  `edge ⟨(i:ℕ)-1,_⟩` oriented out of it, their distinct neighbors, and the re-oriented degree-2 closure.
  So CHAIN-2a's signatures can now bind `cd : G.ChainData n` and reach the split tuple directly. The
  record *definition* is the sharable half of the contract; ENTRY still owns the extractor that
  *produces* it (C.2).

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
record (C.1/C.3), so it is now authorable. **CHAIN-2's *linear algebra* is independent
of the contract, but its *indexing* is contract-coupled** (recon §(l) overturned the
old "CHAIN-2 fully independent" claim): the `ChainData` record it indexes **is now authored
in Lean** (`Induction/Operations.lean`, 2026-06-18, the zeroth leaf — `deg_two` settled), so
the indexing prereq is discharged. CHAIN-5 is unblocked once the rest of CHAIN-2 lands
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
- **CHAIN-2 decomposition (recon 2026-06-18, read-only Plan + coordinator source-verify) — overturns
  §(c)'s framing.** The named `caseIIICandidate`/`case_III_old_new_blocks`/`case_III_rank_certification`
  chain is **already general-`k`** (the only `d=3`-pin in `CaseIII/` is `Realization.lean`'s dispatch =
  CHAIN-5); §(c)'s "(now `q : α × Fin 4`-shaped)" was false. CHAIN-2 = the `Fin d`-indexed reduction
  *layer* (2a per-`i` / 2b ±r-chain / 2c family) on top of that chain + closed CHAIN-1 →
  §"CHAIN"(l).
- **CHAIN-2a design-pass (2026-06-18) — VERDICT: re-index, gates threaded from above** (settles the
  session-#7 open question against the landed bodies). CHAIN-2a's per-`i` reduction is a
  `case_III_arm_realization` (general-`k`) re-index, NOT a from-scratch gate construction: the gate
  family is carried as hypotheses by both the certification (`Candidate.lean:1403`) and the arm closer
  (`Arms.lean:72`), and supplied from above by two general-`k` producers (W6b
  `exists_candidateRow_bottomRows_of_rigidOn` + CHAIN-4d discriminator, fed by
  `case_III_nested_rank_lower_all_k`). Sub-leaves: CHAIN-2a-i `chainData_split_arm_gates` (the two
  producer calls) → CHAIN-2a-ii `chainData_split_realization` (the arm-closer re-index). One
  build-time wiring flag (arm form + `h622lb`/`hIH` instantiation), no motive change → §"CHAIN"(m).
- **CHAIN-2a-i W6b half LANDED 2026-06-18 + a sub-leaf-boundary refinement of §(m).**
  `chainData_split_w6b_gates` (`CaseIII/Realization.lean`, axiom-clean): a `{k}`-general flat-tuple
  lift of the d=3 dispatch's W6b region (`case_III_candidate_dispatch` steps 3–4) — one
  `exists_candidateRow_bottomRows_of_rigidOn` call (fed the `∀ ends q` carry-shaped `h622lb` from
  `case_III_nested_rank_lower_all_k`) producing the chain-order-normalized `ρ`/`w` +
  `hρe₀`/`hρGv`/`hw`/`hwmem` bundle + the base `IsGeneralPosition`/`Gᵥ`-link-recording. Flat-tuple
  (not `ChainData`-bound) so it is reusable by 2a-ii AND callable by the d=3 dispatch at `k=2`; the
  d=3 dispatch left unchanged (the producer is a verbatim extraction, both green). **§(m) refinement
  (build finding): the discriminator half is NOT a single-`i` sub-leaf** —
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` picks an *arbitrary* panel `u`, and the
  gate `hρgate` is about `n u` not the candidate-`i` normal `na`; matching `u` to `i` is the family
  disjunction, so the discriminator half folds into CHAIN-2c (the "discriminator-picks-`i` glue" §(m)
  already names there), not 2a-i. The honest "two producer calls" are W6b (single-`i`, landed) +
  discriminator (family-level, CHAIN-2c). Axiom-clean; no FRICTION (the only non-verbatim step,
  `2 ≤ screwDim 2 := by decide` → `two_le_screwDim hk1`, is the landed §58 numeral-pass kit).
- **`G.ChainData n` record LANDED 2026-06-18 (CHAIN-2 zeroth leaf)** — the contract-C.1 length-`d`
  chain `structure` in `Induction/Operations.lean` (the `splitOff` home): fields `d`/`hd`/`vtx :
  Fin (d+1)→α`/`edge : Fin d→β`/`e₀` + `vtx_mem`/`vtx_inj`/`link`/`edge_inj`/`deg_two`/`e₀_fresh`,
  plus accessors `ChainData.pred_edge_ne`/`isLink_edge`. **`deg_two` settled:** interior vertices
  guarded by `0 < (i:ℕ)` (no `OfNat (Fin d)` literal — the `0`/`1` `Fin d` literals fail to synth at
  general `d`), predecessor edge as `edge ⟨(i:ℕ)-1, _⟩`; d=3-map (C.4) verified by `rfl`/`decide`
  (`vtx 1=v`, `vtx 2=a`; closures `edge 0=e_b`, `edge 1=eₐ`, `edge 2=e_c`). `n` is a phantom index
  (no field uses it) carried only so the contract can write `G.ChainData n`. Axiom-clean; no FRICTION.
- **`ChainData` interior-split geometry accessors LANDED 2026-06-18 (CHAIN-2 zeroth leaf, part 2)** —
  five `ChainData.{pred_succ_eq_castSucc, isLink_pred_edge, isLink_succ_edge, succ_ne_pred_castSucc,
  deg_two_split}` lemmas (`Induction/Operations.lean`) exposing, for an interior index `i` (`0 < (i:ℕ)`),
  the per-`i` `(v,a,b,e_a,e_b)` split tuple `case_III_rank_certification` consumes: split body
  `vtx i.castSucc`; the two chain edges `edge i` / `edge ⟨(i:ℕ)-1,_⟩` oriented *out of* it (the
  predecessor via `pred_succ_eq_castSucc` — `(⟨(i:ℕ)-1,_⟩).succ = i.castSucc` — then `.symm`); distinct
  neighbors `vtx i.succ ≠ vtx (⟨(i:ℕ)-1,_⟩).castSucc`; and the degree-2 closure re-oriented (`Or.symm`
  of the field). Same `0 < (i:ℕ)` + `congrArg Fin.val`/`omega` idiom as `pred_edge_ne`. Axiom-clean; no
  FRICTION (the `Fin.coe_castSucc → val_castSucc` deprecation was a one-name swap).
- **OD-7 `hcontract_k` decomposition (recon 2026-06-18, read-only Plan + coordinator source-verify):**
  5 leaves (6 if h65 splits) — `all_k`/`nonsimple`/`h65`/`dispatch` numeral passes (one `_perp_grade`
  swap; `_all_k` is all-*dof* not all-grade, a trap), the *one* genuinely-new piece LEAF-0
  `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI at `Fin (k+2)`; landed
  `…_general` gives `k+1` rows, h65 has only 3 vertices). No motive/IH change → §"CHAIN"(k).

**Landed CHAIN-3 bricks** (the `_grade` lifts are verbatim — the route is general mathlib, grade
enters nothing; `d=3` names kept as `(d:=3)` instances, no blueprint pin moved). CHAIN-3 is CLOSED;
construction internals live in git + `notes/Phase23-design.md` §"CHAIN"(f)/(h) + the
BlueprintExposition CHAIN-3 entry (the duality KT leaves implicit,
`extensor_join_proportional_complementIso_meet`). The two forward cleanup-candidates are the `[~]`
sub-bullet under the *CHAIN leaf checklist* CHAIN-3 entry.

**Landed OD-7 (four-producer tail) bricks** (OD-7 CLOSED 2026-06-18; per-brick names + the `hcontract_k`
five-leaf split + construction internals live in git + commit messages + `notes/Phase23-design.md`
§(k), the canonical home; all axiom-clean).
All four producers + both M4 halves are now general-`k` via verbatim numeral passes over the d=3 bodies
(`screwDim/ScrewSpace 2→k`, `Fin 4→Fin (k+2)`, dof `k→c`; d=3 lemmas now `k:=2` wrappers/instances,
blueprint pins unmoved, §58 idiom). Two settled cross-cutting notes: the *one* genuinely-new piece was
LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI, **not** a numeral
pass — the landed `…_general` gives `k+1` rows, h65 has only 3 vertices); the M4-forget reach-in routes
solely through the CHAIN-3 (h-4) duality + the new slot-0 rescale `extensor_update_smul` (confirming
caveat (e): the duality *is* the only M4-forget d=3 reach-in).

**Landed CHAIN-4 bricks** (CHAIN-4 CLOSED 2026-06-18, `RigidityMatrix/Claim612.lean`; leaf names + per-leaf
verdicts + construction internals live in git + `notes/Phase23-design.md` §(i)/(j), the canonical home;
all axiom-clean). Two settled cross-cutting notes:
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

- *`Fin d`-index arithmetic at general `d` (no `+1`): a `0 < i` guard / `i - 1` predecessor wants
  `OfNat (Fin d)` literals that don't synth — for plain index bookkeeping (not a `d=0`-false slot),
  guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩` rather than carry `[NeZero d]`* → FRICTION [idiom]
  *`Fin d`-index arithmetic (general `d`): guard `0 < (i:ℕ)`…*.
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
