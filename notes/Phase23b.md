# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2 (the `Fin d` reduction layer — T-W9a span fold LANDED; the bottom-family transport
FIX-FORK is SETTLED 2026-06-19 §(o‴)(H): corrected Fix A = invert the relabel to `(shiftPerm i)⁻¹` +
shared `ρ₀`; Fix B infeasible. Inverse-cycle action block LANDED; NEXT = the `i=3` base→candidate
single-step seed-advance de-risk gate; see *Hand-off*)
+ CHAIN-5 (the dispatch assembly, gated by the ENTRY-contract reshape).**
The integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase
boundary; codes-until-open).

**Orientation.** The **23b (CHAIN layer)** rolling state + hand-off. Cross-phase plan/guidance + the
detailed leaf-level recon live in `notes/Phase23-design.md` (§"CHAIN": (a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions); program map
`notes/MolecularConjecture.md`. **Sub-phase codes** (a letter + work log minted when a layer opens, so
a later split costs no renumber-churn): `CARRIER`(=23a, closed), `CHAIN`(=23b), `ENTRY`/`ASSEMBLY`
(code-only until their turn).

## Current state

**FIX-FORK SETTLED (§(o‴)(H), docs-only design-pass 2026-06-19, KT §6.4.2 read verbatim + landed bodies
via lean-lsp). VERDICT: corrected Fix A (invert the relabel to `(shiftPerm i)⁻¹`, keep the shared `ρ₀`).
Fix B is INFEASIBLE; the "reuse `chainData_split_realization` per-`i`" simplification does NOT hold.**

**Why Fix B / the per-`i` simplification fail (mathematical, in KT's structure — not a punt).** KT's
full-rank existence (6.65–6.67) rests on **ONE** functional `r = ρ₀`, tested against ALL `d` panels (a
single `r≠0` can't annihilate the `D`-dim span, Lemma 2.1). A per-`i` W6b produces an independent `ρᵢ`
(`Classical.choice`, no provable bridge to `ρ₀`), so the shared-`ρ₀` discriminator's panel pick can't
discharge candidate `i`'s `htrans` (quantified over `ρᵢ`) — and running the discriminator per-`i` loses
KT's single-`r` disjunction. This is exactly §(o′) route A, already REJECTED (§(o″)(1)). Landed-body
checks: the producer supplies ONLY the `v₁`-split realization (`Arms.lean:854`), the d=3 dispatch shares
ONE `ρ₀` across all arms (`Realization.lean:404/439/495`), `chainData_split_realization` (the per-`i` arm)
has ZERO live callers.

**Why corrected Fix A works.** Keep the shared `ρ₀`/`w`; transport row-memberships into candidate `i`'s
role by the **inverse cycle** `(shiftPerm i)⁻¹`. The inversion cancels the seed: base row `hingeRow x y r`
↦ `hingeRow (ρ⁻¹x)(ρ⁻¹y) r`, candidate extensor at `qᵢ=q∘ρᵢ` reads `C(q(ρ·ρ⁻¹x),…) = C(qx,qy)` — the seed
`ρ` and relabel `ρ⁻¹` cancel, so the annihilation transports. This matches KT (6.62)'s one-step-DOWN
correspondence `vⱼ₋₁ ⇐⇒ vⱼ` exactly (the forward `funLeft (shiftPerm i)` over-shifted to `ρ²`; `shiftPerm
i` not an involution for `i≥3`, masked at d=3 by `shiftPerm 2 = swap`). The full verdict — KT deciding
lines, the tear-up/keep lists, the buildable leaves, route-β + d=3 dispositions — is `notes/Phase23-design.md`
§(o‴)(H).

**Adversarial verification §(o‴)(H.10) (read-only recon, opus): Fix-B rejection + the corrected-Fix-A
seed-cancellation algebra CONFIRMED, but H.5/H.7's "reuse the landed T-W9a *through its inverse*"
REFUTED — a structural blocker, not a residual.** The landed T-W9a/W9b folds are candidate→base /
seed-FIXED; the arm needs base→candidate / seed-jumping `q→qρ`; `wstep` is non-invertible (rank-degrading
a-column subtraction), so the fold cannot be inverted. **Correction:** re-author the transport
base→candidate directly (reuse the base→candidate single-step `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`,
re-fold in opposite order, seed advancing); the **landed candidate→base T-W9a/W9b are orphaned *for the
arm***. **De-risk gate: write the base→candidate single-step seed-advance lemma at `i=3` first.**

**Tracker (CHAIN-2c-ii-transport):** inverse-cycle action block (2c-ii-inv) **LANDED 2026-06-19**
(11 axiom-clean `shiftPerm_inv_*`/`shiftEdgePerm_inv_*` lemmas, `Operations.lean`; one-liner
`Equiv.Perm.inv_eq_iff_eq` rewrites of the forward action) → **NEXT: base→candidate single-step
seed-advance at `i=3`** (de-risk gate, H.10) → base→candidate cycle fold → 2c-ii-arm
`chainData_relabel_arm` (d=3 M₃ = `i=2` involution instance) → 2c-iii `chainData_dispatch` → CHAIN-5.
(Landed candidate→base T-W9a/W9b + per-body W9b chain = orphaned-for-the-arm, §(o‴)(H.10).)

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm;
route B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + §(o″).)

**Context (closed/landed):** CHAIN-1/3/4 + OD-7 CLOSED; `G.ChainData n` + 7 accessors; CHAIN-2a
CLOSED; 2c-i + 2c-ii-α/graphiso + 2c-ii-inv LANDED. The landed candidate→base T-W9a span fold + the
per-body W9b chain are **orphaned-for-the-arm** (wrong orientation/granularity, §(o‴)(H.10);
confirm-and-delete at the arm build). Remaining (tracker above): base→candidate single-step seed
advance (`i=3` de-risk) → cycle fold → 2c-ii-arm → 2c-iii → CHAIN-5 + ENTRY's extractor reshape.

**Standing context (settled; full detail in the design doc).** (1) *Architectural:* metric-using Hodge
leaves live in `MeetHodge.lean`, never metric-free `Meet.lean` (a `PiL2` import → `whnf` timeout) —
TACTICS-QUIRKS § 59. (2) *Orientation:* the arm-engine is already general-`k`; CHAIN replaced only the
d=3 dispatch + its `⋀²ℝ⁴` discriminator with the `d`-candidate chain + `⋀^{d−1}` duality finish. (3)
*Contract (SETTLED):* the CHAIN↔ENTRY `G.ChainData n` shape is frozen — three lockstep decls (ENTRY
extractor / producer `…hcand` / CHAIN-5 `hdispatch`), no motive/IH change (C.6), `d=3` zero-regression
(design §"CHAIN↔ENTRY contract").

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)/(l)/(m)/(n)/(o)/(o′)/(o″)). **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 +
CHAIN-2a CLOSED; CHAIN-2c-i + 2c-ii-α/β + 2c-ii-graphiso COMPLETE.** Remaining in **CHAIN-2c-ii**:
**2c-ii-transport** (route B, §(o″); T-W9a's linear-algebra layer landed, **(T-W9a-chain)** next) →
**2c-ii-arm** (the closer) — then
**CHAIN-2c-iii** (assembly), and **CHAIN-5** (signature frozen by the CHAIN↔ENTRY contract; gated on
the rest of CHAIN-2 + ENTRY's extractor reshape).

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
- [ ] **CHAIN-2 — the `Fin d`-indexed candidate-reduction layer (eqs. 6.59–6.67)** (`CaseIII/`).
      Zeroth leaf (`G.ChainData n` record + 7 interior-split accessors, `Induction/Operations.lean`)
      + **CHAIN-2a** (per-candidate single-`i` reduction: `chainData_split_w6b_gates` +
      `chainData_split_realization`, both axiom-clean) **LANDED/CLOSED 2026-06-18.** Remaining:
      **CHAIN-2c — the single-base `Fin (k+1)` family dispatch** (route β, design §(n)/(o)): ONE base,
      ONE `ρ₀`, ONE discriminator → `fin_cases u`; eq. (6.66) absorbed. **2c-i**
      (`exists_chainData_discriminator_pick`) LANDED. **2c-ii** (the genuinely-new relabel arm, NOT a
      numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle): foundation (`shiftPerm` / graphiso
      `splitOff_isLink_shiftRelabel_iff`) LANDED. **FIX-FORK SETTLED §(o‴)(H)+(H.10): corrected Fix A** —
      keep the shared `ρ₀`, transport memberships **base→candidate** (relabel `(shiftPerm i)⁻¹` + the seed
      advancing); Fix B / per-`i` re-seed INFEASIBLE (breaks KT's single-`r` discriminator). The landed
      candidate→base T-W9a fold + the per-body W9b chain are **orphaned-for-the-arm** (H.10) → **2c-ii-inv**
      (inverse-cycle action lemmas) **LANDED 2026-06-19** → **NEXT: base→candidate single-step
      seed-advance (`i=3` de-risk)** → cycle fold → **2c-ii-arm** `chainData_relabel_arm` (d=3 M₃ =
      `i=2` involution) → **2c-iii** `chainData_dispatch`. Full detail: design §(o‴)(H)/(H.10).
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

**FIX-FORK SETTLED (§(o‴)(H), 2026-06-19): corrected Fix A.** No motive/IH/spine-carry change (C.3/C.6);
route β preserved; `d=3` zero-regression preserved. The full verdict (KT deciding lines, leaf signatures,
tear-up/keep lists) is `notes/Phase23-design.md` §(o‴)(H); the rationale is *Current state* above.

**CHAIN-2c-ii-inv (the inverse-cycle action block) is LANDED** (2026-06-19; `Operations.lean`, beside
`shiftPerm`/`shiftEdgePerm`): the 4 `shiftPerm_inv_*` (`_apply_interior`/`_vtx_one`/`_apply_off`/
`_apply_vtx_off`) + 7 `shiftEdgePerm_inv_*` (`_apply_off`/`_apply_edge_off`/`_apply_e₀`/
`_apply_edge_top`/`_apply_edge_interior`/`_apply_edge_one`/`_apply_edge_zero`), all axiom-clean,
each a one-liner `rw [Equiv.Perm.inv_eq_iff_eq, <forward action lemma>]` (the `inv_eq_iff_eq`
idiom — FRICTION, under the `formPerm`-cycle entry). Self-contained, graph-free.

**NEXT STEP — the H.10 de-risk gate: the base→candidate single-step seed-advance lemma at `i=3`**
(first non-involution case, cycle length 2). **Do NOT build `chainData_relabel_arm` (or pin its
signature / the cycle fold) until this single-step closes** — the §(o‴)(H.10) adversarial verification
REFUTED H.5/H.7's "reuse the landed T-W9a *through its inverse*": the landed T-W9a/W9b folds are
candidate→base/seed-fixed, the arm needs base→candidate/seed-jumping, and `wstep` is non-invertible
(rank-degrading a-column subtraction). The arm transport must be **re-authored base→candidate**:
source `F 0 = G−v₁` seed `q`, target `F(i−1) = G−vᵢ` seed `q∘shiftPerm i`, per-step relabel
`(shiftPerm)⁻¹` (now landed), the seed advancing one swap per step — reuse the base→candidate
single-step `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, re-folded in opposite chain order.
Write + close the `i=3` instance first — exactly the kind of "mechanically plausible" shape the 4×
mis-pins were.

**Then:** **2c-ii-arm** `chainData_relabel_arm` (signature in §(o‴)(H.6); instantiate
`case_III_arm_realization` at the relabelled roles with seed `qρ = q∘shiftPerm i`, shared `±ρ₀`, the three
slots transported via the **base→candidate cycle fold** of W9a/W9b/G4d-i (H.10, NOT the inverse of the
landed folds); est. ~3–5 commits; d=3 M₃ = `i=2` involution instance) → **2c-iii** `chainData_dispatch`
(the `Fin (k+1)`-case dispatch, `M₀` = direct arm, interior = relabel arm; replaces
`case_III_candidate_dispatch`) → **CHAIN-5**.

**Confirm-and-delete at the reshape** (orphans, `git grep` zero live callers at the deleting commit; full
list §(o‴)(H.5)): the per-body W9b chain `bottomTag_foldr_mem_rigidityRows` + §(o″) single-step
`funLeft_dualMap_bottomTag_mem_rigidityRows` + `redundancy_panel_carry`,
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`, `ofNormals_relabel_perm` (2c-ii-β); and the
per-`i` W6b architecture `chainData_split_realization` + `chainData_split_w6b_gates` (zero callers — Fix B
would have used them; **re-check at the 2c-iii build** whether the dispatch reuses the `v₁`-split W6b via
`chainData_split_w6b_gates` at `i=1` or inlines it as d=3 does). `candidateRow_ac_eq_neg` likely
**re-consumed** by Fix A's `±r` block arm — re-check, don't blind-delete (§(o‴)(F)). The landed
candidate→base T-W9a span fold `shiftBodyList_foldr_mem_span_rigidityRows` is **orphaned-for-the-arm**
(wrong orientation, §(o‴)(H.10) — it proves the converse implication; the base→candidate single-step
`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` it folds over IS reused). **STAYS:** that single-step
lemma, the graph iso `splitOff_isLink_shiftRelabel_iff` + `shiftEdgePerm`, G4d-i
`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, the W6b `ρ⊥C(q(ab))` gate, 2c-i
`exists_chainData_discriminator_pick`, the `ChainData` record + accessors.
**`d=3` zero-regression:** at `i=2` the cycle is `shiftPerm 2 = (v₁v₂)`, an involution where
`(shiftPerm 2)⁻¹ = shiftPerm 2`, so Fix A's inversion is a no-op and the arm reduces to the landed M₃
engine verbatim; the current `case_III_candidate_dispatch` stays green untouched until CHAIN-5/ENTRY wrap
it (C.4).

- **CHAIN-2c — the single-base `Fin (k+1)` family dispatch (design §(n)/§(o)/§(o‴)(H)).** Route β LOCKED
  (user-adjudicated 2026-06-18, KT-source-verified): ONE base `(G₁,q₁)` (the `v₁`-split = `M₀`), ONE
  `ρ₀`, ONE W6b call, ONE discriminator call, then `fin_cases u`; eq. (6.66)'s ±r chain absorbed into
  reusing one `ρ₀`. The relabel arm (2c-ii) covers the interior candidates `2 ≤ i ≤ d−1` (a
  genuinely-new construction, NOT a numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle, the d=3 engines are
  transposition-only). **M₀-arm SETTLED (§(o‴)(H), corrects the prior "2a-ii is the M₀ arm" pin):** the
  `M₀` candidate is the **direct** `case_III_arm_realization` with the shared `ρ₀` (as d=3 M₁), NOT
  `chainData_split_realization` — the latter is the per-`i`-W6b (Fix B) architecture that does not
  assemble against the single-`ρ₀` discriminator, so it joins the confirm-and-delete orphans. The 2c-ii
  leaf decomposition (corrected Fix A) lives in **checklist CHAIN-2** + design §(o‴)(H). No motive/IH or
  spine-carry change. The `G.ChainData n` record + 7 accessors (C.1) are landed; ENTRY owns the
  extractor (C.2).

  **Blueprint-clarity obligation (owner-flagged 2026-06-18 — "absolutely clear").** Route β **absorbs**
  KT's explicit index-shift isos (6.54–6.56) + ±r chain (6.66) into the Lean `shiftPerm` relabel arm —
  so the `lem:case-III` general-`d` node's prose MUST materialize them explicitly (§(o)/§(o′) pin the
  four ordered points): (1) the single-`v₁`-base construction; (2) the index-shift iso `ρᵢ` (the
  `(i−1)`-cycle) and "exactly the same framework" via it; (3) the single redundancy `r` (eq. 6.52)
  carried ±-ly across the `d` panels (eq. 6.66) — the §(o′)(B) route-A eq.-(6.66) identity / route-B
  degree-2 mechanism is exactly this step; (4) the (6.67) discriminator (Lemma 2.1 on the `d+1`
  points). The Lean economizes; the exposition must not. Tracked in BlueprintExposition (the
  `lem:case-III` general-`d` entry, extending the d=3 `lem:case-III-claim612-eq644`); written as
  2c-ii/CHAIN-5 land + at phase-close.

Re-pointing the d=3 discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence` at CHAIN-4d's
`k:=2` instance (h-5) is now an available but **not-forced** simplification — the d=3 body + its
`complementIso_smul_eq_extensor_join` wrapper stay green meanwhile; defer to ASSEMBLY/cleanup. **The
OD-8 route β stays rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count —
distinct from the CHAIN-2c "route β" just locked above; this is the CHAIN-3/OD-8 duality route). The CHAIN-3-finish
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
- **CHAIN-2a CLOSED 2026-06-18 — the complete single-`i` reduction (re-index verdict CONFIRMED).**
  Two axiom-clean leaves in `CaseIII/Realization.lean`: `chainData_split_w6b_gates` (the `{k}`-general
  flat-tuple W6b half) + `chainData_split_realization` (the re-index core, reads the per-`i` split off
  the `ChainData` accessors and calls `case_III_arm_realization` directly — no `_M3` relabel). **The
  transversal half stays a hypothesis `htrans`** — the single-`i` slot CHAIN-2c fills via the
  discriminator (the arbitrary-panel `u`↔candidate `i` match is the family glue). Internals + §(m)
  clause-(ii) resolution in git/design §(m). No FRICTION.
- **CHAIN-2b/2c design-pass (2026-06-18) — VERDICT: single-base `Fin (k+1)` dispatch (route β), ±r
  chain absorbed (no separate 2b lemma).** Single base `(G₁,q₁)` / one `ρ₀` / one discriminator /
  `fin_cases u`. Route β LOCKED (user-adjudicated, row 242). Detail `notes/Phase23-design.md` §(n).
- **The bottom-family-transport recon trail** (route B per-body W9b fold → telescoping pass ruled it dead
  → pair recon refuted the forward whole-relabel → §(o‴)(H) corrected Fix A) lives in design
  §(o)–(o‴)(H.10) + git; the live verdict is the next entry, not the trail.
- **FIX-FORK ADJUDICATION 2026-06-19 (§(o‴)(H), docs-only, KT §6.4.2 verbatim + landed bodies via
  lean-lsp) — VERDICT: corrected Fix A; Fix B INFEASIBLE.** The §(o‴)(G) pair recon refuted the forward
  `funLeft (shiftPerm i)` (over-shifts the seed to `ρ²`; `shiftPerm i` not an involution for `i≥3`, masked
  at d=3 by `shiftPerm 2 = swap`; KT (6.62) is one-step-down `ρ⁻¹`). Fix B / the "reuse
  `chainData_split_realization` per-`i`" simplification fail **fundamentally**: a per-`i` W6b gives an
  independent `ρᵢ` with no bridge to the shared `ρ₀`, breaking KT's single-`r`-against-all-panels
  existence (6.65–6.67) — = §(o′) route A, already rejected. Fix A keeps `ρ₀` + inverts to `(shiftPerm
  i)⁻¹` (cancels the seed `ρ`, matches KT (6.62)); route β + d=3 preserved. First buildable =
  `shiftPerm_inv_*` action block. Detail §(o‴)(H).
- **ADVERSARIAL VERIFICATION of §(o‴)(H) 2026-06-19 (read-only recon, opus → §(o‴)(H.10)): Fix-B
  rejection + corrected-Fix-A algebra CONFIRMED; H.5/H.7 "reuse T-W9a through its inverse" REFUTED.** The
  landed T-W9a/W9b folds are candidate→base/seed-fixed; the arm needs base→candidate/seed-jumping; `wstep`
  is non-invertible (rank-degrading a-column subtraction), so the fold can't be inverted. **Correction:**
  re-author the transport base→candidate directly (reuse the base→candidate single-step
  `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, re-fold opposite order, seed advancing); the landed
  candidate→base T-W9a/W9b are orphaned-for-the-arm. First leaf (inverse-action block) survives; de-risk
  at the `i=3` base→candidate single-step. No motive/IH/spine change. Detail §(o‴)(H.10).
**Landed CHAIN-2 leaves (all axiom-clean; detail = git + design §(o)/(o′)/(o″) + FRICTION).** One-line
verdicts (settled; nothing downstream leans on the internals): **`G.ChainData n` record + accessors**
(`Induction/Operations.lean`, the contract-C.1 length-`d` chain + the interior-split `(v,a,b,e_a,e_b)`
geometry accessors; `Fin d`-index idiom in FRICTION). **CHAIN-2c-i** `exists_chainData_discriminator_pick`
(`Realization.lean`, the route-β single-discriminator pick, verbatim generalization of the d=3
region). **2c-ii-α** `ChainData.shiftPerm` (KT eq. 6.54) + recursion handle
`shiftCycle_eq_cons`/`shiftPerm_eq_swap_mul`. **2c-ii-graphiso** `splitOff_isLink_shiftRelabel_iff` +
`shiftEdgePerm` (the `hiso` supplier, consumed at the **arm**). **2c-ii-inv** (the inverse-cycle action
block, LANDED 2026-06-19) the 4 `shiftPerm_inv_*` + 7 `shiftEdgePerm_inv_*` action lemmas — each a
one-liner `rw [Equiv.Perm.inv_eq_iff_eq, <forward>]`; the base→candidate relabel `(shiftPerm i)⁻¹` the
re-authored arm transport carries (FRICTION, under the `formPerm`-cycle entry). **2c-ii-transport-W9a** (the
genuinely-new span crux — STAYS modulo the §(o‴)(H.7) orientation reconcile, transports the candidate row
`hρGv`) `shiftBodyList_foldr_mem_span_rigidityRows` (fold core + `shiftBodyFramework`/`_htrans` removeVertex
chain; span-only, endpoints removeVertex NOT splits). **⚠ Orphans (confirm-and-delete at the arm build per
§(o‴)(H.5); *Hand-off* flag): the per-body W9b chain** `funLeft_dualMap_bottomTag_mem_rigidityRows` +
`bottomTag_foldr_mem_rigidityRows` + `redundancy_panel_carry` (+ `ofNormals_relabel_perm`,
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`), and the per-`i`-W6b architecture
`chainData_split_realization` + `chainData_split_w6b_gates` (Fix B's mechanism; re-check at 2c-iii) — the
corrected Fix A (inverse-cycle, shared `ρ₀`) replaces them. **OD-7 `hcontract_k`** = 5 leaves (mostly
numeral passes; the one genuinely-new piece LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple`).

**Landed CHAIN-1/3/4/OD-7 bricks (all CLOSED 2026-06-18, axiom-clean; canonical homes = git +
`notes/Phase23-design.md` §(f)/(h)/(i)/(j)/(k) + the BlueprintExposition CHAIN-3 entry).** One-line
verdicts (the closed forward sequence, nothing downstream leans on the internals): **CHAIN-1**
(`RigidityMatrix/Basic.lean`) the eq.-6.62 row-swap + `ιc`-block augment, graph-free over `ScrewSpace k`
(single-`Unit` predecessors as `ιc:=Unit` corollaries; the per-candidate column-op heterogeneity is
CHAIN-2's bookkeeping). **CHAIN-3** (`Meet`/`MeetHodge.lean`) the `⋀^{d−1}W`-is-a-line duality (the
two `[~]` forward cleanup-candidates are the checklist CHAIN-3 sub-bullet). **CHAIN-4**
(`RigidityMatrix/Claim612.lean`) the discriminator (4d's `MeetHodge` import did NOT regress the `⋀²ℝ⁴`
proofs; 4b stays its own green body — off-one-panel hyp + `LI ℝ p` via `hpbar` — not a `k:=2` wrapper).
**OD-7** (the four producers + both M4 halves general-`k`): verbatim numeral passes (§58 idiom) except
LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI, genuinely-new); the
M4-forget reach-in routes solely through CHAIN-3 (h-4) + `extensor_update_smul`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData`
  decl needs its full path including the inner `BodyHingeFramework` namespace (the ambient `namespace` is
  out of scope under `_root_.`; bare and `…Molecular.` both fail "Unknown identifier")* → FRICTION [idiom]
  *Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData`
  decl…*.
- *Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold:
  package via `dite` + a `dif_pos` `_eq` lemma, then `simp only` (not `rw`) the per-step resolutions
  (`rw` chokes on the proof-irrelevant `getElem` bound + the un-beta-reduced `dite` redex)* → FRICTION
  [idiom] *Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold…*.
- *Composing two `(funLeft σ).dualMap` relabel transports: both `funLeft` and `dualMap` are
  contravariant, so the rewrite chain is `← comp_apply` → `dualMap_comp_dualMap` → `← funLeft_comp`
  (the two contravariances cancel to `funLeft (σ₂ ∘ σ₁)`); group the corrections with `sub_sub` on
  the hypothesis only* → FRICTION [idiom] *Composing two `(funLeft σ).dualMap` relabel transports…*.
- *Recovering the other endpoint of a `Graph.IsLink` from a same-edge / same-left-endpoint pair: use
  `IsLink.right_unique` (`y = z` from `IsLink e x y`/`IsLink e x z`), not `eq_and_eq_or_eq_and_eq` +
  disjunct elimination* → FRICTION [idiom] *Recovering the other endpoint of a `Graph.IsLink`…*.
- *`rcases … with rfl` / `subst` fails when the equation's subject is a function application
  (`σ e = edge 0`), not a free local — name the eq and `rw … at` the link instead* → FRICTION [idiom]
  *`rcases hmem with rfl | …` / `subst` fails when the equation's subject is a function application…*.
- *A finite-`i`-cycle permutation over an indexed family `vtx : Fin n → α` as `Equiv.Perm α`:
  `List.formPerm (List.ofFn …)` (needs `[DecidableEq α]`); `Nodup` via `nodup_ofFn`, action lemmas
  via `formPerm_apply_lt_getElem` / `…_getElem` + `Nat.mod_self` / `…_of_notMem`* → FRICTION [idiom]
  *A `Fin n → α` indexed-family cycle as an `Equiv.Perm`…*.
- *Dropping the involution from a `ρ = Equiv.swap`-relabel transport to a general `Equiv.Perm ρ`: the
  `ρ`/`ρ.symm` placement is forced — `qρ` keeps forward `ρ`, but `endsσρ` + the rigidity-pullback
  motion `S∘ρ.symm` flip to `.symm`; the vertex-region transport stays forward `ρ`* → FRICTION
  [idiom] *Dropping the involution from a `ρ = Equiv.swap`-relabel transport…*.
- *`rw [hidx]` on a `getElem` index `l[k]`/`l[k]'h` (the bounds proof depends on `k`) trips "motive
  is not type correct" — re-apply the indexing lemma at the new index, don't rewrite the index in
  place; the `List.ofFn _ = x :: …` head-peel sibling sidesteps it via `List.ext_getElem` + `match`*
  → TACTICS-QUIRKS § 61 (+ variant).
- *A `Fin d`-index relabel proof: destructure `m = m'+1` early so `m-1` reduces to `m'` by `rfl` (kills
  the §61 in-place index rewrites), and bridge `(i.castSucc:ℕ)` to `(i:ℕ)` in `omega` args with `simp
  only [Fin.val_castSucc]` — not `show` (style linter) or `rw [hicv]` (`hicv := rfl` errors)* → FRICTION
  [idiom] *A `Fin d`-index relabel proof over general `d`…*.
- *`Fin d`-index arithmetic at general `d` (no `+1`): a `0 < i` guard / `i - 1` predecessor wants
  `OfNat (Fin d)` literals that don't synth — for plain index bookkeeping (not a `d=0`-false slot),
  guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩` rather than carry `[NeZero d]`* → FRICTION [idiom]
  *`Fin d`-index arithmetic (general `d`): guard `0 < (i:ℕ)`…*.
- *Index a `Fin`-parametrized `def` (e.g. `shiftBodyGraph`) by its *minimal* validity bound (the
  vertex-index range `s+1 < d+1`), not the looser step-/cycle-level bound the consumers carry —
  coupling them re-derives the wrong arithmetic obligation at every instantiation offset* → FRICTION
  [idiom] *Index a `Fin`-parametrized `def` by its minimal validity bound…*.
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
