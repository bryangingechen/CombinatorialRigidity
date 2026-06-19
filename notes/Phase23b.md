# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2 (the `Fin d` reduction layer — T-W9a/T-W9b transport machinery LANDED; the W9b
MEMBERSHIP is BLOCKED on a fold-invariant reshape, the KT §6.4.2 telescoping crux — next is a
comprehensive telescoping-structure DESIGN-PASS, **user-adjudicated 2026-06-19**; see *Hand-off* for the
design-pass guidance) + CHAIN-5 (the dispatch assembly, gated by the ENTRY-contract reshape).**
The integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase
boundary; codes-until-open).

**Orientation.** The **23b (CHAIN layer)** rolling state + hand-off. Cross-phase plan/guidance + the
detailed leaf-level recon live in `notes/Phase23-design.md` (§"CHAIN": (a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions); program map
`notes/MolecularConjecture.md`. **Sub-phase codes** (a letter + work log minted when a layer opens, so
a later split costs no renumber-churn): `CARRIER`(=23a, closed), `CHAIN`(=23b), `ENTRY`/`ASSEMBLY`
(code-only until their turn).

## Current state

**Route B LOCKED (§(o″)). Telescoping DESIGN-PASS DONE (§(o‴), 2026-06-19) — VERDICT: FLAG-DON'T-FORCE
STOP. The W9b-membership crux is NOT a fold over the landed single-steps; it is a bottom-family-transport
RESHAPE (the `chainData_relabel_arm` `hwmem` slot), gated on one OPEN structural fact (see *Hand-off*).
No motive/IH/spine-carry change (C.3/C.6 unmoved).**

The §(o‴) design-pass (KT §6.4.2 pp.696–698 close-read + landed bodies + 2 machine-verified single-steps)
established the GLOBAL structure end-to-end and **ruled out every per-body fold-invariant**: (1) the
§(o″) single-pinned-`Tag` is dead — the carry `(funLeft (swap a v)).dualMap (hingeRow a b ρ) = hingeRow
v b ρ ≠ hingeRow c v ρ` leaves a generically-nonzero residual (machine-confirmed). (2) A pure-span `Tag`
`ψ ∈ span (G−vₛ).rows` carries the *genuine-row* disjunct (it IS the landed T-W9a) but **fails on the
`(ab)`-block disjunct** — that block row lives in the `ab`-edge block `Eb ⊄ span (G−vᵢ).rows`
(rank-provable, `Candidate.lean:339–355`), so the W9a step has no premise. (3) An accumulating-sum `Tag` fails identically
(the residuals do NOT telescope — no pairwise cancellation; each `hingeRow vₛ₊₂ b ρ` sits at a distinct
body pair with no later negative). **Root cause:** KT carries the redundancy GLOBALLY (one (6.52)
pushforward under the whole relabel `ρᵢ`, zero on `V∖{vᵢ}`, + one (6.44) at the single body `vᵢ`) — the
Lean per-body `shiftBodyList` fold is the right granularity for the *relabel* (T-W9a, done) but the WRONG
granularity for the *bottom family*, whose per-body residuals have no per-body home.

**The honest GLOBAL transport (§(o‴)(d))** is KT's (6.62) **whole-relabel row correspondence**: transport
the SHARED `w` by ONE `funLeft (shiftPerm i)`, reading `hwmem` membership off the graph-iso
`splitOff_isLink_shiftRelabel_iff` (genuine arm) + the single `±r` block at `vᵢ` via G4d-i (one (6.44)) —
the cycle generalization of the d=3 M₃ `case_III_bottom_relabel` genuine-row arm, NOT a `bottomTag_foldr`.
This abandons the per-body W9b chain; **the candidate-row `hρGv` T-W9a span half STAYS** (it transports
the candidate row correctly, machine-verified). The §(o‴) **FLAG**: one OPEN FACT must be reconned before
any build — whether the genuine `M₀`-row → genuine candidate-`i`-row correspondence closes against the
whole `shiftPerm i` + seed `qᵢ = q₁∘ρᵢ` (6.56). See *Hand-off*.

**The piecemeal recon→build loop mis-pinned this crux 4× (iter 3/7/9/11) — all per-body local pins.**
Confirm-and-delete once the reshape lands (now extended): the orphan bridge `redundancy_panel_carry` +
`candidateRow_ac_eq_neg`, AND (per §(o‴)) the per-body `bottomTag_foldr_mem_rigidityRows` +
§(o″) single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (the wrong granularity; the whole-relabel
transport replaces them). Tracker (CHAIN-2c-ii-transport): T-W9a ✓ (correct, stays) → per-body W9b chain
✗ (wrong granularity, §(o‴)) → **bottom-family whole-relabel transport [next — gated on §(o‴) OPEN FACT
recon]** → 2c-ii-arm → 2c-iii → CHAIN-5.

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm;
route B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + §(o″).)

**Context (closed/landed):** CHAIN-1/3/4 + OD-7 CLOSED; `G.ChainData n` + 7 accessors; CHAIN-2a
CLOSED; 2c-i + 2c-ii-α/graphiso + T-W9a span fold LANDED (the candidate-row half — STAYS). The per-body
W9b chain (step/fold core/bridge) is LANDED-but-orphaned (wrong granularity, §(o‴)). Remaining
(tracker): the bottom-family whole-relabel transport [gated on the §(o‴) OPEN FACT recon] → 2c-ii-arm →
2c-iii → CHAIN-5 + ENTRY's extractor reshape.

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
      `splitOff_isLink_shiftRelabel_iff`) + transport **T-W9a** span fold
      (`shiftBodyList_foldr_mem_span_rigidityRows`, transports the candidate row `hρGv` — STAYS, the
      candidate-row half is DONE) LANDED. The per-body W9b chain
      (`funLeft_dualMap_bottomTag_mem_rigidityRows` / `bottomTag_foldr_mem_rigidityRows` /
      `redundancy_panel_carry`) is **the WRONG granularity for the bottom family** (§(o‴), 2026-06-19) →
      **bottom-family whole-relabel transport [next — GATED on the §(o‴) OPEN FACT recon]** (KT (6.62):
      transport the shared `w` by ONE `funLeft (shiftPerm i)`, `hwmem` off the graph-iso genuine arm +
      the single `±r` block at `vᵢ` via G4d-i — the cycle generalization of d=3 M₃
      `case_III_bottom_relabel`, NOT a `bottomTag_foldr`) → **2c-ii-arm** `chainData_relabel_arm`
      (closer; d=3 M₃ = `i=2` instance) → **2c-iii** `chainData_dispatch`. Live status: *Current state*
      tracker; full detail: design §(o‴) (the live verdict; §(o″) preserved as the invalidated record).
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

**Route B LOCKED; no motive/IH/spine-carry change (C.3/C.6 unmoved). Telescoping DESIGN-PASS DONE
(§(o‴), 2026-06-19) — VERDICT FLAG-DON'T-FORCE: the W9b membership is a bottom-family-transport RESHAPE,
NOT a per-body fold, gated on one OPEN structural fact (below).**

**NEXT STEP — a focused recon of the §(o‴) OPEN FACT before any build** (do NOT build the arm until it
closes — it is exactly the "mechanically plausible" shape the 4× mis-pins were). The §(o‴) design-pass
(design `notes/Phase23-design.md` §(o‴), source-verified KT pp.696–698 + landed bodies + 2
machine-verified single-steps) ruled out every per-body fold-invariant (pinned-`Tag` residual /
pure-span block-disjunct miss / accumulating-sum no-telescope) and pinned the honest GLOBAL transport:
KT (6.62)'s **whole-relabel row correspondence** — transport the shared `w` by ONE
`funLeft (shiftPerm i)`, reading `hwmem` off the graph-iso `splitOff_isLink_shiftRelabel_iff` (genuine
arm) + the single `±r` block at `vᵢ` via G4d-i (one (6.44)) — the cycle generalization of the d=3 M₃
`case_III_bottom_relabel` genuine-row arm, NOT a `bottomTag_foldr`.

**RE-ROUTE CONFIRMED** by an adversarial second read (read-only recon, opus, §(o‴)(F)): all three
attacks failed (block-disjunct not a span member, rank-provable; KT verbatim = a family of single-body
facts, no per-body chain; abandoned machinery has zero live consumers). The OPEN FACT was sharpened:

**THE OPEN FACT to recon (§(o‴)(E)/(F)):** does the genuine `M₀`-row → genuine candidate-`i`-row
correspondence close against the whole `shiftPerm i` + seed `qᵢ = q₁∘ρᵢ` (6.56), via the landed graph
iso + `hingeRow_funLeft_dualMap`? It is the d=3 M₃ `case_III_bottom_relabel` genuine-row arm
(`Relabel.lean:1109–1144`, single-swap via `hrecGv`/`hends₃_off`/off-`{e_a,e_b,e_c}` extensor
coincidence) generalized to the whole cycle + seed change. **Load-bearing new obligation (2nd read):**
the **`shiftPerm`-fixed-point / seed-extensor-coincidence identity for non-chain edges** — `shiftPerm i`
fixes every non-chain edge's endpoints so `qᵢ = q₁∘ρᵢ` reproduces `q₁`'s extensors there (KT
(6.55)/(6.56)); the T-W9a chain keeps `ends`/`q` FIXED (`_htrans` by `le_refl`) so does NOT supply it —
the genuinely-new piece, write it before any build. IF it closes:
the single leaf is `chainData_relabel_arm` with `hwmem` filled by a NEW whole-cycle transport
`chainData_relabel_hwmem` (no `bottomTag` infra). IF NOT: the obstruction is at the bottom-family
PRODUCTION level (how `w`'s block disjunct is generated) — a `ChainData`/W6b-producer question for the
coordinator, NOT a CHAIN-2c-ii leaf.

**Confirm-and-delete at the reshape** (orphans, zero live callers): (1) the per-body W9b chain —
`bottomTag_foldr_mem_rigidityRows` + §(o″) single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` +
bridge `redundancy_panel_carry` (wrong granularity, replaced by the whole-relabel transport);
`candidateRow_ac_eq_neg` likely **re-consumed** by the new block arm (G4d-i/eq.6.44) — re-check at the
arm build, don't blind-delete (§(o‴)(F)). (2) `ofNormals_relabel_perm` (2c-ii-β, REJECTED route A). (3)
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` (binary composition, superseded by `wstep`).
**STAYS (NOT orphaned):** the T-W9a span fold `shiftBodyList_foldr_mem_span_rigidityRows` (transports the
candidate row `hρGv` — machine-verified DONE), the graph iso `splitOff_isLink_shiftRelabel_iff` (the
whole-relabel genuine arm, consumed at the arm `chainData_relabel_arm`), G4d-i
`acolumn_mem_hingeRowBlock_of_span_rigidityRows` (the `±r` block arm), the W6b `ρ ⊥ C(q(ab))` gate.
**`d=3` zero-regression CONFIRMED:** `shiftPerm 2 = (v₁v₂)` single swap = landed `case_III_bottom_relabel`;
reshape fires only `i≥3`; d=3 M₃ / `case_III_arm_realization_M3` / dispatch untouched. **Per-leaf
tracker** (checklist CHAIN-2): T-W9a ✓ (stays) → per-body W9b chain ✗ (wrong granularity) →
**bottom-family whole-relabel transport [next — gated on §(o‴) OPEN FACT recon]** → 2c-ii-arm → 2c-iii
→ CHAIN-5.

- **CHAIN-2c — the single-base `Fin (k+1)` family dispatch (design §(n)/§(o)/§(o′)).** Route β LOCKED
  (user-adjudicated 2026-06-18, KT-source-verified): ONE base `(G₁,q₁)` (the `v₁`-split = `M₀`), ONE
  `ρ₀`, ONE W6b call, ONE discriminator call, then `fin_cases u`; eq. (6.66)'s ±r chain absorbed into
  reusing one `ρ₀`. The relabel arm (2c-ii) covers the interior candidates `2 ≤ i ≤ d−1` (a
  genuinely-new construction, NOT a numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle, the d=3 engines are
  transposition-only); **M₀-arm reuse SETTLED:** 2a-ii (`chainData_split_realization`) is the `i=1`/`M₀`
  arm (its per-`i` split at `i=1` IS the `v₁`-split), the uniform arm does not subsume it (they are the
  `fin_cases`'s direct / relabel legs). The 2c-ii leaf decomposition + the §(o′)(B) fork (**adjudicated
  → route B**) live in **checklist CHAIN-2** (the single tracker) + design §(o″). No motive/IH or
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
  `fin_cases u`; reuse 2a-ii only at `M₀`. Route β LOCKED (user-adjudicated, row 242). Detail
  `notes/Phase23-design.md` §(n).
- **CHAIN-2c-ii design-pass (§(o)/§(o′)/§(o″)) — route B (shared-`ρ₀` row-span); route A REJECTED**
  (its eq.-6.66 identity equates two `Classical.choice` existentials). Superseded on the W9b-transport
  granularity by §(o‴) (the whole-relabel verdict, entry below). Detail §"CHAIN"(o)/(o′)/(o″).
- **TELESCOPING DESIGN-PASS 2026-06-19 (§(o‴), docs-only, supersedes the iter-3/7/9/11 per-body pins
  incl. §(o″)) — VERDICT: FLAG-DON'T-FORCE STOP. The W9b membership is a bottom-family-transport reshape,
  NOT a per-body fold.** Machine-verified (2 single-step compiles): the §(o″) pinned-`Tag` leaves the
  residual `hingeRow v b ρ ≠ hingeRow c v ρ`; a pure-span `Tag` carries the genuine-row arm (= landed
  T-W9a) but misses the `(ab)`-block (∉ `span (G−vᵢ)`, rank-provable `Candidate.lean:339–355`); an
  accumulating sum doesn't telescope. Root cause: KT (6.62)/(6.52)/(6.66) carries the redundancy GLOBALLY
  (whole relabel `ρᵢ`, zero on `V∖{vᵢ}` + one (6.44) at `vᵢ`) — the per-body `shiftBodyList` fold is right
  for the *relabel* (T-W9a stays) but wrong for the *bottom family*. Honest transport = whole-relabel
  graph-iso (cycle gen of d=3 M₃ `case_III_bottom_relabel`), GATED on one OPEN FACT (§(o‴)(E)). No
  motive/IH/spine change. **2nd read §(o‴)(F): RE-ROUTE CONFIRMED** (adversarial recon, all 3 attacks
  failed; OPEN FACT sharpened to the `shiftPerm`-fixed-point seed-coincidence identity). The per-body W9b
  chain joins the confirm-and-delete orphans. Detail §(o‴).
**Landed CHAIN-2 leaves (all axiom-clean; detail = git + design §(o)/(o′)/(o″) + FRICTION).** One-line
verdicts (settled; nothing downstream leans on the internals): **`G.ChainData n` record + accessors**
(`Induction/Operations.lean`, the contract-C.1 length-`d` chain + the interior-split `(v,a,b,e_a,e_b)`
geometry accessors; `Fin d`-index idiom in FRICTION). **CHAIN-2c-i** `exists_chainData_discriminator_pick`
(`Realization.lean`, the route-β single-discriminator pick, verbatim generalization of the d=3
region). **2c-ii-α** `ChainData.shiftPerm` (KT eq. 6.54) + recursion handle
`shiftCycle_eq_cons`/`shiftPerm_eq_swap_mul`. **2c-ii-graphiso** `splitOff_isLink_shiftRelabel_iff` +
`shiftEdgePerm` (the `hiso` supplier, consumed at the **arm**). **2c-ii-transport-W9a** (route B, the
genuinely-new crux — STAYS, transports the candidate row `hρGv`) `shiftBodyList_foldr_mem_span_rigidityRows`
(fold core + `shiftBodyFramework`/`_htrans` removeVertex chain; span-only, endpoints removeVertex NOT
splits). **⚠ Orphans (confirm-and-delete at the arm build — wrong-granularity per §(o‴); *Hand-off* flag):
the per-body W9b chain** `funLeft_dualMap_bottomTag_mem_rigidityRows` + `bottomTag_foldr_mem_rigidityRows`
+ `redundancy_panel_carry` (+ the route-A `ofNormals_relabel_perm`) — the §(o‴) whole-relabel transport
replaces them. **OD-7 `hcontract_k`** = 5 leaves (mostly numeral passes; the
one genuinely-new piece LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple`).

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
