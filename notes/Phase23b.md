# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2 (the `Fin d` reduction layer — corrected Fix A SETTLED §(o‴)(H); the candidate-row
(`hρGv`) W9a-slot fold COMPLETE (inverse-cycle action block + H.10 de-risk gate + `foldl` fold core + the
concrete `shiftBodyListAsc_foldl_mem_span_rigidityRows`). **BUILD-PATH CONSOLIDATED §(o‴)(I), 2026-06-19:**
the W9b per-body chain (single-step + `foldl` core `bottomTag_foldl_mem_rigidityRows`) is **OFF the critical
path** — a confirm-and-delete orphan, NOT a prerequisite (Q1). The arm's `hwmem` slot is the per-member
`case_III_bottom_relabel` map (NO fold) cycle-generalized to `(shiftPerm i)⁻¹`: genuine-row → graph-iso,
block → a single G4d-i at `vᵢ` (Leaf B, inline; Q2/Q3). NEXT = 2c-ii-arm `chainData_relabel_arm`
(inverse-cycle action lemmas already landed; gated by the flagged genuine-arm seed-coincidence bookkeeping),
then 2c-iii; see *Hand-off*)
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

**FIX-FORK SETTLED + DE-RISKED — corrected Fix A buildable** (§(o‴)(H), adversarially verified (H.10),
confirmed by the landed de-risk gate): keep the shared `ρ₀`, transport memberships **base→candidate**
(relabel `(shiftPerm i)⁻¹`, seed advancing). Fix B (per-`i` re-seed) INFEASIBLE (breaks KT's single-`r`
existence). The landed candidate→base T-W9a/W9b folds are **orphaned-for-the-arm** (`wstep`
non-invertible). Full reasoning + KT deciding lines = design §(o‴)(H)/(H.10).

**Tracker (CHAIN-2c-ii-transport) — re-pinned by the §(o‴)(I) build-path consolidation (2026-06-19).**
The arm's **candidate-row (`hρGv`) W9a slot is COMPLETE** (the `foldl` fold core + the concrete
seed-advancing chain instance `shiftBodyListAsc_foldl_mem_span_rigidityRows`, through the H.10 de-risk
gate / `seedAdvance_wstep_hstep` bundle — it transports the *span* membership of the redundant `±r` row,
§(o‴)(b) bullet 1). **The W9b per-body chain is OFF the critical path (Q1, §(o‴)(I.1)):** the landed W9b
single-steps + the **abstract foldl core** `bottomTag_foldl_mem_rigidityRows` (b6c780f) encode the
per-body block transport that §(o‴)(b)/(c)/(d)/(H) machine-refuted — they are **confirm-and-delete
orphans** (zero live callers; the chain cannot terminate at the interior). The b6c780f foldl core is
DEAD INFRA, not a build prerequisite. **Q2/Q3 SETTLED (§(o‴)(I.2)/(I.3)):** `chainData_relabel_arm`'s
`hwmem` slot is the **per-member `case_III_bottom_relabel` map (NO fold)** cycle-generalized to
`(shiftPerm i)⁻¹` — genuine-row disjunct via the inverse-relabel **graph-iso** correspondence
(`splitOff_isLink_shiftRelabel_iff` + `hingeRow_funLeft_dualMap`, the d=3 M₃ genuine arm
`case_III_bottom_relabel:1499–1595` lifted from one swap to the cycle), block disjunct = a **single
G4d-i at `vᵢ`** (Leaf B, inline, one eq.-(6.44)). **⚠ Tracker correction:** the bottom-family
*genuine-row* disjunct does NOT ride the W9a span fold — that fold carries the *candidate row* `hρGv`
(a span member); the genuine-row disjunct is a *literal-row* membership transported by the graph-iso
(a pure relabel does not preserve genuine-span membership across the cycle, `case_III_bottom_relabel:1672`).
→ **NEXT: 2c-ii-arm** `chainData_relabel_arm` (§(H.6) leaf-1 inverse-cycle action lemmas already LANDED,
`Operations.lean:1550–2110`; the arm = genuine-row graph-iso arm + Leaf-B single G4d-i + the `hρGv`
W9a fold; **gated by the flagged genuine-arm seed-coincidence bookkeeping**; d=3 M₃ = `i=2` involution)
→ 2c-iii → CHAIN-5. (Orphaned-for-the-arm: the candidate→base T-W9a/W9b folds **and** the entire W9b
per-body chain, §(o‴)(H.10)/(I.1).)

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm;
route B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + §(o″).)

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
CHAIN-2a CLOSED; CHAIN-2c-i + 2c-ii-α/β + 2c-ii-graphiso + 2c-ii-inv + the H.10 de-risk gate (now
covering interior AND top steps, single bound `s+2 < d`, factored into the reusable `hstep` bundle
`seedAdvance_wstep_hstep`) + the abstract `foldl` fold core `wstep_foldl_mem_span_rigidityRows` + **the
concrete `ChainData` seed-advancing instance** `shiftBodyListAsc_foldl_mem_span_rigidityRows` (with its
data `shiftBodyListAsc`/`shiftSeedSwap`/`shiftSeedAdv`/`shiftBodyFrameworkAsc`(`Total`)) COMPLETE; **the
W9b per-body chain (the single-step `funLeft_dualMap_bottomTag_seedAdvance_mem_rigidityRows` + the
abstract `foldl` core `bottomTag_foldl_mem_rigidityRows`) LANDED but is OFF the critical path** —
§(o‴)(I.1) refuted the per-body block transport it encodes; **confirm-and-delete orphans**, NOT
prerequisites (Q1). Remaining in **CHAIN-2c-ii** (§(o‴)(I)): CHAIN-2c-ii-inv (the inverse-cycle action
lemmas) is already LANDED (`Operations.lean:1550–2110`), so → **2c-ii-arm** `chainData_relabel_arm` whose
`hwmem` slot is the **per-member `case_III_bottom_relabel` map (NO fold)** cycle-generalized to
`(shiftPerm i)⁻¹` — genuine-row
disjunct via the inverse-relabel **graph-iso** correspondence, **block disjunct = a single G4d-i at `vᵢ`**
(Leaf B, inline, Q2). **⚠ The bottom-family genuine-row disjunct does NOT ride the W9a span fold** — that
fold carries the *candidate row* `hρGv` (a span member); the genuine-row disjunct is a literal-row
membership via the graph-iso (Q3 correction, §(o‴)(I.3)) — then **CHAIN-2c-iii** (assembly), and
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
      (inverse-cycle action lemmas) + the **H.10 de-risk gate** (base→candidate single-step seed-advance,
      now split into the reusable `hstep` bundle `seedAdvance_wstep_hstep` + wrapper) + the abstract W9a
      `foldl` fold core + **the concrete base→candidate W9a cycle fold** `shiftBodyListAsc_foldl_mem_span_rigidityRows`
      + the W9b single-step `funLeft_dualMap_bottomTag_seedAdvance_mem_rigidityRows` + the **abstract W9b
      `foldl` core** `bottomTag_foldl_mem_rigidityRows` **LANDED 2026-06-19** → **NEXT: Leaf B** (block via
      G4d-i at `vᵢ`; the genuine-row arm reuses the landed W9a span fold per §(o‴)(b)) → **2c-ii-arm**
      `chainData_relabel_arm` (d=3 M₃ = `i=2` involution) → **2c-iii** `chainData_dispatch`.
      Full detail: design §(o‴)(H)/(H.10).
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

**BUILD-PATH CONSOLIDATED — §(o‴)(I) (2026-06-19, design-settle pass; the three questions settled vs the
landed bodies).** **Q1 — `bottomTag_foldl_mem_rigidityRows` (b6c780f) is OFF the critical path.** It is
the abstract pure-relabel `reverseRec` foldl core for a per-body block-disjunct chain — but that chain is
the route §(o‴)(b)/(c)/(d)/(H) machine-refuted (the per-step block residual has no home at the interior;
the W9b single-step's block output `hingeRow c v ρ'` cannot terminate without the `e_b`-row that
`removeVertex` cuts). `git grep`: zero live callers (its own def + `notes/` only). **It is a
confirm-and-delete orphan** — DEAD INFRA, not a prerequisite — joining the §(H.5) tear-up list with
`bottomTag_foldr_mem_rigidityRows`, the two W9b single-steps
(`funLeft_dualMap_bottomTag_mem_rigidityRows`, `…_seedAdvance_…`), and `redundancy_panel_carry` (all zero
live callers). Confirm-and-delete at the arm-build commit; **keep** `candidateRow_ac_eq_neg` (Leaf B
re-consumes it). **STILL LANDED + KEPT:** the candidate-row (`hρGv`) W9a slot — the `wstep_foldl` core +
the concrete `shiftBodyListAsc_foldl_mem_span_rigidityRows` (it transports the *span* membership of the
redundant `±r` row), through the de-risk gate / `seedAdvance_wstep_hstep` bundle.

**Q2 — Leaf B = a SINGLE direct G4d-i at `vᵢ`, NOT a `bottomTag_foldl` instantiation (§(o‴)(I.2)).** The
block disjunct is the whole-relabel image of `M₀`'s single redundant row → the `±r` row at `vᵢ` by ONE
eq.-(6.44) at the single degree-2 body `vᵢ` (G4d-i `acolumn_mem_hingeRowBlock_of_span_rigidityRows` +
`candidateRow_ac_eq_neg`). It is **not minted as a standalone fold-bearing decl** — it is the `Or.inr`
arm inside `chainData_relabel_arm`'s `hwmem` proof (the inverse-cycle generalization of the d=3 single-swap
block branch `case_III_bottom_relabel:1596–1611`; the swap acts non-trivially only near `vᵢ`, so it does
NOT chain over the `i−1` cycle bodies). Do **not** build a per-body block carry (the §(o‴)-rejected route,
mis-pinned 4× at iters 3/7/9/11).

**Q3 — the `hwmem` assembly: per-member `case_III_bottom_relabel` map (NO fold), cycle-generalized to
`(shiftPerm i)⁻¹` (§(o‴)(I.3)).** The engine slot (`case_III_arm_realization`, `Arms.lean:96–99`) wants,
per member `j`: `w j ∈ (genuine Gv-rows) ∨ (∃ρ', ρ'⊥C(q a,q b) ∧ w j = hingeRow a b ρ')`. The arm's proof
is `intro j; <transport the disjunction of (hwmem₀ j)>` — the cycle generalization of the d=3 M₃ discharge
(`Relabel.lean:2264–2272`, a per-member map over `w`, no fold). The two disjuncts transport by DIFFERENT
non-fold mechanisms: (a) **genuine-row disjunct** → the inverse-relabel **graph-iso** row correspondence
(`splitOff_isLink_shiftRelabel_iff` + `hingeRow_funLeft_dualMap`, seed cancellation `qρ(ρ⁻¹x)=q x`), the
cycle generalization of `case_III_bottom_relabel:1499–1595`; (b) **block disjunct** → Leaf B's single
G4d-i. **⚠ Correction to the prior Leaf-A framing:** the bottom-family *genuine-row* disjunct does NOT
ride the W9a span fold — that fold carries the *candidate row* `hρGv` (a span member). The genuine-row
disjunct is a *literal-row* membership; a pure relabel sends a genuine-row-at-the-moving-body to a
`(c,v)`-block (`case_III_bottom_relabel:1672`), so it needs the graph-iso, not a span fold. The W9a span
fold and the genuine-row graph-iso are different mechanisms on different objects.

**STILL FLAGGED (un-discharged here, §(o‴)(I.4)/(E)/(F)(D)):** the genuine-row arm's *cycle generalization*
of `case_III_bottom_relabel:1499–1595` over `(shiftPerm i)⁻¹` + seed `qρ` is the genuinely-new piece (the
`shiftPerm`-fixed-point / seed-extensor-coincidence identity for non-chain edges); its difficulty is
unknown until that bookkeeping is written. This pass does NOT build it — honest status is FLAG, not pin.

**NEXT STEP — `chainData_relabel_arm` (§(o‴)(H.6) leaf-2).** The §(H.6) leaf-1 CHAIN-2c-ii-inv inverse-cycle
action lemmas are **already LANDED** (`Operations.lean:1550–2110`, the 4 `shiftPerm_inv_*` + 7
`shiftEdgePerm_inv_*`), so the arm itself is next: instantiate `case_III_arm_realization` at the relabelled
roles, seed `qρ = q∘shiftPerm i`, shared `±ρ₀`; slots = the `hρGv` W9a fold + the per-member `hwmem` map
(genuine-row graph-iso arm + Leaf-B single G4d-i) + G4d-i (`hρe₀`); also needs the `funLeft (shiftPerm i)⁻¹`
relabel bridge. **Gated by writing the flagged genuine-arm seed-coincidence bookkeeping first**; est. ~3–5
commits; d=3 M₃ = `i=2` involution. → **2c-iii** `chainData_dispatch` (`Fin (k+1)`-case, `M₀` = direct arm,
interior = relabel arm; replaces `case_III_candidate_dispatch`) → **CHAIN-5**.

**Confirm-and-delete / STAYS at the reshape** (full list §(o‴)(H.5); `git grep` zero callers at the
delete commit). **Orphaned-for-the-arm (delete):** the candidate→base folds
`shiftBodyList_foldr_mem_span_rigidityRows` (T-W9a) + `bottomTag_foldr_mem_rigidityRows` (wrong
orientation — converse implication); `funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`,
`ofNormals_relabel_perm`; the per-`i` W6b architecture `chainData_split_realization`/`_w6b_gates`
(re-check at 2c-iii — does the dispatch reuse the `v₁`-split W6b or inline it). **STAYS:** the
base→candidate single-steps (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` + the H.10 W9a gate + the
W9b single-step + the framework-form W9b single-step, now live), the W9a fold + concrete instance, the
graph iso + `shiftEdgePerm`, the inverse-cycle action block, G4d-i, the W6b gate, 2c-i, `ChainData` +
accessors. **⚠ `candidateRow_ac_eq_neg`** (eq.-(6.44)): likely used ONCE at `vᵢ` for the block via G4d-i
— NOT a per-body `redundancy_panel_carry` carry (§(o‴)(H); re-check at the block build).
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
- **FIX-FORK SETTLED 2026-06-19 (§(o‴)(H)/(H.10) — adjudication + adversarial verification, both
  docs-only) — VERDICT: corrected Fix A; Fix B INFEASIBLE.** Keep the shared `ρ₀`, invert to `(shiftPerm
  i)⁻¹` (cancels the seed, matches KT (6.62)); Fix B (per-`i` re-seed) breaks KT's single-`r` existence.
  Correction the verification forced: re-author the transport **base→candidate directly** (reuse the
  base→candidate single-step `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, re-fold opposite order,
  seed advancing) — the landed candidate→base T-W9a/W9b folds are orphaned-for-the-arm (`wstep`
  non-invertible). No motive/IH/spine change; route β + d=3 preserved. Detail §(o‴)(H)/(H.10) + git.
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
re-authored arm transport carries (FRICTION, under the `formPerm`-cycle entry). **The W9a-slot
base→candidate fold (COMPLETE)** = the de-risk-gate `hstep` bundle `seedAdvance_wstep_hstep` (six
per-step conjuncts incl. the seed-advancing `htrans`; single bound `s+2 < cd.d` covers interior AND the
candidate top step) + its wrapper `funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`, the
abstract `foldl` core `wstep_foldl_mem_span_rigidityRows` (`reverseRec`), and the concrete instance
`shiftBodyListAsc_foldl_mem_span_rigidityRows` (chain `shiftBodyFrameworkAsc`/`shiftSeedAdv`, ascending
`shiftBodyListAsc i`, one swap per step) — this carries the *candidate row* `hρGv` (a span member), the
arm's only fold consumer. **The W9b per-body chain (LANDED 2026-06-19, now OFF the critical path —
§(o‴)(I.1)):** the single-step `funLeft_dualMap_bottomTag_seedAdvance_mem_rigidityRows` + the abstract
`foldl` core `bottomTag_foldl_mem_rigidityRows` (the `reverseRec` `Tag`-threading analogue of
`bottomTag_foldr…`) encode the per-body block transport §(o‴)(b)/(c)/(d)/(H) machine-refuted; **zero live
callers, confirm-and-delete orphans, NOT prerequisites.** The arm's `hwmem` is the per-member
`case_III_bottom_relabel` map cycle-generalized to `(shiftPerm i)⁻¹` (genuine-row → graph-iso, block →
single G4d-i; §(o‴)(I.2)/(I.3)) — no W9b fold. **⚠ Orphans-for-the-arm (confirm-and-delete at the arm
build per §(o‴)(H.5)/(I.1); `git grep` zero callers): the candidate→base T-W9a fold**
`shiftBodyList_foldr_mem_span_rigidityRows` + its seed-fixed `shiftBodyFramework`/`_htrans` chain (wrong
orientation, H.10); **the entire W9b per-body chain** — `bottomTag_foldr_mem_rigidityRows`,
`bottomTag_foldl_mem_rigidityRows`, the two single-steps (`funLeft_dualMap_bottomTag_mem_rigidityRows`,
`…_seedAdvance_…`), `redundancy_panel_carry` (+ `ofNormals_relabel_perm`,
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`); and the per-`i`-W6b architecture
`chainData_split_realization` + `chainData_split_w6b_gates` (Fix B's mechanism; re-check at 2c-iii). **Keep**
`candidateRow_ac_eq_neg` (Leaf B re-consumes it via G4d-i). **OD-7 `hcontract_k`** = 5 leaves (mostly
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

- *Match the list recursor to which end the fold's base case sits on: a `foldl`/accumulating fold
  anchored at index 0 inducts with `List.reverseRec` (peel the last element, don't generalize the
  chain); a `foldr` anchored at the tail wants `cons` + `generalizing`* → TACTICS-GOLF § 20 / FRICTION
  [idiom] *A `List.foldl` whose induction base case lives at index `0`…*.
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
