# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2** (the `Fin d` reduction layer) — corrected Fix A SETTLED (§(o‴)(H)). The
**genuine-row `hwmem` leaf `chainData_bottom_relabel` is now LANDED** (`Relabel.lean`, axiom-clean,
2026-06-20): the per-member `(shiftPerm i.castSucc)⁻¹` cycle transport of the `v₁`-base `removeVertex`
bottom-row disjunction to the candidate-`i` arm disjunction, dispatching the base genuine/block split
through the make-or-break `removeVertex_genuine_shiftRelabel` + the genuine-row branches
(`rigidityRow_relabel_to_genuine`) + an inline `±r` wrap-block + `blockRow_relabel_perm` (base block →
genuine `edge 0` row). Two new recording hyps the arm supplies: `hrec` (`removeVertex (vtx 1)` link
recording) + `he₀rec` (`ends₀ e₀ = (vtx 2, vtx 0)`).
The **`hρGv` G1 bridges are now LANDED** (`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` /
`wstep_foldl_funLeft_eq`, both axiom-clean, 2026-06-20): the perm-level + linear-map-level halves
bridging the landed W9a `foldl` fold (`shiftBodyListAsc_foldl_mem_span_rigidityRows`) to the engine's
`qρ`/`shiftPerm` form — the `foldl` order lands on the *inverse* product `(funLeft (shiftPerm
i.castSucc)⁻¹)`, exactly the base→candidate inverse-cycle relabel the arm wants.
**`hρGv` DESIGN-PASS DONE + KT-FAITHFULNESS RECON DONE + ROUTE LOCKED 2026-06-20** (design §(o‴)(I.7)/
(I.7.7)): the bare-row extraction decomposes into **3 leaves** (LEAF-ρ1 / ρ2 literal-row id / ρ3 assembly);
span level confirmed matching. An adversarial KT recon (owner-prompted) **REFUTED the clean-relabel
collapse and CONFIRMED the W9a fold is KT-faithful** (KT 6.63–6.66 = the degree-2 `a`-column cancellation =
the `wstep` residue). Two pin corrections locked (§(o‴)(I.7.7)): I.7.4(a)'s "residue at surviving edge" is
WRONG (residue link `v–c` is a non-edge), and the correct LEAF-ρ1 = the **d=3 M₃ template**
(`Relabel.lean:2437–2506`) generalized to `i−1` steps (W9a fold + genuine-row id + `sub_mem`). **NEXT =
LEAF-ρ1** (the `i−1`-step M₃ generalization, `i=3` 2-residue de-risk FOR REAL first), then the **arm wiring**
`chainData_relabel_arm`: instantiate `case_III_arm_realization` at the per-`i` roles (`hwmem` → landed
`chainData_bottom_relabel`, block → `blockRow_relabel_perm`, `hρGv` → LEAF-ρ3 over the landed W9a fold +
G1 bridges) → **2c-iii** `chainData_dispatch` (closes 23b green-modulo `hdispatch`). detail = *Current
state* + *Hand-off*.
**Settled context (full detail in Tracker + Hand-off):** the arm engine binds `hwmem`/`hρGv` at
**removeVertex** level (`ofNormals Gv ends q`, `Gv ≤ G`), so the split-level rows-288/291 bricks
`rigidityRow_chainData_relabel` / `rigidityRow_relabel_perm` are **orphaned-for-the-arm** (the resolved
"NOT pure instantiation" mis-pin — recon-1 + a build BLOCKED, 2026-06-19); the W9b per-body chain DELETED
(§(o‴)(I.1), dead infra).
+ CHAIN-5 (the dispatch assembly, gated by the ENTRY-contract reshape — **moved to 23c**).**
The integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain. **23b CLOSE BOUNDARY (2026-06-19):
close 23b when `chainData_dispatch` (2c-iii) lands — CHAIN-5 → front of 23c=ENTRY, 23b closes green-modulo
`hdispatch`. ⚠ This boundary's TIMELINE is now contingent on the genuine-row `hwmem` crux being tractable
(the de-risk recon settles it); the *shape* of the boundary stands.** (codes-until-open).

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

**Tracker (CHAIN-2c-ii-transport) — the `hwmem` slot is now CLOSED; `hρGv` remains.** The arm engine
`case_III_arm_realization` (`Arms.lean:72`) binds BOTH `hwmem` (`:96`) and `hρGv` (`:91`) at the
**removeVertex-level** `ofNormals Gv ends q` (`Gv ≤ G`, `v ∉ V(Gv)`; `splitOff ⋬ G` so `Gv` can't be a
split). The d=3 wiring (`case_III_arm_realization_M3:1957/2065`) instantiates `Gv := G.removeVertex a` and
transports `(G−v) → (G−a)` via the bespoke `case_III_bottom_relabel`, **not** a graph-iso. Slot status:
- **Genuine-row `hwmem` leaf `chainData_bottom_relabel` — LANDED 2026-06-20** (`Relabel.lean`,
  axiom-clean): the per-member `(shiftPerm i.castSucc)⁻¹` cycle transport (the general-`d` analogue of
  d=3 `case_III_bottom_relabel`). Dispatch: genuine base row → `removeVertex_genuine_shiftRelabel` then
  `rigidityRow_relabel_to_genuine` (genuine image) or an **inline `±r` block** (wrap edge → candidate
  fresh pair, sign by recorded orientation via one hoisted `hperp`); base `(vtx 2,vtx 0)`-block tag →
  `blockRow_relabel_perm` at `e_t = edge 0` (link `vtx 1—vtx 0`, surviving). The two pre-built block
  bricks (`rigidityRow_relabel_to_block{,_swap}`) were too rigid for the wrap case (literal `hsupp`
  can't absorb the orientation sign, independent of endpoint order) → inlined; they stay
  orphaned-for-the-arm. Two arm-supplied recording hyps: `hrec` + `he₀rec`.
- **`hρGv` (candidate-row, W9a span fold) — G1 BRIDGES LANDED 2026-06-20; DESIGN-PASS DONE 2026-06-20**
  (design §(o‴)(I.7)). The G1 bridges `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (`Operations.lean`)
  + `wstep_foldl_funLeft_eq` (`Relabel.lean`, the relabel-only `foldl` = `funLeft ⇑(∏ swap)⁻¹`, the
  `foldl`-order inverse = the base→candidate relabel) are LANDED. The bare-row extraction is now
  decomposed into **3 leaves** (LEAF-ρ1/ρ2/ρ3, §(o‴)(I.7.3)): the crux is that the W9a `_foldl` output is
  `(relabel-only foldl) φ − Σ(i−1 residues)` but `hρGv` wants the literal `(relabel-only foldl) φ`, so the
  extraction adds the `i−1` a-column residues back (the `i−1`-residue generalization of the d=3 M₃ single
  `sub_mem`). **Span level CONFIRMED matching** (both fold endpoints = removeVertex frameworks at
  `G − v₁`/`G − vᵢ` = the engine's `Gv`; no mismatch leaf). One open decision pinned (residue-lands-in-top
  -span, §(I.7.4); de-risk `i=3` first). **← NEXT: LEAF-ρ1 (the residue telescope, P≈3), then the arm
  wiring `chainData_relabel_arm`.**
- **Orphaned-for-the-arm (split-level / now-unused, delete at the arm-build commit):**
  `rigidityRow_chainData_relabel` / `rigidityRow_relabel_perm` (rows 288/291); the candidate→base
  T-W9a fold; **and now the two pre-built block bricks `rigidityRow_relabel_to_block{,_swap}`** (the
  assembly inlined the wrap-block construction instead).
d=3 M₃ `i=2` cycle is the single-swap involution (zero-regression).

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
abstract `foldl` core `bottomTag_foldl_mem_rigidityRows`) DELETED 2026-06-19** —
§(o‴)(I.1) refuted the per-body block transport it encoded; **confirm-and-delete done** (zero callers),
never prerequisites (Q1). Remaining in **CHAIN-2c-ii** (§(o‴)(I)/(I.5)): CHAIN-2c-ii-inv (the inverse-cycle
action lemmas) is already LANDED (`Operations.lean:1550–2110`), and the genuine-row `hwmem` leaf
`chainData_bottom_relabel` is now **LANDED 2026-06-20** (`Relabel.lean`, axiom-clean — the per-member
`(shiftPerm i.castSucc)⁻¹` cycle transport; *Current state* Tracker + *Hand-off* + §(o‴)(I.6)), and the
**`hρGv` G1 bridges** `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` / `wstep_foldl_funLeft_eq` are now
**LANDED 2026-06-20** (both axiom-clean — the W9a `foldl` fold's `qρ`/`shiftPerm`-form bridge; the
`foldl` order lands on the *inverse* product, exactly `(funLeft (shiftPerm i.castSucc)⁻¹)`). So → the
**arm wiring** `chainData_relabel_arm` + **CHAIN-2c-iii** (the assembly `chainData_dispatch`), then
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
        touch**) — revert the lifted infra to `Fin 4`. (2) **DONE 2026-06-20** — the `finrank {n}^⊥ = k`
        metric transport (duplicated between (h-3)/(h-4)) is factored into the shared
        `finrank_toDualPerp_pair_eq` helper (`MeetHodge.lean`, axiom-clean; the byte-identical ~55-line
        `Q`/`W` blocks now both call it).
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
      **LANDED 2026-06-19** (the W9b per-body chain — single-step + `foldl` core
      `bottomTag_foldl_mem_rigidityRows` — was landed then **DELETED 2026-06-19**, §(o‴)(I.1) dead infra).
      The flagged genuine-arm bookkeeping's **seed half** LANDED 2026-06-19 (`seedShift_inv_cancel` +
      `seedShift_off_cycle`, `Operations.lean`, axiom-clean). The genuine-row `hwmem` transport is a
      removeVertex-level **per-row case-split** (NOT the split→split graph-iso — `rigidityRow_relabel_perm` /
      `rigidityRow_chainData_relabel`, rows 288/291, are orphaned-for-the-arm). Its **all 3 abstract branches
      LANDED** (`rigidityRow_relabel_{off_cycle,to_block,to_genuine}`, `Relabel.lean`, axiom-clean — off-cycle,
      wrap-edge→block, interior-chain-edge; the interior brick is the general moving form, off-cycle delegates
      to it) + **both block-orientation siblings** (`rigidityRow_relabel_to_block` `(a,b)`-order `ρ':=r` +
      `rigidityRow_relabel_to_block_swap` `(b,a)`-order `ρ':=-r`, LANDED 2026-06-20). The **block disjunct**
      `blockRow_relabel_perm` (Leaf B) is also slotted. The **genuine-link transport crux**
      `removeVertex_genuine_shiftRelabel` (the make-or-break) **LANDED 2026-06-20**, and the **per-member
      assembly `chainData_bottom_relabel`** (the genuine-row `hwmem` leaf) is now **LANDED 2026-06-20**
      (`Relabel.lean`, axiom-clean — the `(shiftPerm i.castSucc)⁻¹` dispatch of the base disjunction
      through the crux + `rigidityRow_relabel_to_genuine` + an inline `±r` wrap-block + `blockRow_relabel_perm`).
      The **`hρGv` G1 bridges** `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` /
      `wstep_foldl_funLeft_eq` are now **LANDED 2026-06-20** (axiom-clean; the W9a `foldl` fold's
      `qρ`/`shiftPerm`-form bridge, `foldl`-order → inverse product → `(funLeft (shiftPerm
      i.castSucc)⁻¹)`). → **NEXT: the arm wiring `chainData_relabel_arm`** → **2c-iii**
      `chainData_dispatch`. d=3 M₃ = `i=2` involution (zero-regression). Full detail: *Current state*
      Tracker + *Hand-off* + design §(o‴)(I.6).
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`). **→ MOVED TO 23c**
      (boundary LOCKED 2026-06-19; gated on ENTRY's extractor reshape, so it lands at the front of
      23c=ENTRY alongside the extractor that feeds it — 23b closes green-modulo `hdispatch`).
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

- **OD-8 — RESOLVED 2026-06-17** (route α, `complementIso` = the O(n)-natural Hodge `⋆`; β rejected — the
  withdrawn `dim Φ̃` count). §"CHAIN"(h).
- **OD-6 — DECIDED:** five leaves within ONE sub-phase 23b (the arm engine is already general-`k`).
- **OD-7 — DECIDED + CLOSED:** the four 23a producers folded into CHAIN's tail (after CHAIN-3); all general-`k`.
- **OD-4 — RESOLVED 2026-06-18:** existence/homogeneous route, alg-independence NOT forced — the eq.-(6.67)
  D-span runs off `span_omitTwoExtensor_eq_top` (linear independence of `d+1` homogeneous vectors, via Lemma
  2.1, not KT's affine points). §(i).
- **(b) producer-shape — SETTLED 2026-06-17:** the `G.ChainData n` interface frozen, no motive/IH change
  (C.6), `d=3` zero-regression wrapper (C.4: chain `v₀v₁v₂v₃ = b—v—a—c`). §"CHAIN↔ENTRY contract".
- **OD-1 (still open — ENTRY's to resolve at build, C.5).** KT Lemma 5.4 short-cycle base is a real branch
  of the general-`d` chain entry (unlike `d=3`'s inline triangle floor); whether the dispatch assumes the
  chain branch (ENTRY discharging the cycle branch) is invariant for CHAIN-5's signature.

## Hand-off / next phase

**FIX-FORK SETTLED (§(o‴)(H), 2026-06-19): corrected Fix A.** No motive/IH/spine-carry change (C.3/C.6);
route β preserved; `d=3` zero-regression preserved. The full verdict (KT deciding lines, leaf signatures,
tear-up/keep lists) is `notes/Phase23-design.md` §(o‴)(H); the rationale is *Current state* above.

**2c-ii-arm is a removeVertex-level transport (settled 2026-06-19; not pure instantiation).** The arm
engine binds `hwmem`/`hρGv` at **removeVertex** level (`ofNormals Gv ends q`, `Gv ≤ G`), so the
genuine-row `hwmem` disjunct is a *literal per-member removeVertex* cycle transport generalizing
`case_III_bottom_relabel:1499–1595` from a single swap to `(shiftPerm i)⁻¹` — a **per-row case analysis**
(NOT a graph-iso: the split iso mixes fresh `e₀` with genuine edges; NOT the W9a span fold: `hwmem` needs
*literal* rows). De-risk CONFIRMED tractable (§(o‴)(I.6)): `deg_two` (interior chain vertices are degree-2
in `G`, `Operations.lean:1303`) rules out homeless interior blocks; cycle chain-edge rows → genuine
chain-edge rows (KT 6.62), the wrap `edge i` → the candidate `(a,b)` block, off-cycle rows → genuine via
`seedShift`. Orphaned-for-the-arm (wrong graph level, confirm-and-delete at the arm build):
`rigidityRow_chainData_relabel` / `rigidityRow_relabel_perm` (rows 288/291, split→split). `hρGv`'s G1
bridges `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` / `wstep_foldl_funLeft_eq` are now **LANDED**
(see *Current state* Tracker), so the candidate-row span transport is bridgeable at the arm.

**Genuine-row `hwmem` leaf `chainData_bottom_relabel` — all 3 abstract branches LANDED**
(`rigidityRow_relabel_off_cycle` + `rigidityRow_relabel_to_block` + `rigidityRow_relabel_to_genuine`,
`Relabel.lean`, all axiom-clean; per-branch construction in *Decisions made* → "Genuine-row hwmem transport
bricks" + the Lean docstrings): *off-cycle* (both endpoints fixed → genuine target row), *wrap-edge→block*
(top edge `edge i` → candidate `(a,b)` BLOCK disjunct), and the new *interior-chain-edge*
`rigidityRow_relabel_to_genuine` (`edge s ↦ edge (s−1)`, both endpoints move one step but survive
`removeVertex vᵢ` → genuine `(G−vᵢ)` row at the shifted link). The interior brick is the general moving
form; the off-cycle sibling delegates to it (`(u',w',f')=(u,w,f)`).
**`hsupp_of` FOUNDATION LANDED 2026-06-20** (`ofNormals_supportExtensor_relabel_perm`, `Relabel.lean`,
axiom-clean): the abstract support-extensor coincidence under any relabel `(ρ, σ)` —
`(ofNormals Gt endsσρ qρ).supportExtensor f = (ofNormals Gt ends₀ q₀).supportExtensor (σ f)` — extracted
from `ofNormals_relabel_perm`'s local `h_supp` step (which now delegates to it, no duplication). This is
the `hsupp` ingredient the genuine-row bricks (`rigidityRow_relabel_{off_cycle,to_genuine}`) consume;
instantiated at `(shiftPerm i.castSucc, shiftEdgePerm i)` it supplies their per-branch support-extensor
coincidence at the candidate-`i` split.

**Genuine-row `hwmem` leaf `chainData_bottom_relabel` — LANDED 2026-06-20** (`Relabel.lean`,
axiom-clean): the per-member `(shiftPerm i.castSucc)⁻¹` cycle transport of the `v₁`-base
`removeVertex (vtx 1)` bottom-row disjunction to the candidate-`i` arm disjunction (general-`d` analogue
of d=3 `case_III_bottom_relabel`). Dispatch: a genuine base row `hingeRow x y r` → the make-or-break
`removeVertex_genuine_shiftRelabel` classifies the relabelled link, then `rigidityRow_relabel_to_genuine`
(genuine image) or an **inline `±r` wrap-block** (candidate fresh pair, sign from the recorded `ends₀ f`
orientation via one hoisted `hperp : r (C(q x)(q y)) = 0`); a base `(vtx 2,vtx 0)`-block tag →
`blockRow_relabel_perm` at `e_t = edge 0` (link `vtx 1—vtx 0`, surviving). Two arm-supplied recording
hyps: `hrec` (`removeVertex (vtx 1)` link recording) + `he₀rec` (`ends₀ e₀ = (vtx 2, vtx 0)`). Two
lessons (→ TACTICS-QUIRKS §38, *Decisions made*): (1) pin the relabel bricks' implicit seed `qρ`/panel
endpoints `a,b` explicitly to avoid a higher-order-unification `whnf` blowup; (2) the pre-built block
bricks `rigidityRow_relabel_to_block{,_swap}` were too rigid (literal `hsupp` can't absorb the
orientation sign, which is independent of the endpoint-classification order) → inlined the wrap-block,
leaving those two bricks orphaned-for-the-arm.

**`hρGv` G1 bridges — LANDED 2026-06-20** (`shiftPerm_eq_prod_map_swap_shiftBodyListAsc`,
`wstep_foldl_funLeft_eq`, both axiom-clean): together they bridge the landed base→candidate W9a `foldl`
fold (`shiftBodyListAsc_foldl_mem_span_rigidityRows`) to the engine's `qρ`/`shiftPerm` form. The perm
bridge identifies `shiftPerm i.castSucc` with the (forward) swap product over `shiftBodyListAsc i`
(`Equiv.swap_comm` reduction to the landed descending bridge); the linear-map bridge identifies the
relabel-only `foldl` of `(funLeft swap).dualMap` with `funLeft ⇑(∏ swap)⁻¹` — the `foldl` order
reverses the product to the **inverse**, which composed with the perm bridge is *precisely* `(funLeft
(shiftPerm i.castSucc)⁻¹).dualMap`, the base→candidate inverse-cycle relabel the arm wants (the same
`.symm`/`⁻¹` form the `hwmem` leaf `chainData_bottom_relabel` already uses).

**NEXT STEP — build `hρGv` LEAF-ρ1 via the d=3 M₃ template, then LEAF-ρ2/ρ3, then the arm wiring
`chainData_relabel_arm`.** **KT-FAITHFULNESS RECON DONE + ROUTE LOCKED (§(o‴)(I.7.7), 2026-06-20):** an
adversarial read-only recon (prompted by the owner's "are we grounding on KT?") REFUTED the
clean-relabel-collapse hypothesis and CONFIRMED the W9a residue machinery is **KT-faithful** — KT's
redundancy transport (6.63–6.66) is the degree-2 `a`-column cancellation (eq 6.44, iterated `i−1` to `±r`),
which IS the `wstep` residue. The **fold route stands** (not a wrong turn); the clean relabel is closed
(`T` is not span-to-span: the moving-body `e_c=ac` row strips to a non-edge `v–c` row only the `a`-column
cancels). **Two prior-pin corrections locked by the recon:** (1) §(o‴)(I.7.4)(a) is **SUPERSEDED** — the
residue link is `v–c = vtx(s+1)–vtx(s+3)` (a NON-edge), NOT the surviving `a–c = edge(s+2)`; the residue is
NOT a standalone span member; (2) the row-306 build's "LEAF-ρ1 is false" was flawed reasoning (the
difference can be a span member while neither term is). **The correct LEAF-ρ1 structure = the d=3 M₃
template** (`case_III_arm_realization_M3`, `Relabel.lean:2437–2506`) generalized to `i−1` steps: feed the
base redundancy through the W9a fold, identify the genuine relabel-image `e_b`-row (via `hρe₀`), then
`sub_mem` + `sub_sub_cancel` extracts the engine's `hρGv` slot (= the residue). **Span level matches**
(§(o‴)(I.7.0)): both fold endpoints are removeVertex frameworks at `G − v₁` / `G − vᵢ` = the engine's `Gv`.
The leaves:
- **LEAF-ρ1** (P≈3, the genuinely-new piece) — the `i−1`-step generalization of the d=3 M₃ `case hρGv`
  extraction (W9a fold + genuine-row identification + `sub_mem`). **Do the `i=3` 2-residue de-risk FOR REAL
  first** (§(o‴)(I.7.6); the row-306 build bailed into the now-closed clean-relabel tangent before
  finishing it) — confirm the residues resolve via the `a`-column / G4d-i
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows`, NOT via "surviving edge."
- **LEAF-ρ2** the literal-row identification (P≈2, the landed G1 bridges + `shiftPerm_inv_*`; this is the
  genuine relabel-image row — correct + load-bearing, but does NOT discharge the slot alone).
- **LEAF-ρ3** the `hρGv` assembly inline in the arm (P≈2, the `sub_mem` combine).
NOT a motive/IH/contract change. Then the **arm wiring `chainData_relabel_arm`**:
instantiate `case_III_arm_realization` at the per-`i` roles (cycle generalization of d=3
`case_III_arm_realization_M3`): seed `qρ = q ∘ shiftPerm i.castSucc`, shared `−ρ₀`; `hwmem` → landed
`chainData_bottom_relabel`; `hρGv` → LEAF-ρ3; block → `blockRow_relabel_perm`; `hρe₀`/`htrans` → G4d-i +
2c-i's discriminator (~1 commit of §38 explicit-seed slot bookkeeping). → **2c-iii** `chainData_dispatch`
(replaces `case_III_candidate_dispatch`) → **CHAIN-5** (in 23c). Close-boundary timeline: **~3–4 commits
to the closed arm** then 2c-iii. d=3 M₃ = `i=2` involution (zero-regression). Orphan-for-the-arm at the
arm-build commit (zero callers, confirm-and-delete): `rigidityRow_chainData_relabel` /
`rigidityRow_relabel_perm` (split-level) + the now-unused `rigidityRow_relabel_{off_cycle,to_block,to_block_swap}`
(the assembly inlined / used only `…_to_genuine`); the candidate→base `_foldr` fold (orphaned-for-the-arm,
H.10). **STAYS (the `hρGv` consumers):** the base→candidate `_foldl` fold + both G1 bridges (§(o‴)(I.7.0)).

**Confirm-and-delete / STAYS** (full list §(o‴)(H.5); `git grep` zero callers at the delete commit).
**DELETED 2026-06-19** (Q1): the 5-decl W9b per-body chain. **Orphaned-for-the-arm (delete at the arm
build, sync the docstring refs):** the candidate→base W9a fold `shiftBodyList_foldr_mem_span_rigidityRows`
(wrong orientation, H.10), `funLeft_dualMap_sub_acolumn_comp_…` (binary, superseded), `ofNormals_relabel_perm`
(route A); the per-`i` W6b architecture `chainData_split_realization`/`_w6b_gates` (re-check at 2c-iii).
**STAYS:** the base→candidate W9a single-step + the H.10 gate `seedAdvance_wstep_hstep` + fold + instance,
the graph iso + `shiftEdgePerm`, the inverse-cycle block, the seed lemmas, G4d-i, `candidateRow_ac_eq_neg`
(used ONCE at `vᵢ` via G4d-i, NOT a per-body carry), the W6b gate, 2c-i, `ChainData` + accessors.
**`d=3` zero-regression:** `i=2` cycle `(v₁v₂)` is an involution → Fix A's inversion is a no-op, the arm
reduces to the landed M₃ engine; `case_III_candidate_dispatch` stays green until CHAIN-5/ENTRY wrap it (C.4).

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

The d=3 discriminator re-point at CHAIN-4d's `k:=2` (h-5) is an available-but-**not-forced** simplification
(defer to ASSEMBLY/cleanup; the d=3 body stays green). The CHAIN-3-finish geometry (`⋀^{d−1}W`-is-a-line,
NOT the withdrawn d=3-only `Φ̃`) + the OD-8 route-β rejection live in design §"CHAIN"(f)/(h) + the
BlueprintExposition CHAIN-3 entry.

**CHAIN↔ENTRY contract SETTLED** (`notes/Phase23-design.md` §"CHAIN↔ENTRY contract"): CHAIN-5's
`hdispatch`/`hcand` signature is frozen against the `G.ChainData n` record (C.1/C.3, landed in
`Operations.lean`); CHAIN-5 is unblocked once the rest of CHAIN-2 lands + ENTRY's extractor is reshaped.

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
§"CHAIN"(d)): CHAIN constructs the general-`k` `chainData_dispatch` (against the frozen
`ChainData` contract) and lifts the four producers (OD-7); **CHAIN-5 wires it into the spine to
discharge `hdispatch` in 23c** (gated on ENTRY's extractor), so 23b hands `hdispatch` downstream
green-modulo. **ASSEMBLY** composes
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
- **W9b per-body chain DELETED 2026-06-19 (§(o‴)(I.1) confirm-and-delete, build/lint-verified).** Removed
  the 5-decl dead cluster from `CaseIII/Relabel.lean` (`funLeft_dualMap_bottomTag{,_seedAdvance}_mem_rigidityRows`,
  `bottomTag_{foldr,foldl}_mem_rigidityRows`, `redundancy_panel_carry`): `git grep` zero live callers, and
  §(o‴)(I.1) showed the per-body block transport it encoded cannot terminate at the chain interior — dead
  infra, never a build prerequisite. Full project build green + warning-clean + `lake lint` clean. Kept
  `candidateRow_ac_eq_neg` (Leaf B re-consumes it). The other §(H.5) orphans (`ofNormals_relabel_perm`, the
  binary `…comp…`, the candidate→base T-W9a fold, the per-`i` W6b architecture) stay flagged for the
  arm-build commit (docstring back-references / re-check coupling, §(o‴)(H.5)).
- **2c-ii-arm `hwmem` = a removeVertex-level per-row transport; all 3 genuine-row branches LANDED
  (2026-06-19/20, axiom-clean).** The genuine-row `hwmem` disjunct is the literal per-member
  `(shiftPerm i)⁻¹` cycle transport (a per-row case-split generalizing `case_III_bottom_relabel`, NOT the
  split→split graph-iso — `rigidityRow_{relabel_perm,chainData_relabel}` rows 288/291 are
  orphaned-for-the-arm). Branches (`Relabel.lean`, enumerated in the bricks block below): off-cycle, wrap-
  edge→block, and the genuinely-new interior-chain-edge `rigidityRow_relabel_to_genuine` (the general
  moving form — free `f'`/`u'`/`w'`, strictly subsuming off-cycle, which now delegates to it). No FRICTION
  (clean reuse, shared 5-line proof). NEXT = the assembly `chainData_bottom_relabel` (*Hand-off*).
- **The swapped-orientation block brick `rigidityRow_relabel_to_block_swap` LANDED 2026-06-20
  (axiom-clean).** The `(b,a)`-order sibling of `rigidityRow_relabel_to_block` (`ρ.symm u = b`,
  `ρ.symm w = a`, `ρ':=-r`): `funLeft(ρ.symm).dualMap (hingeRow u w r) = hingeRow b a r = hingeRow a b (-r)`
  via `hingeRow_funLeft_dualMap`+`hu`/`hw`+`hingeRow_swap`, the negated functional annihilating via
  `LinearMap.neg_apply`+`neg_eq_zero`. Models the d=3 ±r block branch (`case_III_bottom_relabel:1790–1821`),
  so the assembly's wrap case dispatches BOTH `ends₀ (edge i)` orientations (the BLOCKED draft's only gap).
  No FRICTION (clean 3-line sibling of the landed brick, first-draft compile).
- **Genuine-link transport crux `removeVertex_genuine_shiftRelabel` LANDED 2026-06-20 (the
  make-or-break, axiom-clean).** The genuine-row `hwmem` disjunct's link layer: a genuine `G`-link
  surviving `removeVertex (vtx 1)` transports under `((shiftPerm i.castSucc)⁻¹, (shiftEdgePerm i)⁻¹)`
  to EITHER a genuine `removeVertex (vtx i.castSucc)` link OR the candidate fresh pair
  `{vtx (i+1), vtx (i−1)}` (some order). Key move: **lift** the base row to a `v₁`-base `splitOff`
  survivor (`f ∈ E(G)`, `e₀ ∉ E(G)`) and reuse the landed split-level intertwiner
  `splitOff_isLink_shiftRelabel_iff` (`.mpr`) + read back the candidate-split link (survivor ⇒
  removeVertex link; fresh ⇒ wrap pair) — so the `deg_two` case analysis is NOT re-run at removeVertex
  level (it already lives inside `splitOff_isLink_shiftRelabel_forward`). No FRICTION (5-line
  lift-and-reuse; `simpa` closes the `σ(σ⁻¹f)=f` apply-inv identity). NEXT = the assembly
  `chainData_bottom_relabel`, which dispatches the base disjunction through this brick (*Hand-off*).
- **Genuine-row `hwmem` leaf `chainData_bottom_relabel` LANDED 2026-06-20 (axiom-clean — the
  per-member cycle transport).** The general-`d` analogue of `case_III_bottom_relabel`: transports the
  `v₁`-base `removeVertex (vtx 1)` bottom-row disjunction to the candidate-`i` arm disjunction under
  `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`. Genuine base row → `removeVertex_genuine_shiftRelabel`,
  then `rigidityRow_relabel_to_genuine` or an inline `±r` wrap-block; base `(vtx 2,vtx 0)`-block →
  `blockRow_relabel_perm` at `edge 0`. Arm-supplied recording hyps `hrec` + `he₀rec`. Two lessons
  (→ TACTICS-QUIRKS §38): pin the relabel bricks' implicit seed `qρ`/endpoints `a,b` explicit (else a
  higher-order-unif `whnf` blowup at the `refine`); and **inline the wrap `±r` block** because the
  pre-built `rigidityRow_relabel_to_block{,_swap}` demand a literal `hsupp` that can't carry the recorded
  orientation sign (independent of endpoint order) — so `…to_block{,_swap}` + `…off_cycle` join the
  orphans, the arm uses only `…to_genuine`. ~1 commit, P≈2.
- **`hρGv` G1 bridges `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` + `wstep_foldl_funLeft_eq` LANDED
  2026-06-20 (both axiom-clean).** The two-level bridge from the landed W9a `foldl` fold to the engine's
  `qρ`/`shiftPerm` form. Perm bridge (`Operations.lean`): `shiftPerm i.castSucc = ∏ swap` over
  `shiftBodyListAsc i` — same swaps as the descending `shiftBodyList i.castSucc` (`Equiv.swap_comm`,
  element-wise), so a 3-line reduction to the landed descending bridge. Linear-map bridge
  (`Relabel.lean`): the relabel-only `foldl` of `(funLeft swap).dualMap` = `funLeft ⇑(∏ swap)⁻¹` — the
  `foldl` applies the last body **outermost**, reversing the product order, so it lands on the **inverse**
  (swaps are involutions: `mul_inv_rev` + `Equiv.swap_inv`, then the same `funLeft_comp`/
  `dualMap_comp_dualMap` cancellation as the `foldr` sibling). The inverse is *desirable*: composed with
  the perm bridge it is exactly `(funLeft (shiftPerm i.castSucc)⁻¹)`, the base→candidate inverse-cycle
  relabel the `hwmem` leaf already uses. `reverseRec` induction (FRICTION [idiom] *A `List.foldl` whose
  induction base case…* / TACTICS-GOLF §20). No build-iteration friction; the `foldl`→inverse recurrence
  is the reusable note (→ FRICTION [idiom] *Composing two `(funLeft σ).dualMap` relabel transports…*).
- **`hρGv` bare-row extraction DESIGN-PASS DONE 2026-06-20 (docs-only, design §(o‴)(I.7)).** Decomposed
  the `hρGv` slot into **3 leaves**, every load-bearing claim source-verified. (1) **Span level confirmed
  matching** (the hand-off's worry (2) resolved favorably): the W9a `_foldl` fold's endpoints are
  removeVertex frameworks at `G − v₁`/`G − vᵢ` (= the engine's `Gv`), seed-advancing — read off
  `shiftBodyFrameworkAsc`'s `def`, not name similarity. (2) **The fold-vs-literal-row gap is real** (the
  hand-off's framing stands): W9a output = `(relabel-only foldl) φ − Σ(i−1 a-column residues)`, but `hρGv`
  wants the literal `(relabel-only foldl) φ` — so add the `i−1` residues back, the `i−1`-residue
  generalization of the d=3 M₃ single `sub_mem` (`Relabel.lean:2481–2506`). Leaves: **LEAF-ρ1** the
  residue-membership invariant (P≈3, genuinely-new `reverseRec` telescope via G4d-i) → **LEAF-ρ2**
  literal-row id (P≈2, landed G1 bridges + `shiftPerm_inv_*`) → **LEAF-ρ3** the assembly (P≈2). One
  clause-(ii) open decision pinned: residue-lands-in-top-span (§(I.7.4)); de-risk `i=3` first (§(I.7.6)).
  No motive/IH/contract change. ~3–4 commits to the closed arm.
- **CHAIN-3 cleanup item (2) DONE 2026-06-20 — `finrank_toDualPerp_pair_eq` factored (`MeetHodge.lean`,
  axiom-clean).** The byte-identical ~55-line `finrank {n 0, n 1}^⊥ = k` metric transport carried by both
  the (h-3) `complementIso_extensor_mem_range_map_subtype` (its `Q`) and the (h-4)
  `extensor_join_proportional_complementIso_meet` (its `W`) is extracted into one shared helper (over the
  bare-carrier `iInf`-of-`toDual.flip`-kernels, the form both `set` their perp to); each consumer now calls
  it in one line, dropping ~110 lines of duplication. One known-idiom recurrence (the bare `⨅` in the
  *return type* needs `(j : Fin 2)` + `: Submodule …` ascription, else `InfSet Type` synth failure) —
  already FRICTION [idiom] *A standalone `⨅ i ∈ s, ker (proj i)` term needs an explicit `Submodule …`…*.
**Landed CHAIN-2 leaves (all axiom-clean; one-line verdicts — settled, nothing downstream leans on the
internals; detail = git + design §(o)/(o′)/(o″)/(o‴) + FRICTION).** `G.ChainData n` record + accessors
(`Operations.lean`, contract-C.1 chain + interior-split geometry); **2c-i** `exists_chainData_discriminator_pick`
(route-β single-discriminator pick); **2c-ii-α** `ChainData.shiftPerm` (KT 6.54) + `shiftCycle_eq_cons`/
`shiftPerm_eq_swap_mul`; **2c-ii-graphiso** `splitOff_isLink_shiftRelabel_iff` + `shiftEdgePerm`; **2c-ii-inv**
the 4 `shiftPerm_inv_*` + 7 `shiftEdgePerm_inv_*` action lemmas; **seed half** `seedShift_inv_cancel` +
`seedShift_off_cycle`; the **W9a fold** (`seedAdvance_wstep_hstep` + `wstep_foldl_mem_span_rigidityRows` +
`shiftBodyListAsc_foldl_mem_span_rigidityRows`) — carries the *candidate row* `hρGv` (a span member);
the **`hρGv` G1 bridges** `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (`Operations.lean`) +
`wstep_foldl_funLeft_eq` (`Relabel.lean`) bridging that fold's relabel to the engine's
`(funLeft (shiftPerm i.castSucc)⁻¹)` form (the `foldl`-order inverse). **OD-7 `hcontract_k`** =
5 leaves (numeral passes + LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple`).

**Genuine-row `hwmem` transport bricks** (the per-member `case_III_bottom_relabel` cycle generalization at
**removeVertex** level — a per-row case-split, NOT a split graph-iso, NOT a W9b fold; §(o‴)(I.5)/(I.6)):
- **`blockRow_relabel_perm`** (Leaf B, the W6b `(ab)`-block-tag→genuine disjunct) +
  **`rigidityRow_relabel_off_cycle`** (genuine off-cycle branch, delegates to `…to_genuine`) +
  **`rigidityRow_relabel_to_block`** (genuine wrap-edge→`(a,b)`-block branch, `(a,b)`-order, `ρ':=r`) +
  **`rigidityRow_relabel_to_block_swap`** (the `(b,a)`-order sibling, `ρ':=-r` via `hingeRow_swap`;
  LANDED 2026-06-20 — together the two block bricks dispatch BOTH `ends₀ (edge i)` orientations) +
  **`rigidityRow_relabel_to_genuine`** (genuine interior-chain-edge moving branch, the general form) +
  **`ofNormals_supportExtensor_relabel_perm`** (the abstract `hsupp_of` foundation, LANDED 2026-06-20:
  `(ofNormals Gt endsσρ qρ).supportExtensor f = (ofNormals Gt ends₀ q₀).supportExtensor (σ f)` for any
  relabel `(ρ, σ)`, extracted from `ofNormals_relabel_perm`'s local `h_supp` — now delegates to it; the
  `hsupp` ingredient the off-cycle / interior genuine-row bricks consume; supportExtensor ignores the
  graph, so the `Gs`/`Gt` slot is defeq-free) +
  **`removeVertex_genuine_shiftRelabel`** (the genuine-link transport crux / make-or-break, LANDED
  2026-06-20: the `hlinkGt` + wrap classification, by lift-to-`splitOff`-survivor + reuse of
  `splitOff_isLink_shiftRelabel_iff` — the `deg_two` make-or-break stays inside that split-level lemma)
  — all LANDED, axiom-clean, correctly slotted (removeVertex /
  arm-level; design §(o‴)(I.6) + Lean docstrings). The per-member assembly `chainData_bottom_relabel`
  remains (*Hand-off* / *Current state*).
- **Orphaned-for-the-arm (confirm-and-delete at the arm build, `git grep` zero callers):** the split→split
  `rigidityRow_relabel_perm` / `rigidityRow_chainData_relabel` (wrong graph level, (I.5)); the candidate→base
  T-W9a fold `shiftBodyList_foldr_…` (wrong orientation, H.10); `ofNormals_relabel_perm` + the binary
  `…comp…` (docstring-referenced — sync on delete); the per-`i`-W6b `chainData_split_realization`/`_w6b_gates`
  (Fix B; re-check at 2c-iii). **The W9b per-body chain DELETED** (§(o‴)(I.1), 5-decl dead cluster, machine-refuted).
  **Keep** `candidateRow_ac_eq_neg` (Leaf B re-consumes it).

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
  the hypothesis only. The `foldl` recurrence (`wstep_foldl_funLeft_eq`): a relabel-only `List.foldl`
  reverses the order, landing on the **inverse** product `funLeft ⇑(∏ swap)⁻¹` (vs the `foldr`
  sibling's forward product) — `mul_inv_rev` + `Equiv.swap_inv` then the same cancellation* → FRICTION
  [idiom] *Composing two `(funLeft σ).dualMap` relabel transports…*.
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
