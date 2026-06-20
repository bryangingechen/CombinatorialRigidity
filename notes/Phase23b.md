# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CLOSED:** CHAIN-1/3/4 + OD-7 (the four-producer tail, all general-`k`) + CHAIN-2a
+ the CHAIN-2c-ii foundation (graphiso / inverse-cycle / seed lemmas; the base→candidate W9a `foldl`
fold + its G1 bridges + LEAF-ρ2) + the genuine-row `hwmem` leaf `chainData_bottom_relabel`
(`Relabel.lean`, axiom-clean — the per-member `(shiftPerm i.castSucc)⁻¹` cycle transport of the
`v₁`-base bottom-row disjunction to the candidate-`i` arm disjunction). The **`hρGv` route is LOCKED**
(KT-source re-derivation, design §(o‴)(I.7.10), **option (b)**: the engine slot `hingeRow vᵢ₊₁ vᵢ₋₁ ρ`
is KT-faithful, the missing piece is the buildable KT-eq.-(6.66) fresh-edge telescope, **no
engine/motive/IH/signature change**), and its **re-targeted `i=3` de-risk GATE has PASSED**
(`i3_freshEdge_slot_mem_deRisk`, axiom-clean — the telescope's membership algebra converges:
`slot = W φ − (surviving rows)`). **The LEAF-ρ1 ALGEBRAIC CORE is now LANDED 2026-06-20**
(`wstep_foldl_hingeRow_telescope` + the two per-step helpers `wstep_hingeRow_off`/`_frontier`,
`Relabel.lean`, all axiom-clean): the general-`i` closed form of the `wstep` foldl =
`(∑_{s<m} hingeRow wₛ wₛ₊₁ ρ₀) + hingeRow w_m w_{m+2} ρ₀` (the `m=i−1`-step `reverseRec`
generalization of the `i=3` gate). **The `hρGv` ALGEBRAIC CORE is now COMPLETE 2026-06-20** — the
general-`m` membership corollary `wstep_foldl_freshEdge_slot_mem` (`Relabel.lean`, axiom-clean: the
`m=i−1` generalization of `i3_freshEdge_slot_mem_deRisk`) peels the slot row from `W φ ∈ S` minus the
`m` surviving rows over an abstract carrier `S`. **P1 (the BLOCKER unblocker) is now LANDED 2026-06-20**
(`wstep_foldl_{hingeRow_telescope,freshEdge_slot_mem}` restated finite-range, `Relabel.lean`, axiom-clean):
both algebraic-core lemmas now take `Set.InjOn w (Set.Iic (m+2))` instead of the dead
`Function.Injective (w : ℕ → α)` (which is `False` over the arm's `[Finite α]`) — instantiable from
`cd.vtx_inj` via `Set.InjOn.mono`. **The `hρGv` P2 A-2 de-risk CORE is now LANDED 2026-06-20**
(`candidate_perp_two_incident_panels` + the `supportExtensor`-perp form
`candidate_perp_two_incident_supportExtensors`, `Relabel.lean`, both axiom-clean): the interior-vertex
eq.~(6.44) perp carry — the common candidate `r̂ := ∑λab•rab` is ⊥ both incident chain-edge panels (⊥ `C_c`
direct, ⊥ `C_d` via `candidateRow_ac_eq_neg`'s `rAC = −r̂`), self-contained over the explicit eq-(6.52)
witness (the `d=3` `candidateRow_ac_eq_neg` applies VERBATIM at an interior vertex), the direct
`hperp0`/`hperp1`/`hperp` shape, ZERO blast radius. (The earlier *generic-`ρ₀` isolated-implication* pin
`ρ₀_perp_interior_chain_edge` was REFUTED §(o‴)(I.8.3.v-REFUTED) — the `_sup_` crux is vacuous `=⊤` for
independent consecutive panels; the perp lives in the *specific* `r̂`, not arbitrary `ρ₀`; the
`acolumn_..._sup_...` crux STANDS as scaffolding, the isolated-implication signature is withdrawn.)
**ROUTE SETTLED = Route A**
(adversarial pair rows 322/323 + tie-breaker recon row 324; route B/C refuted as the route-(b) circularity,
interior rows GENUINELY INDEPENDENT — §(o‴)(I.8.3.v-SETTLED)): the perp comes from the SPECIFIC redundancy
`r`/`g` carried OUT of the W6b producer. **The A-2 de-risk CORE is now LANDED 2026-06-20**
(`candidate_perp_two_incident_panels` + the `supportExtensor`-perp form
`candidate_perp_two_incident_supportExtensors`, `Relabel.lean`, both axiom-clean): the interior-vertex
eq.~(6.44) `r̂ = −rAC` perp carry (witness-as-hyps, the direct `hperp0`/`hperp1`/`hperp` shape, ZERO blast
radius — the `d=3` `candidateRow_ac_eq_neg` applies verbatim at an interior chain vertex). **A-1 is now
LANDED 2026-06-20** (`Candidate.lean` + `Realization.lean`, axiom-clean): the W6b producer
`exists_candidateRow_bottomRows_of_rigidOn` SUPPLIES the eq-(6.52) `λ`-grouped `(ab)`-edge witness
(`lamAB`/`rab`, `∀ j, rab j ∈ hingeRowBlock e₀`, `ρ = ∑ⱼ lamAB j • rab j` — the in-scope `r`/`lam`
re-threaded via the per-row `Eb = map (hingeRow …).dualMap block` decomposition + `hingeRow` injectivity),
and `chainData_split_w6b_gates` threads it to its output in chain order (the `(b,a)` branch negates
`rab → −rab`, W8 sign-swap). 3 live callers re-plumbed; d=3 zero-regression (full project green + lint).
**A-3 SINGLE-VERTEX COMPOSITION LANDED 2026-06-20** (`freshEdge_surviving_row_mem_of_witness`,
`Relabel.lean`, axiom-clean, ZERO blast radius): the Route-A closure of `freshEdge_surviving_row_mem`'s
abstract `hperp` — at a surviving edge's interior degree-2 chain vertex `vtx (s+1)`, feed the eq.-(6.52)
`λ`-grouped two-edge witness (the A-1 producer's `lamAB`/`rab`/`lamAC`/`rac`/`grest` + perps + col-vanishing)
through A-2 (`candidate_perp_two_incident_supportExtensors`) to discharge `ρ₀ ⊥ Fva.supportExtensor (edge s)`
FOR REAL, then thread to the `link`-half builder. **REMAINING A-3:** the all-`i` lift (propagate the
witness across the chain off the W6b `hρe₀` base — the iterated KT eq.-(6.66) carry; each interior vertex
needs its own col-vanishing witness, which W6b gives only at the base) + the arm `chainData_relabel_arm`;
**P3 (flagged):** the fold seed `shiftSeedAdv q (i−1)` = engine seed `qρ` is unbuilt. d=3 zero-regression stands; then **2c-iii** `chainData_dispatch`;
**CHAIN-5 → moved to 23c** (ENTRY-gated). Full rolling state = *Current state* + *Hand-off* + design
§(o‴)(I.8); the settled route history (the clean-relabel refutation, the FIX-FORK, the engine-slot
adjudication) is in `notes/Phase23-design.md` §(o‴) + git, **not** re-narrated here.

**23b CLOSE BOUNDARY (LOCKED 2026-06-19):** close 23b when `chainData_dispatch` (2c-iii) lands —
CHAIN-5 → front of 23c=ENTRY, 23b closes green-modulo `hdispatch`. The integer Phase 23 stays **in
progress** (ENTRY / ASSEMBLY remain). (Sub-phase codes-until-open: `CARRIER`=23a closed, `CHAIN`=23b,
`ENTRY`/`ASSEMBLY` code-only.)

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
- **`hρGv` (candidate-row) — path RESOLVED 2026-06-20 (§(o‴)(I.7.10), KT-source re-derivation): the
  engine slot is KT-faithful; the missing piece is the buildable KT-eq.-(6.66) fresh-edge telescope —
  RE-TARGETED `i=3` DE-RISK GATE NOW PASSED.** The KT recon refuted "slot wrong": the slot
  `hingeRow vᵢ₊₁ vᵢ₋₁ ρ` IS KT's `Mᵢ` row (forced by `hG_ea/hG_eb`, eqs 6.56/6.64); the fold is faithful
  only up to KT 6.62+6.63, and KT eq. (6.66) (the degree-2 `±r` telescope) is the missing buildable leaf
  — **NO engine/motive/signature change**, ~3–5 commits. The Lean-verified gate `i3_freshEdge_slot_mem_deRisk`
  (`Relabel.lean` tail, axiom-clean) now confirms the telescope **converges at `i=3`**: the slot row
  `hingeRow v₂v₄ ρ₀` is `W φ` (landed `∈ span`) minus the two genuine surviving chain-edge rows
  `hingeRow v₀v₁ ρ₀`/`hingeRow v₁v₂ ρ₀`, via `sub_mem` (NOT via `D φ`, the red herring). The W9a fold
  + G1 bridges + LEAF-ρ2 + `chainData_bottom_relabel` all STAND (consumers of the resolved route). The G1 bridges
  `shiftPerm_eq_prod_map_swap_shiftBodyListAsc` (`Operations.lean`)
  + `wstep_foldl_funLeft_eq` (`Relabel.lean`, the relabel-only `foldl` = `funLeft ⇑(∏ swap)⁻¹`, the
  `foldl`-order inverse = the base→candidate relabel) are LANDED. **LEAF-ρ2 LANDED 2026-06-20**
  (`shiftBodyListAsc_relabel_foldl_hingeRow`, `Relabel.lean`, axiom-clean): the relabel-only ascending
  `foldl` sends `hingeRow x y ρ₀` to the literal candidate row
  `hingeRow ((shiftPerm i.castSucc)⁻¹ x) ((shiftPerm i.castSucc)⁻¹ y) ρ₀` — a 3-rewrite chain over the
  two G1 bridges + `hingeRow_funLeft_dualMap` (the d=3 M₃ step-2/3 generalization; correct + load-bearing,
  does NOT discharge the slot alone). The bare-row extraction is decomposed into **3 leaves**
  (LEAF-ρ1/ρ2/ρ3, §(o‴)(I.7.3)). **LEAF-ρ1 ALGEBRAIC CORE LANDED 2026-06-20**
  (`wstep_foldl_hingeRow_telescope` + helpers `wstep_hingeRow_off`/`wstep_hingeRow_frontier`,
  `Relabel.lean`, all axiom-clean): the general-`i` closed form of the W9a `wstep` foldl over the
  ascending body list, applied to the base redundancy `hingeRow (w 0)(w 2) ρ₀`, is the explicit sum
  `(∑_{s<m} hingeRow (w s)(w (s+1)) ρ₀) + hingeRow (w m)(w (m+2)) ρ₀` (`m = i−1`), proved by a clean
  induction-on-`m` (`ofFn_succ'` peel + the two per-step helpers: surviving rows fixed by `wstep`,
  the frontier row advances) over an injective vertex function `w`. This is the `i−1`-step
  generalization of the `i=3` gate `i3_wstep_foldl_base_redundancy_deRisk` (`m=2` recovers it
  verbatim) and realizes KT eq. (6.66). **Span level CONFIRMED matching** (both fold endpoints =
  removeVertex frameworks at `G − v₁`/`G − vᵢ` = the engine's `Gv`; no mismatch leaf).
  **The `hρGv` algebraic CLOSED FORM is COMPLETE** — the closed-form telescope PLUS its general-`m`
  membership corollary `wstep_foldl_freshEdge_slot_mem` (LANDED 2026-06-20, axiom-clean: the
  `m=i−1`-step generalization of `i3_freshEdge_slot_mem_deRisk`, peeling the slot row from `W φ ∈ S`
  minus the `m` surviving rows over an abstract carrier `S`).
  **← NEXT: `chainData_relabel_arm`, gated on THREE genuinely-new prerequisites (ARM-WIRING DESIGN-PASS
  §(o‴)(I.8), 2026-06-20 — corrects the "purely graph-level / one instantiation" pin).** The slot→brick
  map is clean and source-verified for every engine slot except `hρGv` (`hwmem ← chainData_bottom_relabel`,
  `hρe₀ ← G4d-i`, etc.), and the engine bindings `Gv = G−vᵢ` / `ends = relabelled` / `q = qρ` /
  `(a,b) = (vᵢ₊₁,vᵢ₋₁)` are KT-faithful (confirmed vs `chainData_bottom_relabel`'s landed output type,
  `Relabel.lean:1960–1972`). But `hρGv` cannot yet be supplied:
  - **P1 (BLOCKER) — LANDED 2026-06-20 (`Relabel.lean`, axiom-clean).** `wstep_foldl_freshEdge_slot_mem` +
    `wstep_foldl_hingeRow_telescope` are now stated over `(hinj : Set.InjOn w (Set.Iic (m + 2)))` instead of
    the dead `(hw : Function.Injective (w : ℕ → α))` (which is `False` over `[Finite α]`:
    `Finite.of_injective` + `not_finite ℕ`). The induction's IH gets the smaller-range form via
    `hinj.mono (Set.Iic_subset_Iic.mpr …)`; each `fun h => hw h; omega` became a range-scoped local
    `hne i j (≤N) (≤N) (≠)`. The arm now instantiates `hinj` from `cd.vtx_inj` (`Fin (d+1) → α` injective)
    via `Set.InjOn.mono`. Zero callers existed (only each other), so the restatement was self-contained;
    no d=3 regression. Lesson → FRICTION [idiom] *A `(w : ℕ → α)`-indexed lemma whose carrier will be
    `[Finite α]`…*.
  - **P2 (real math) — A-2 DE-RISK CORE LANDED 2026-06-20 (Route A).** The genuinely-new, KT-faithful
    perp carrier `candidate_perp_two_incident_panels` (+ its `supportExtensor`-perp form
    `candidate_perp_two_incident_supportExtensors`, the direct `hperp` shape) is now LANDED
    (`Relabel.lean`, both axiom-clean): at an interior degree-2 chain vertex `a = vₛ₊₁` (incident edges
    `ab = vₛ₊₁vₛ`, `ac = vₛ₊₁vₛ₊₂`), the common candidate vector `r̂ := ∑ⱼ λab • rab` is ⊥ **both**
    incident panels — `⊥ C_c` direct (each `rab j ∈ block e_c`, block closed under the combination),
    `⊥ C_d` via **eq.~(6.44)** `candidateRow_ac_eq_neg` (`rAC = −r̂`, each `rac j ∈ block e_d`, so `r̂ =
    −rAC ∈ block e_d`). This is the interior-vertex instance of KT eq.~(6.44) — the landed `d=3`
    single-degree-2-vertex column equation applies **verbatim** at an interior chain vertex (the
    structural fix the refuted isolated implication missed). **Self-contained over the explicit eq.~(6.52)
    witness, ZERO blast radius** (no live caller; the de-risk gate `i3_freshEdge_surviving_rows_mem_deRisk`
    + the general `freshEdge_surviving_row_mem` carry their perp as `hperp0`/`hperp1`/`hperp` hyps, which
    this discharges from the witness). Why this is correct where the row-318/321 pin was refuted: the
    refuted form was the *generic-`ρ₀` isolated implication* `ρ₀ ∈ block(edge s) → block(edge s+1)` (FALSE
    — the `_sup_` crux gives only *sup* membership, vacuous `=⊤` for independent consecutive panels); the
    landed form routes through the **specific** redundancy `r̂` (whose interior `a`-columns are non-trivial)
    via the per-edge `λ`/`r` witness — exactly §(o‴)(I.8.3.v-SETTLED) Route A. **A-1 LANDED 2026-06-20**
    (`Candidate.lean` + `Realization.lean`, axiom-clean, B=2 as scoped): the W6b producer
    `exists_candidateRow_bottomRows_of_rigidOn` now outputs `lamAB`/`rab` with `∀ j, rab j ∈ hingeRowBlock e₀`
    + `ρ = ∑ⱼ lamAB j • rab j` — the in-scope `r`/`lam` re-threaded (each `r j ∈ Eb = map (hingeRow …).dualMap
    block` factors as `hingeRow … (rab j)`; the candidate identity by `hingeRow` injectivity at distinct
    endpoints). `chainData_split_w6b_gates` threads it to its output in chain order (`(b,a)` branch negates
    `rab → −rab`, W8 sign-swap). 3 callers re-plumbed (`case_III_candidate_dispatch` `_`-ignores per d=3;
    `chainData_split_realization` `_`-ignores until the arm). Full project green + lint clean, d=3
    zero-regression. **WITHDRAW** (at the arm build, zero live callers) the refuted
    `freshEdge_surviving_row_mem` (the isolated-`hperp`-carrying builder) + `wstep_foldl_freshEdge_slot_mem`'s
    `hsurv` form; the closed-form telescope + `acolumn_..._sup_...` STAND. **NEXT = A-3**: feed the A-1
    witness through A-2 (`candidate_perp_two_incident_supportExtensors`) to discharge the
    `freshEdge_surviving_row_mem`/`i3_*` `hperp`/`hperp0`/`hperp1` hyps for real, generalize to all `i`, then
    the arm assembly `chainData_relabel_arm`. NO motive/IH change.
  - **P3 (flagged, likely clean ~½-commit).** The fold seed `shiftSeedAdv q (i−1)` (the `hW` span's seed)
    vs the engine/`chainData_bottom_relabel` seed `qρ = q ∘ shiftPerm i.castSucc` must coincide — NO landed
    lemma (searched); the (I.7.0) "H.10-confirmed" claim conflated the single-step cancel with the composed
    `shiftSeedAdv = q ∘ shiftPerm`. Named un-landed bridge `shiftSeedAdv_eq_funLeft_shiftPerm`.

  The A-2 de-risk CORE (the perp from the eq.~(6.52) witness) is now LANDED (Route A,
  `candidate_perp_two_incident_panels`/`_supportExtensors`); the remaining P2 work is purely A-1
  (re-thread the witness through the W6b producer to the de-risk's `hperp` hyps, B=2) → A-3 (all-`i`
  lift + arm). The `i=3` gates (`i3_freshEdge_slot_mem_deRisk` abstract `m=2` `sub_mem` peel;
  `i3_freshEdge_surviving_rows_mem_deRisk` concrete surviving-row membership, perp as `hperp0/1`) STAND
  as the de-risk shells the witness now feeds; their `hperp` hyps are what A-2's core discharges.
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
`foldl` order lands on the *inverse* product, exactly `(funLeft (shiftPerm i.castSucc)⁻¹)`), and the
**`hρGv` LEAF-ρ2** `shiftBodyListAsc_relabel_foldl_hingeRow` is now **LANDED 2026-06-20** (`Relabel.lean`,
axiom-clean — the relabel-only ascending `foldl` = inverse-cycle relabelled hinge row), and the
**`hρGv` LEAF-ρ1 algebraic core** `wstep_foldl_hingeRow_telescope` (+ helpers `wstep_hingeRow_off`/
`wstep_hingeRow_frontier`) is now **LANDED 2026-06-20** (`Relabel.lean`, axiom-clean — the general-`i`
closed form of the W9a `wstep` foldl = `(∑_{s<m} hingeRow wₛ wₛ₊₁) + hingeRow w_m w_{m+2}`, `m=i−1`,
the `i=3` gate's `m=2` generalization, KT eq. (6.66)), and the **`hρGv` general-`m` membership corollary**
`wstep_foldl_freshEdge_slot_mem` is now **LANDED 2026-06-20** (`Relabel.lean`, axiom-clean — the
`m=i−1` generalization of `i3_freshEdge_slot_mem_deRisk`, peeling the slot row from `W φ ∈ S` minus the
`m` surviving rows over an abstract `S`; the `hρGv` algebraic CLOSED FORM is COMPLETE), and **P1 (the
finite-range restatement of both, `Set.InjOn w (Set.Iic (m+2))`) is now LANDED 2026-06-20** (axiom-clean,
the `Function.Injective (ℕ→α)` interface was dead over finite `α`). So → the **arm wiring**
`chainData_relabel_arm`, **gated on P2/P3** (ARM-WIRING DESIGN-PASS §(o‴)(I.8) — NOT
"purely graph-level / one instantiation": **P2** (next) the `m` `hsurv` summands need
`ρ₀ ⊥ chain-edge panel` (deferred as abstract-`S` hyps, unbuilt); **P3** the fold-vs-engine seed bridge) +
**CHAIN-2c-iii** (the assembly `chainData_dispatch`), then
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

**Landed leaves toward the arm (settled; full per-leaf detail in *Decisions made* + §(o‴)(I.6)/(I.8)
+ the Lean docstrings + git):** the genuine-row `hwmem` leaf `chainData_bottom_relabel` (+ its 3 branch
bricks `rigidityRow_relabel_{off_cycle,to_block,to_genuine}`, the `hsupp_of` foundation
`ofNormals_supportExtensor_relabel_perm`, and the make-or-break crux `removeVertex_genuine_shiftRelabel`),
the `hρGv` G1 bridges (`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` / `wstep_foldl_funLeft_eq`) + LEAF-ρ2
(`shiftBodyListAsc_relabel_foldl_hingeRow`), and the LEAF-ρ1 algebraic core (`wstep_foldl_hingeRow_telescope`
+ the membership corollary `wstep_foldl_freshEdge_slot_mem`, finite-range per P1) — all LANDED axiom-clean.

**P1 LANDED 2026-06-20 — the algebraic core is now finite-range-callable.**
`wstep_foldl_{hingeRow_telescope,freshEdge_slot_mem}` restated over `Set.InjOn w (Set.Iic (m+2))` (axiom-clean,
zero callers existed so self-contained, d=3 zero-regression). The `Function.Injective (w : ℕ → α)` interface
was dead over the arm's `[Finite α]`; the arm now supplies `hinj` from `cd.vtx_inj` via `Set.InjOn.mono`.

**NEXT STEP — the arm wiring `chainData_relabel_arm`, gated on the TWO remaining prerequisites
(ARM-WIRING DESIGN-PASS §(o‴)(I.8), 2026-06-20).** The `hρGv` algebraic CLOSED FORM is complete + now
finite-range-callable (`wstep_foldl_hingeRow_telescope` + the membership corollary
`wstep_foldl_freshEdge_slot_mem`, both axiom-clean, P1 done), and the slot→brick map + engine bindings are
source-verified clean for every slot except `hρGv` (`Gv = G−vᵢ` / `ends = relabelled` / `q = qρ` /
`(a,b) = (vᵢ₊₁,vᵢ₋₁)`, confirmed vs the landed `chainData_bottom_relabel` output type
`Relabel.lean:1960–1972`; `hwmem ← chainData_bottom_relabel`, `hρe₀ ← G4d-i`, rest per `M₃`). Remaining: **(P2, real math) — PERP ROUTE SETTLED = Route A** (adversarial pair rows 322/323 +
user-authorized tie-breaker recon row 324; full verdict + grounding in §(o‴)(I.8.3.v-REFUTED)/(I.8.3.v-PAIR)/
(I.8.3.v-SETTLED)). The row-318 isolated-implication pin `ρ₀_perp_interior_chain_edge` is REFUTED (FALSE for
arbitrary `ρ₀` — the per-edge perp is a claim KT never proves, eq 6.66 is a vector *equality* in the eq-6.67
counting argument); route B/C is the route-(b) circularity (`htrans` forward-only `≤`, interior panels
`le_refl`-coincide); the interior surviving rows are GENUINELY INDEPENDENT, so the perp comes from the
SPECIFIC redundancy `r`/`g` (interior `a`-columns non-trivial) carried OUT of the W6b producer (the
`r`/`lam`/`∑λr` witness is computed in-scope `Candidate.lean:421–457` but DISCARDED at `:485` — re-threading,
not new math). **Build sequence (de-risk-first):** **(A-2 de-risk — DONE 2026-06-20)** the
self-contained perp carrier `candidate_perp_two_incident_panels` + the `supportExtensor`-perp form
`candidate_perp_two_incident_supportExtensors` (`Relabel.lean`, both axiom-clean): given the eq-(6.52)
witness (the per-edge-grouped `λ`/`r` data + the combination's `a`-column vanishing `hcol`/`hrest`) as
EXPLICIT hyps, the common candidate `r̂ := ∑λab•rab` is ⊥ both incident panels — ⊥ `C_c` direct (block
closed under the combination), ⊥ `C_d` via eq.~(6.44) `candidateRow_ac_eq_neg` (`rAC = −r̂`). This is the
direct `hperp0`/`hperp1`/`hperp` shape the de-risk gate / general builder carry as hyps; ZERO blast
radius. (The `d=3` single-degree-2-vertex `candidateRow_ac_eq_neg` applies VERBATIM at an interior chain
vertex — the structural fix the refuted isolated implication missed.) **(A-1 — DONE 2026-06-20,
axiom-clean)** the producer `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean`) now SUPPLIES the
eq-(6.52) `λ`-grouped `(ab)`-witness `lamAB`/`rab` (`∀ j, rab j ∈ hingeRowBlock e₀`, `ρ = ∑ⱼ lamAB j • rab j`
— the in-scope `r`/`lam` re-threaded via the per-row `Eb = map (hingeRow …).dualMap block` decomposition +
`hingeRow` injectivity at distinct endpoints), and `chainData_split_w6b_gates` (`Realization.lean`) threads it
to its output in chain order (`(b,a)` branch negates `rab → −rab`, W8 sign-swap). The 3 live callers re-plumbed
(d=3 dispatch + `chainData_split_realization` `_`-ignore until the arm); full project green + lint clean, d=3
zero-regression. **(A-3 single-vertex composition — DONE 2026-06-20, axiom-clean)** fed the A-1 witness through
A-2 (`candidate_perp_two_incident_supportExtensors`, the `hperp_ab`/`hperp_ac` + `hcol`/`hrest` interface) to
discharge `freshEdge_surviving_row_mem`'s `hperp` for REAL: the new composition lemma
`freshEdge_surviving_row_mem_of_witness` (`Relabel.lean`) takes the eq-(6.52) `λ`-grouped two-edge witness at
the surviving edge's interior degree-2 vertex `vtx (s+1)` (with `ρ₀ = ∑ⱼ lamAB j • rab j`, `hsd : s+1 < cd.d`
so `edge (s+1)` is a chain edge), applies A-2 to get `ρ₀ ⊥ Fva.supportExtensor (edge s)`, and threads it to the
`link`-half builder. ZERO blast radius (no live caller). **(NEXT) A-3 all-`i` lift — ROUTE FORK, recon-settled
to a de-risk-first (design §(o‴)(I.8.7), recon row 328, opus read-only Plan + coordinator scrutiny).** The
all-`i` lift must SUPPLY each interior vertex's witness (the `hsurv` summands, `m=i−1`), which A-1 gives only at
the base `e₀`. Recon verdict: the **witness-propagation route (Route W)** has NO landed supply (a genuinely-new
~3–5-commit producer if forced); the **RECOMMENDED route (G4d-i-PROJECTED)** — the d=3 M₃ mechanism, deriving
the interior perp from `hρe₀` + `hW`/the fold output + the LANDED two-edge sup form (`acolumn_..._sup_...`), NOT
`hcol`/`hrest` — hinges on ONE genuinely-new sup-projection lemma the recon could not confirm landed (flagged,
not pinned). **SMALLEST NEXT COMMIT = the i=3 DE-RISK**: confirm the interior perp at `i=3` (interior vertex v₁,
edges `edge 0=v₀v₁`/`edge 1=v₁v₂`) is derivable from `hρe₀` + `hW` + the two-edge degree-2 geometry WITHOUT the
per-vertex `hcol`/`hrest`. It DECIDES the fork before any leaf signature. **SUCCESS** → Route G4d-i-PROJECTED
(then `interior_perp_carry` + the `s↦s+1` induction `chainData_freshEdge_surviving_row_mem` + the arm;
`_of_witness`/A-2 orphaned, confirm-and-delete at the arm). **FAILURE** → Route W forced — **FLAG for user
adjudication** (genuinely-new math). **Orphan status FORK-DEPENDENT** — do NOT delete `_of_witness` / A-2
`candidate_perp_two_incident_*` until the de-risk decides (they STAND under Route W). `freshEdge_surviving_row_mem`
(the perp-half BUILDER — LIVE under BOTH routes; only the per-edge-perp slot-peel *framing* was withdrawn) + the
telescope (`:2938`/`:3006`) + the `_sup_` crux + A-1/A-2/`_of_witness` STAND. NO motive/IH change; d=3
zero-regression. Then the arm `chainData_relabel_arm`. (The refuted §(o‴)(I.8.4) step 2 / (I.8.6.v)
`ρ₀_perp_interior_chain_edge` route is superseded by (I.8.7).)
**(P3, flagged, likely
clean)** the fold seed `shiftSeedAdv q (i−1)` = engine seed `qρ` is an unbuilt bridge
(`shiftSeedAdv_eq_funLeft_shiftPerm`). Neither is a motive/signature change; option (b) + d=3 zero-regression
stand; ~3–4 commits (P2→P3→assembly). Sub-step sequence + exact signatures in design §(o‴)(I.8.4); the perp
verdict (Q1–Q4 vs KT 6.50–6.66 + the landed bricks) in §(o‴)(I.8.3.v)/(I.8.6.v).

> **⚠ SUPERSEDED OLD-ROUTE HISTORY — skip to the arm-wiring paragraph below.** Everything from here down
> to "**arm wiring `chainData_relabel_arm`**" (the `i=3`-de-risk / KT-source-re-derivation / LEAF-ρ1–ρ3 /
> "arm gated on P1/P2/P3-via-perp" narrative) is PRE-REFUTATION history, superseded by the Route-A
> settlement above (§(o‴)(I.8.3.v-SETTLED)): the per-edge-perp slot-peel framing is DEAD. The landed
> closed-form telescope `wstep_foldl_hingeRow_telescope` + its corollary `wstep_foldl_freshEdge_slot_mem`
> STAND as true linear-map infra, but their `hsurv` slot-peel framing is WITHDRAWN (Route A supplies the
> perp from the producer witness via the A-2 carrier `candidate_perp_two_incident_*` instead). Kept
> transiently for the arm-assembly structure + the orphan/confirm-and-delete lists; **a dedicated
> compression pass is DUE.** Audit trail: §(o‴)(I.7.x)/(I.8) + git.

**`i=3` de-risk DONE
(Lean-verified `i3_*_deRisk` lemmas) + KT-SOURCE RE-DERIVATION RESOLVED the path (§(o‴)(I.7.10),
owner-chosen recon).** The de-risk computed `W φ = hingeRow v₀v₁ + v₁v₂ + v₂v₄ ρ₀` / `R φ
= hingeRow v₀v₁ ρ₀` / `D φ = hingeRow v₁v₄ (−ρ₀)` — the three links `v₀—v₁` / `v₁—v₄` / slot `v₂—v₄`
diverge for `i≥3` (coincide at d=3, `vᵢ₋₁=v₁`). The KT recon **refuted the "slot wrong" reading**: the
engine slot `hingeRow vᵢ₊₁ vᵢ₋₁ ρ` is **KT-faithful** (forced by `case_III_arm_realization`'s `hG_ea/hG_eb`
= the split vertex's neighbors; = KT's `Mᵢ` fresh-edge row, eqs 6.56/6.64). The fold is faithful up to KT
6.62+6.63 (the `(v₀v₁)`-row form); the **missing piece is KT eq. (6.66)** — the iterated degree-2 `±r`
fresh-edge telescope (the "±r chain d=3 collapses"). **Option (b): buildable, NO engine/motive/IH/signature
change** (~3–5 commits). `D φ` at `v₁—v₄` was never the slot (red herring). **The build** (per the L5b
resolution — done inline where the role binding is concrete, generalizing d=3 M₃ `case hρGv`
`Relabel.lean:2437–2506`): identify the genuine reproduced-edge row at `vᵢ₋₁vᵢ` (LEAF-ρ2 + `hρe₀`), then
the KT-6.66 iterated degree-2 telescope (via `acolumn_mem_hingeRowBlock_of_span_rigidityRows` +
`hingeRow_sub_hingeRow_eq` + `shiftPerm_inv_*` + `case_III_bottom_relabel` + the landed `W φ ∈ span`) peels
the fresh-edge slot row `hingeRow v₂ v₄ ρ₀ ∈ span(G−vᵢ)`. **Re-targeted `i=3` de-risk** (the build's
internal check): confirm `hingeRow v₂ v₄ ρ₀` reaches `span` via the telescope (NOT "does `D φ` = slot" — it
provably does NOT, by design). d=3 (`i=2`) = the landed M₃ verbatim. **KT-FAITHFULNESS
RECON DONE + ROUTE LOCKED (§(o‴)(I.7.7), 2026-06-20):** an
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
- **LEAF-ρ1 algebraic core — LANDED 2026-06-20** (`wstep_foldl_hingeRow_telescope` + helpers
  `wstep_hingeRow_off`/`wstep_hingeRow_frontier`, `Relabel.lean`, all axiom-clean). The general-`i`
  closed form: the W9a `wstep` foldl over the ascending body list, applied to the base redundancy
  `hingeRow (w 0)(w 2) ρ₀`, telescopes to `(∑_{s<m} hingeRow (w s)(w (s+1)) ρ₀) + hingeRow (w m)(w (m+2))
  ρ₀` (`m=i−1`), over an injective vertex `w`. Proof = induction on `m` (`ofFn_succ'` peel; the `m`
  surviving rows are `wstep`-fixed, the frontier row advances), the `i−1`-step generalization of the
  `i=3` gate `i3_wstep_foldl_base_redundancy_deRisk` (`m=2` recovers it). This realizes KT eq. (6.66) as
  a clean closed form (NOT the per-step `sub_mem` telescope the design sketched — the telescope sum is
  exact, no residue bookkeeping). The general-`m` **membership corollary** `wstep_foldl_freshEdge_slot_mem`
  (LANDED 2026-06-20, axiom-clean — the `m=i−1` generalization of `i3_freshEdge_slot_mem_deRisk`) peels the
  slot row from `W φ ∈ S` minus the `m` surviving rows over an abstract carrier `S`, completing the `hρGv`
  algebraic bridge. **The remaining `hρGv` work is the arm wiring, gated on P1/P2/P3** (§(o‴)(I.8), NOT
  "purely graph-level"): P1 restate the corollary finite-range (the `(w:ℕ→α)`-injective interface is dead
  over finite `α`); then instantiate at `S := span (G−vᵢ).rigidityRows`, supply `hW` from
  `shiftBodyListAsc_foldl_mem_span_rigidityRows` (P3 seed-bridge), and the `hsurv` summand memberships (P2,
  the `ρ₀ ⊥ chain-edge panel` perp — the deferred real-math step). **The re-targeted `i=3` de-risk GATE is
  PASSED for the `sub_mem` ALGEBRA ONLY** (`i3_freshEdge_slot_mem_deRisk`, abstract `S`); P2 is what it
  deferred (it took `h01`/`h12` as hyps, never checked them at concrete `span (G−v₃)`). (Design §(o‴)(I.8)
  RESIDUAL; the algebra is discharged, the graph-level memberships are not.)
- **LEAF-ρ3 — the `hρGv` assembly inline in the arm** (now decomposed into P1+P2+P3+assembly, §(o‴)(I.8.4);
  NOT a single instantiation — P1 is a Lean-confirmed BLOCKER, P2 is genuinely-new math).
- **LEAF-ρ2 — LANDED 2026-06-20** the literal-row identification `shiftBodyListAsc_relabel_foldl_hingeRow`
  (the landed G1 bridges + `hingeRow_funLeft_dualMap`; this is the genuine relabel-image row — correct +
  load-bearing, but does NOT discharge the slot alone).
NOT a motive/IH/contract change. Then the **arm wiring `chainData_relabel_arm`** (§(o‴)(I.8.4) sub-steps):
`refine case_III_arm_realization` at the per-`i` roles (cycle generalization of d=3
`case_III_arm_realization_M3`): seed `qρ = q ∘ shiftPerm i.castSucc`, shared `−ρ₀`; `hwmem` → landed
`chainData_bottom_relabel`; `hρGv` → P1/P2/P3 (flip orientation via `hingeRow_swap` — the corollary emits
`hingeRow vᵢ₋₁ vᵢ₊₁ ρ₀`, the OPPOSITE order to the engine's `hingeRow vᵢ₊₁ vᵢ₋₁ ρ`, as `M₃`'s
`case hρGv` opens `Relabel.lean:2475`); block → `blockRow_relabel_perm`; `hρe₀`/`htrans` → G4d-i +
2c-i's discriminator (~1 commit of §38 explicit-seed slot bookkeeping). → **2c-iii** `chainData_dispatch`
(replaces `case_III_candidate_dispatch`) → **CHAIN-5** (in 23c). Close-boundary timeline: **~4–5 commits
to the closed arm** (P1→P2→P3→assembly) then 2c-iii. d=3 M₃ = `i=2` involution (zero-regression). Orphan-for-the-arm at the
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
- **2c-ii-arm transport bricks all LANDED 2026-06-19/20 (axiom-clean) — verdicts only; canonical list =
  the *Genuine-row `hwmem` transport bricks* + *Landed CHAIN-2 leaves* blocks below.** The genuine-row
  `hwmem` disjunct is a removeVertex-level per-row case-split (generalizing `case_III_bottom_relabel`, NOT
  a split graph-iso, NOT a W9b fold; §(o‴)(I.5)/(I.6)). Landed: the 3 genuine-row branches (off-cycle /
  wrap→`±r`-block / interior-chain-edge `…to_genuine`), both block-orientation bricks, the `hsupp_of`
  foundation, the make-or-break `removeVertex_genuine_shiftRelabel`, the per-member assembly
  `chainData_bottom_relabel`, the `hρGv` G1 bridges, and LEAF-ρ2. Proof lessons → TACTICS-QUIRKS §38
  (explicit-seed `whnf`) / GOLF §20 (`reverseRec`, the `foldl`→inverse recurrence) / the FRICTION [idiom]
  entries; per-brick mechanics = git + design §(o‴) + the Lean docstrings.
- **`hρGv` algebraic core + P2 crux — LANDED 2026-06-20, all axiom-clean (one-line verdicts; full detail
  = §(o‴)(I.7.10)/(I.8) + git + the Lean docstrings + the promoted FRICTION idioms):**
  - **LEAF-ρ1 closed-form telescope** `wstep_foldl_hingeRow_telescope` (+ helpers `wstep_hingeRow_off`/
    `_frontier`): the general-`i` `wstep` foldl of `hingeRow (w 0)(w 2) ρ₀` = `(∑_{s<m} hingeRow wₛ wₛ₊₁ ρ₀)
    + hingeRow w_m w_{m+2} ρ₀` (`m=i−1`). **An EXACT closed-form sum, NOT the per-step residue telescope
    §(o‴)(I.7.3) sketched** (KT eq. 6.66; `m=2` recovers the i=3 gate).
  - **general-`m` slot membership** `wstep_foldl_freshEdge_slot_mem` + the **i=3 gate**
    `i3_freshEdge_slot_mem_deRisk`: the slot row = `W φ − (∑ surviving rows) ∈ S` (`sub_mem`/`sum_mem`,
    abstract over the span carrier `S` — the `sub_mem` ALGEBRA only, NOT the concrete memberships).
  - **P1** the finite-range restatement: both telescope lemmas restated in place over
    `Set.InjOn w (Set.Iic (m+2))` (the dead `Function.Injective (ℕ→α)` is `False` over `[Finite α]`); the
    arm supplies `hinj` from `cd.vtx_inj` via `Set.InjOn.mono`.
  - **P2 two-edge column crux** `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`: at an interior
    degree-2 vertex `a` (two surviving links `e_c`/`e_d`), the `a`-column ∈ `hingeRowBlock e_c ⊔ e_d` (KT
    eq. 6.44 two-block; the honest analogue of the one-edge G4d-i, provably non-instantiable there). Also
    the P2 i=3 concrete-link gate `i3_freshEdge_surviving_rows_mem_deRisk` (link half clean, perp isolated).
  - **P2 general-`i` surviving-row builder** `Graph.ChainData.freshEdge_surviving_row_mem`: the lift of the
    i=3 de-risk gate's `hrow` to general candidate `i : Fin (cd.d+1)` + edge index `s` (`s+1 < (i:ℕ)`) —
    `hingeRow (vtx s)(vtx s+1) ρ₀ ∈ span (G−vtx i) rigidityRows` once the per-edge perp `hperp` is supplied.
    The `link`/membership half is fully discharged (`cd.link` + `vtx_inj` survival + `hingeRow_mem_rigidityRows`
    + `mem_hingeRowBlock_iff`); the perp is the explicit gate hyp (standing crux idiom). This is exactly the
    `hsurv` summand `wstep_foldl_freshEdge_slot_mem` defers, packaged per-edge for the arm. FRICTION [idiom]
    *`ChainData.vtx_ne` against a `Fin (d+1)` variable index — prove `≠` via `congrArg Fin.val (vtx_inj ·)`…*.
  - **P2 A-2 de-risk CORE — LANDED 2026-06-20 (Route A; the perp from the eq-6.52 witness):**
    `candidate_perp_two_incident_panels` (+ the `supportExtensor`-perp form
    `candidate_perp_two_incident_supportExtensors`, the direct `hperp` shape), `Relabel.lean`, both
    axiom-clean. At an interior degree-2 chain vertex, the common candidate `r̂ := ∑λab•rab` is ⊥ both
    incident panels: ⊥ `C_c` direct (`Submodule.sum_mem`/`smul_mem`), ⊥ `C_d` via eq.~(6.44)
    `candidateRow_ac_eq_neg` (`rAC = −r̂`, block `neg_mem`). The `d=3` single-degree-2-vertex
    `candidateRow_ac_eq_neg` applies VERBATIM at an interior vertex (`a := vₛ₊₁`, `b := vₛ`, `c := vₛ₊₂`)
    — the structural fix the refuted *generic-`ρ₀` isolated implication* `ρ₀_perp_interior_chain_edge`
    missed (the `_sup_` crux is vacuous `=⊤` for independent consecutive panels; the perp lives in the
    *specific* `r̂`, not arbitrary `ρ₀`). Self-contained over the explicit witness, ZERO blast radius —
    discharges the de-risk gate's `hperp0`/`hperp1` + the builder's `hperp` from the witness. The
    isolated-implication `freshEdge_surviving_row_mem` / the `hsurv` form of
    `wstep_foldl_freshEdge_slot_mem` are WITHDRAWN at the arm build (zero live callers).
  - **P2 A-1 — LANDED 2026-06-20 (the W6b witness re-thread; the blast-radius step, B=2 as scoped):**
    `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean`) + `chainData_split_w6b_gates`
    (`Realization.lean`), both axiom-clean. The producer now outputs the eq-(6.52) `λ`-grouped `(ab)`-edge
    witness `lamAB`/`rab` (`∀ j, rab j ∈ hingeRowBlock e₀`, `ρ = ∑ⱼ lamAB j • rab j`) — the in-scope `r`/`lam`
    re-threaded: each row `r j ∈ Eb = map (hingeRow …).dualMap block` factors as `hingeRow … (rab j)` (per-`j`
    choice), and the candidate identity follows by `hingeRow` injectivity at distinct endpoints (both sides map
    to `r̂`). The wrapper threads it to its output in chain order; the `(b,a)` normalization branch negates
    `rab → −rab` (block `neg_mem`, `−ρ = ∑ⱼ lamAB j • (−rab j)`), matching the W8 sign-swap on `ρ`. 3 live
    callers re-plumbed (d=3 dispatch + `chainData_split_realization` `_`-ignore the new data until the arm).
    Full project green + lint clean, d=3 zero-regression. This is the per-edge witness shape A-2 consumes;
    NEXT = A-3 (feed it through A-2 to discharge the `hperp` gates for real, all-`i` lift, arm). FRICTION
    [idiom] *`hingeRow u v` (a `def`) isn't seen as a bundled map by `map_sum`/injectivity — `rw
    [hingeRow_eq_dualMap]` first*.
  - **P2 A-3 single-vertex composition — LANDED 2026-06-20, axiom-clean, ZERO blast radius:**
    `freshEdge_surviving_row_mem_of_witness` (`Relabel.lean`). The Route-A closure of
    `freshEdge_surviving_row_mem`'s abstract `hperp`: at a surviving edge's interior degree-2 chain vertex
    `vtx (s+1)` (`hsd : s+1 < cd.d`, so `edge (s+1)` is a chain edge; the two incident chain edges are
    `e_c = edge s`/`e_d = edge (s+1)`), feed the eq-(6.52) `λ`-grouped two-edge witness (the A-1 producer's
    `lamAB`/`rab`/`lamAC`/`rac`/`grest` + the per-edge perps + col-vanishing) through A-2
    (`candidate_perp_two_incident_supportExtensors`) to get `ρ₀ = ∑ⱼ lamAB j • rab j ⊥ Fva.supportExtensor
    (edge s)` FOR REAL (A-2's first conjunct), then `exact cd.freshEdge_surviving_row_mem … hperp`. The `≠`
    side-conditions `hab`/`hac` reuse the logged `congrArg Fin.val ∘ vtx_inj` idiom; the proof is a 2-`have` +
    `exact` composition (no friction, built first try). NEXT = A-3 all-`i` lift (the iterated KT eq-(6.66)
    carry — supply each interior vertex's col-vanishing witness, the genuinely-hard remaining piece) + the arm.
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
