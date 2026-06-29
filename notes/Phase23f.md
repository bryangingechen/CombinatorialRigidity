# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **THIS SESSION LANDED the dispatch's interior `ends → ends₀` transfer
`PanelHingeFramework.chainData_dispatch_interior_of_discriminator` (`CaseIII/Realization.lean`)** — the `ends₁`
mechanical-plumbing half of the router: it takes the base-`v₁`-split discriminator
(`exists_shared_redundancy_and_matched_candidate`) output VERBATIM (at the honest base selector `ends`, the
`Gab`-recording) and, at a matched interior `i` (`2 ≤ i`, `3 ≤ cd.d`), produces `HasGenericFullRankRealization k n G`.
Body: build `ends₀ := Function.update³ ends` overriding the three edges the `Gab`-recording does not orient — the base
body `vtx 1`'s two degree-2 chain edges `edge 0`/`edge 1` (so `ends₀` records every `G`-link via
`fullLink_recording_of_splitOff_recording`) + the splice `e₀` (normalized to `(vtx 2, vtx 0)` for `he₀rec`); all three
override edges LINK `vtx 1`, so none is a `Gv = G − vtx 1`-link, hence the discriminator's `Gv`-stated facts
(`hwmem'`/`hedgeGv`/`hρ₀Gv`) transfer to `ends₀` unchanged via `rigidityRows_ofNormals_congr_ends` (+ a per-edge
`hingeRowBlock` congruence for `hedgeGv`), and the `e₀`-panel `hρ₀e₀` / matched gate `hLI`/`hgate` are selector-free;
then it calls the landed `chainData_dispatch_interior`. Axiom-clean `[propext, Classical.choice, Quot.sound]`, full
build (2830 jobs) + lint green, `d=3` untouched, zero blast radius (no live consumer). Below the C.0–C.6 contract +
0-dof motive; no cert change, no new LA. **NEXT = the dispatch ROUTER** `chainData_dispatch`: fire the discriminator
ONCE at the base `v₁`-split (deriving `h622lb` from `case_III_nested_rank_lower_all_k`; taking `hdef_Gab`/`hsplitGP`
as hypotheses, the `hdispatch` shape), case-split `(i : ℕ)`: interior `2 ≤ i` → THIS lemma (the transfer is DONE);
the `i ≤ 1` base-candidate + `d=3` floor → `chainData_split_realization` (its `htrans` from the same discriminator,
reconciled across the `(vtx 1, vtx 0, vtx 2)`-base vs `(vtx 1, vtx 2, vtx 0)`-candidate a/b-swap). Lands with the
approved C.3 `hIH` add. See *Hand-off*. The §(4.100) route was SETTLED as a SELECTOR re-target
(`candidateEnds → ends₀` + the SPARSE `Function.update` override
`endsσρ₁` bridged by `rigidityRows_ofNormals_congr_ends`).
The reshape ASSEMBLY is underway: the honest engine `case_III_rank_certification` (`Candidate.lean:1662`, ALREADY
general-`k`) sources `±r` via the eq.-(6.27) ROW-OP of a BOTTOM `G−v`-row (decoupling the gate from the
membership — no §(4.91) collision); the interior-`hρGv` row membership (§(4.95)) is the LANDED crux leaf
`chainData_relabel_arm_hρGv` (`ChainColumn.lean:1390`). The interior arm wires the engine at the interior split
tuple `(v,a,b) = (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc)` with candidate functional `−ρ₀`, at the
candidate-relabelled framework `ofNormals (G − vᵢ) endsσρ qρ` — **the build CONFIRMED the real satisfiability
test:** the bottom family `w`/`hwmem` (the `chainData_bottom_relabel` disjunction shape) + the relabelled-`endsσρ`
structural slots fill the honest engine defeq-clean for the interior. The gate slots reduce through the landed
seed reads `seedShift_succ_/pred_castSucc`. **The §(4.96) interior-branch satisfiability spike then probed the
WHOLE dispatch composition head-on (discriminator fired, all 11 arm slots fed its ACTUAL outputs): 6/11 discharge
exit-0, but the spike found the live blocker = a SELECTOR-ORIENTATION interface gap** — `hends_ea`/`hends_eb` (+
`hρe₀`'s `hends_i`, + the bottom-relabel's `he₀rec`) need the SPECIFIC split-body-first orientation of `ends₀` at
the re-inserted hinges + `e₀`, which the discriminator's IH `ends₀ = Q.ends` gives only as a free disjunction. The
honest arm conflates the raw-`ends₀` bottom role with the orientation-forced hinge role into one `endsσρ` (the d=3
M₃ arm SEPARATES them via a `Function.update` override `ends₃`). **NEXT = add the orientation-override shim (fix A,
the M₃ `ends₃` pattern) to the interior arm, THEN build the `chainData_dispatch` router**, then discard the
diverged `_aug`/`rigidityMatrixEdgeAug` fork. NOT row-598, NOT §(4.91) — the reshape's engine-level GO stands; the
arm/dispatch INTERFACE needs the shim. Below the C.0–C.6 contract + the 0-dof motive; NO shortcut. `d=3`
stays fully green (it runs the SAME honest engine via the `k=2` spine). Authoritative scoping:
`notes/Phase23-design.md` §(4.96) (the interior-branch spike → BLOCKED-with-exact-residual + the two fixes),
§(4.95) (crux-leaf-landed GO), §(4.94) (the reshape + the `d=3` mechanism), §(4.93)
(the cert-interface obstruction), §(4.92) (route-(a) corner core), §(4.91)/(4.90)/(4.84)–(4.89) (the refuted
(D-substitution)/override arc), §§(4.77)–(4.83) (the six route refutations). Program map:
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`). 23f built the geometry-arm cert
infrastructure (interior-corner cert, D-CAN bottom, the `_aug` ladder), refuted six narrow corner routes, then
spent a full session building the (D-substitution) re-architecture — which a final dispatch found is OFF-BY-ONE
at the corner. When the geometry arm closes, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THIS SESSION: the dispatch's interior `ends → ends₀` transfer `chainData_dispatch_interior_of_discriminator` LANDED**
(`CaseIII/Realization.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build (2830 jobs) + lint green,
`d=3` untouched, zero blast radius). The `ends₁` mechanical-plumbing half of the router: takes the base-`v₁`-split
discriminator (`exists_shared_redundancy_and_matched_candidate`) output VERBATIM (at the honest base selector `ends`,
the `Gab`-recording) and, at a matched interior `i` (`2 ≤ i`, `3 ≤ cd.d`), produces `HasGenericFullRankRealization k n
G`. Body: build `ends₀ := Function.update³ ends` overriding the three edges the `Gab`-recording does not orient — the
base body `vtx 1`'s two degree-2 chain edges `edge 0`/`edge 1` (`fullLink_recording_of_splitOff_recording` → `ends₀`
records every `G`-link) + the splice `e₀ ↦ (vtx 2, vtx 0)` (for `he₀rec`); all three override edges LINK `vtx 1`, so
none is a `Gv = G − vtx 1`-link → the discriminator's `Gv`-stated `hwmem'`/`hedgeGv`/`hρ₀Gv` transfer to `ends₀`
unchanged via `rigidityRows_ofNormals_congr_ends` (+ a per-edge `hingeRowBlock` congruence for `hedgeGv`), and the
`e₀`-panel `hρ₀e₀` / matched gate `hLI`/`hgate` are selector-free; then call the landed `chainData_dispatch_interior`.
**What remains = the dispatch ROUTER** `chainData_dispatch`: fire the discriminator ONCE at the base `v₁`-split (derive
`h622lb` from `case_III_nested_rank_lower_all_k`; take `hdef_Gab`/`hsplitGP` as hypotheses, the `hdispatch` shape),
case-split `(i : ℕ)`: interior `2 ≤ i` → THIS session's transfer lemma (DONE); `i ≤ 1` base-candidate + `d=3` floor →
`chainData_split_realization` (`:1227`, its `htrans` from the same discriminator; the `(vtx 1, vtx 0, vtx 2)`-base vs
`(vtx 1, vtx 2, vtx 0)`-candidate a/b-swap reconciled by `splitOff_swap_ab`). Lands with the approved C.3 `hIH` add.

**PRIOR SESSION: the dispatch's INTERIOR BRANCH `chainData_dispatch_interior`** (`CaseIII/Realization.lean`,
axiom-clean, gates green, `d=3` untouched) — the load-bearing arm core: at a matched interior `i` it wires the honest
arm `chainData_interior_realization_hρGv` to all per-slot suppliers from the `ends₀`-shaped discriminator data (crux
`±r` ← `chainData_relabel_arm_hρGv` + `fullLink_recording_of_splitOff_recording`; `hρe₀` ← `interior_hρe₀_of_
baseWidening`; override `endsσρ₁`; bottom `L ∘ w` ← `chainData_bottom_relabel`; gate ← `candidateVtx_succ_eq`). This
session's transfer lemma feeds it the `ends → ends₀` override.

**PRIOR SESSION: `chainData_freshEdge_slot_perp_ends₀` (`ChainColumn.lean:1406`) — the §(4.101) `hperp`-at-`ends₀` perp
producer (axiom-clean, build + lint green, `d=3` untouched).** Produces `ρ₀ ⊥ (ofNormals (G − vᵢ) ends₀ qρ).supportExtensor
(edge s)` at the HONEST `ends₀` selector (NOT the relabel-image `endsσρ` — the two support extensors at `edge s` coincide
only up to sign). Reduces the `ends₀`-form panel via the recording `hrec`/`hrece₀` + `shiftPerm`: interior `s ≥ 1` →
`±panel(q(vtx s+1))(q(vtx s+2))` = base support at `edge (s+1)` (STEP 1 `chainData_freshEdge_perp_of_baseRedundancy`);
head `s = 0` → the `e₀` panel (base perp `hρe₀`, via `hrece₀`). Orientation absorbed by `perp_panelSupportExtensor_swap`.
Consumed by the leaf re-target above.

**(B′) (prior session): the discriminator RE-EXPOSES `_hρ₀Gv` (base redundancy span at the honest `ends`) + `hrec'`
(full `Gab`-link recording incl. `e₀`)** — the inputs the leaf re-target / the new perp producer consume.
`chainData_split_w6b_gates` (`Realization.lean:889`) RETURNS `hrec'`; `exists_shared_redundancy_and_matched_candidate`
(`:2322`) RETURNS both. Exposing-not-proving, axiom-clean, build + lint green, zero blast radius (no live discriminator
consumer yet).

**THE RESHAPE (§(4.94)/(4.95)) — THE INTERIOR ARM IS LANDED + §(4.100)-RE-TARGETED.** The honest engine
`case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine, ALREADY general-`k`) sources
`±r` via the eq.-(6.27) ROW-OP `hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ` (genuine present-body `e_b`-row
− BOTTOM `G−v`-row `hρGv`), decoupling the gate from the membership. The honest interior arm
`chainData_interior_realization_hρGv` (`Realization.lean:1364`) re-indexes `case_III_arm_realization` at the
interior split tuple, candidate functional `−ρ₀`, candidate seed `qρ = q ∘ shiftPerm i.castSucc`; its gate slots
`hLn`/`hgab`/`hρgate`/`hρe₀` reduce through the landed seed reads `seedShift_succ_/pred_castSucc` (the engine
`b`-role reads at the SPLIT BODY, so `hgab`'s pair is `(a,v)`, the cycle analogue of `M₃`'s `hqρv`); `hρe₀` from
`interior_hρe₀_of_widening` with the `−ρ₀` flip. After §(4.100)/§(4.102) the crux `hρGv` slot is at the HONEST base
selector `ends₀ qρ` (the re-targeted leaf `chainData_relabel_arm_hρGv` lands there) bridged to the override `endsσρ₁`
via the EXACT `rigidityRows_ofNormals_congr_ends`, while the bottom `hwmem` slot is at the relabel-image
`candidateEnds i ends₀` (where `chainData_bottom_relabel` lands) bridged via the SWAP-tolerant
`rigidityRows_ofNormals_congr_ends_swap`. The structural
slots `hends_ea`/`hends_eb`/`hends_Gv` are dispatch-supplied via the LEAF-1 supplier
`candidateEnds_records_splitOff_isLink` (`Relabel/Chain.lean:312`). NEXT = the `chainData_dispatch` router. See
*Hand-off* + §(4.94)/(4.95)/(4.100).

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched).**
- **The selector-route + interior-assembly pieces (prior + this session)** — one-line verdicts in *Decisions made →
  reshape ASSEMBLY* (full detail there + design §(4.100)–(4.104) + git): the `ends₀`-perp producer
  `chainData_freshEdge_slot_perp_ends₀` (§(4.101)); the leaf re-target `chainData_relabel_arm_hρGv → ends₀`
  (`ChainColumn.lean:1519`); the arm `congr_ends` bridges + §(4.102) `hwmem` re-statement +
  `rigidityRows_ofNormals_congr_ends_swap` (`Realization.lean:92`); (B′)'s discriminator re-exposure; the crux leaf's
  `hrec` supplier `fullLink_recording_of_splitOff_recording`; the interior branch `chainData_dispatch_interior`; and
  this session's interior `ends → ends₀` transfer `chainData_dispatch_interior_of_discriminator`.
- **THE `hends_i` DISJUNCTION-RELAXATION + `splitOff_swap_ab` (§(4.98)):** the widening chain
  (`baseRedundancy_perp_interior_reproduced_panel`/`interior_hρe₀_of_widening`/`interior_hρe₀_of_baseWidening`,
  `ForkedArm.lean`) now takes `hends_i` as the orientation DISJUNCTION (discharging the §(4.96) `hends_i` residual
  from the discriminator's free-orientation `hends'`); `Graph.splitOff_swap_ab` (`Operations.lean`) the base-split
  a/b-symmetry. No `d=3` content; no motive/IH/cert change.
- **THE LANDED LEAF-1 SELECTOR-RECORDING SUPPLIER (prior session):** `candidateEnds_records_splitOff_isLink`
  (`Relabel/Chain.lean:312`) — IF `ends₀` records every `v₁`-base-split link THEN `cd.candidateEnds i ends₀`
  records every candidate-`i`-split link (`1 < i`); the unified supplier for the interior arm's three selector
  slots `hends_ea`/`hends_eb`/`hends_Gv`. Generic in `ends₀`; proof = `splitOff_isLink_shiftRelabel_iff` `.mp` +
  recording + `Equiv.symm_apply_apply`.
- **SURVIVES the reshape (the honest engine + its general-`k` infrastructure, §(4.94)):** the honest cert
  `case_III_rank_certification` (`Candidate.lean:1662`, general-`k`!) + arm `case_III_arm_realization`/`_M2`
  (`Arms.lean:310`); `chainData_split_realization` (`Realization.lean:1164`, base/floor route + interior arm
  template); the base `hρGv` producer `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:401`) +
  `chainData_split_w6b_gates` (`Realization.lean:889`); the discriminator `exists_shared_redundancy_and_matched_
  candidate` (`Realization.lean:2134`) + `case_III_claim612_gen` (`Claim612.lean:1333`); `interior_hρe₀_of_
  widening` (`ForkedArm.lean:768`, the `hρe₀` slot); the column carry `interior_group_acolumn_eq_neg_base
  Redundancy` (`ChainColumn.lean:729`, ingredient for the new leaf); `hingeRow_sub_hingeRow_eq` (`Basic.lean:612`);
  the interior-arm seed reads `seedShift_succ_castSucc`/`seedShift_pred_castSucc` (`Induction/Operations.lean`,
  landed this session — `qρ(a,·)`/`qρ(b,·)` at the arm roles, the M₃-`hqρc`/`hqρv` analogues the gate slots
  reduce through); the bottom-family per-member relabel `chainData_bottom_relabel` (`Chain.lean:316`); the gate
  bridge `candidateVtx_succ_eq` + the interior `removeVertex`/IsLink/split accessors (`Operations.lean`, the
  `endsσρ`-free structural slots).
- **DISCARDED at the reshape (the diverged `_aug`/`rigidityMatrixEdgeAug` interior fork + the refuted arms):**
  the backbone `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1258`, AS the
  interior cert) + the cert forks `case_III_rank_certification_aug{,_ofNormals}`/`_matrix{,_sep}`/`_zero₁₂`/
  `_chain` (`Candidate.lean:2429`–`2783`); the arm `case_III_arm_realization_aug_ofNormals` (`ForkedArm.lean:
  1309`) + `hr`-filler `hingeRow_mem_ofNormals_rigidityRows_chainEdge` (`:621`, the colliding membership); the
  `caseIIICandidate` override device + `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`; the override
  spine/corner (`Realization.lean:1625`/`:1761`); the (D-subst) S1–S5 `_ofNormals` siblings. Complete lemmas, no
  `sorry`s — retire at the reshape build (or phase-close).

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean + SATISFIABLE; 23f only *produces*
  its block data. Build against the literal `Lrow * M * U` product, NOT the component leaves in isolation
  (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before declaring "remaining = assembly").
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through the general-`d` cert. Do NOT unify the two. (The reproduced→chain-edge panel coincidence is a
  `d=3` single-swap `shiftPerm 2` body-rename; the corner seam is a `d ≥ 4`-only phenomenon, §(4.83)/(4.90).)
- **Below the CHAIN↔ENTRY contract TYPES + the motive/IH.** The geometry arm + dispatch are below the C.0–C.6
  signatures and the 0-dof motive (no new motive conjunct, no IH-strength change, no `ChainData` field). The
  override route adds the APPROVED C.3 `hIH` field (below) when the dispatch is wired — not a motive change.

## Lemma checklist

**§(4.99)→§(4.100)→§(4.101) RESOLVED: the §(4.95) "crux leaf LANDED, reshape = pure ASSEMBLY" was OVER-OPTIMISTIC — the
leaf `chainData_relabel_arm_hρGv` was landed but its `hφ` slot was MIS-STATED (a mixed `(G−v₁, endsσρ, q)` framework with
no honest producer). The fix was a SELECTOR re-target (NOT a fold re-statement): re-target the leaf to the HONEST base
selector `ends₀` + a SPARSE `Function.update` override in the arm bridged by `congr_ends`. This session LANDED the leaf
re-target itself (`chainData_relabel_arm_hρGv` now at `ends₀`, fed by the prior-session `ends₀`-perp producer); NEXT = the
arm's `congr_ends` override bridge (Probe E2) + the dispatch — see *Hand-off* + §(4.100)/§(4.101).**

- [x] **THE OVERRIDE-COMPOSITION SPIKE — RAN, REFUTED (§(4.91), row 600).** §(4.82)/(4.83) STAND. Detail: §(4.91).
- [x] **THE KT-FAITHFULNESS SCOPING (§(4.92)) + THE ROUTE-(a) CORNER SPIKE (§(4.93)) — DONE.** Corner core
  `corner_hA'_of_gate` composes (sub-Q A GO), but the `_aug` cert's `hr : rRow ∈ span F.rigidityRows` slot
  REFUTES route (a) — the TRUE obstruction is the cert INTERFACE (`rigidityMatrixEdgeAug` forces `±r` onto a
  framework edge, colliding with the gate). Detail: §(4.93).
- [x] **THE `d=3`-ANCHORED CERT-INTERFACE DESIGN-PASS — DONE (§(4.94), session #48).** The WORKING `d=3` cert is
  `case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine, ALREADY general-`k`),
  sourcing `±r` via the eq.-(6.27) ROW-OP of a BOTTOM `G−v`-row, NOT the `_matrix`/`_aug` fork. Reshape = route
  the interior through that engine. SURVIVES/DISCARDS + the spike-flagged new leaf in §(4.94).
- [x] **THE INTERIOR-`hρGv`-MEMBERSHIP SPIKE — RAN, GO (§(4.95), row 604).** The interior `hρGv` row membership
  is TRUE, honestly provable from the single base `ρ₀`, and ALREADY LANDED sorry-free as
  `Graph.ChainData.chainData_relabel_arm_hρGv` (`Relabel/ChainColumn.lean:1390`; coordinator-verified — right
  conclusion, axiom-clean, green; collision-free in the honest engine). The §(4.94) open leaf is DISCHARGED; no
  genuinely-new LA leaf remains. Detail: §(4.95).
- [x] **THE INTERIOR-ARM SEED READS — LANDED (`seedShift_succ_castSucc`/`seedShift_pred_castSucc`,
  `Induction/Operations.lean`, axiom-clean).** The cycle-arm `qρ(a,·)`/`qρ(b,·)` reads at the engine roles
  `a = vtx i.succ`, `b = vtx (i−1).castSucc` (`qρ = q ∘ shiftPerm i.castSucc`): `a`'s index `i+1` is off the
  cycle (fixed → base `q(vtx i.succ,·)`); `b`'s index `i−1` is interior (`2 ≤ i`, shifts → split body
  `q(vtx i.castSucc,·)`). The cycle generalization of `M₃`'s `hqρc`/`hqρv`; the foundation the interior arm's
  `hLn`/`hgab`/`hρgate`/`hρe₀` gate slots reduce through (gate bridge already landed:
  `candidateVtx_succ_eq`). Beside the existing `seedShift_inv_cancel`/`seedShift_off_cycle`.
- [x] **THE RESHAPE BUILD — the honest interior arm `chainData_interior_realization_hρGv` — LANDED** (§(4.94) Part 4;
  re-indexes the honest general-`k` engine `case_III_arm_realization` at the interior split tuple, functional `−ρ₀`,
  candidate seed `qρ`; gate slots via `seedShift_succ_/pred_castSucc`, `hρe₀` via `interior_hρe₀_of_widening`). Current
  state (after the §(4.100) step-2 re-target) is the top LANDED-INVENTORY entry; the all-`i` generalization of
  `case_III_arm_realization_M3` (`i=2`).
- [x] **THE LEAF-1 SELECTOR-RECORDING SUPPLIER — LANDED** (`candidateEnds_records_splitOff_isLink`,
  `Relabel/Chain.lean:312`, axiom-clean `[propext, Classical.choice, Quot.sound]`, gates-clean). §(4.10) LEAF-1:
  for an interior `1 < i`, IF the base selector `ends₀` records every link of the `v₁`-base split, THEN the
  relabel-image selector `cd.candidateEnds i ends₀` records every link of the candidate-`i` interior split. This
  is the unified supplier for the interior arm's THREE selector slots — `hends_ea`/`hends_eb` (the two
  re-inserted chain hinges) and `hends_Gv` (the surviving `Gv = G − vᵢ` links) all reduce to "every such link IS
  a candidate-split link", recorded by this lemma. Generic in `ends₀`; proof is the `splitOff_isLink_shiftRelabel_iff`
  `.mp` intertwiner + `ends₀`'s recording + `Equiv.symm_apply_apply` on `candidateEnds`. No `d=3` content, no new
  LA, no motive/IH/contract change.
- [x] **THE `chainData_dispatch` INTERIOR-BRANCH SATISFIABILITY SPIKE — RAN, BLOCKED-with-exact-residual (§(4.96)).**
  Head-on kernel-checked: fired the discriminator once, fed its ACTUAL outputs into the interior arm; the composition
  typechecks, 6/11 slots discharge exit-0, but `hends_ea`/`hends_eb`/`hρe₀`-`hends_i`/`he₀rec` need the SPECIFIC
  split-body-first ORIENTATION of `ends₀` at the re-inserted hinges + `e₀`, which the discriminator's IH `ends₀ =
  Q.ends` gives only as a free disjunction. NOT row-598 / NOT §(4.91) — a SELECTOR-ORIENTATION interface gap. Detail
  + the two below-contract fixes (A: arm override slot / B: discriminator orientation-normalization): §(4.96).
- [x] **THE ORIENTATION-OVERRIDE SHIM — LANDED (fix (A), §(4.97), prior session).** Gave the arm a `Function.update`
  override selector `endsσρ₁` + the off-the-chain-edges agreement `hoff` (the M₃ `ends₃` pattern): hinge/structural slots
  against `endsσρ₁`, crux `hρGv`/`hwmem` bridged on `Gv`-links via `rigidityRows_ofNormals_congr_ends`. The §(4.100)
  step-2 re-target (this session, top inventory) re-pointed that bridge from `endsσρ → endsσρ₁` to `ends₀ → endsσρ₁`.
- [x] **THE `chainData_dispatch` INTERIOR-BRANCH HEAD-ON BUILD — RAN, BLOCKED-with-exact-residual (§(4.98)).**
  Built the full interior branch against the reshaped arm: 10/13 slots discharge sorry-free incl. `hρe₀` (the
  §(4.96) `hends_i` residual now DISCHARGED via the disjunction-relaxation below). 3 blockers, all one root: `hρGv`'s
  `hφ` (base redundancy at the RELABELLED selector — a mixed framework with NO producer), `hρe₀base`/`he₀rec`/
  `hrecBase` (the `e₀`/`Gab`-link recording the discriminator drops). Fix = (B′) discriminator exposure +
  (C) the new `hφ` relabel-transport. Detail: §(4.98).
- [x] **THE §(4.96) `hends_i` ORIENTATION RESIDUAL — DISCHARGED** (the disjunction-relaxation of the widening chain,
  this session). `baseRedundancy_perp_interior_reproduced_panel`/`interior_hρe₀_of_widening`/
  `interior_hρe₀_of_baseWidening` (`ForkedArm.lean`) now take `hends_i` as the recording DISJUNCTION
  `ends (edge i) = (vᵢ₊₁,vᵢ) ∨ (vᵢ,vᵢ₊₁)` (the conclusion `ρ₀ ⊥ panel = 0` is orientation-invariant via
  `panelSupportExtensor_swap`/`map_neg`/`neg_eq_zero`); the dispatch reads it off the discriminator's `hends'` at
  the matched chain edge (a `Gv`-link). + `Graph.splitOff_swap_ab` (`Operations.lean`, the base-split a/b-symmetry).
  Both axiom-clean, gate-green, below-contract, `d=3` untouched. The §(4.96) fix-(A) arm slots `hends_ea`/`hends_eb`/
  `hends_Gv`/`hne_Gv` also discharge clean (override + LEAF-1).
- [x] **THE `hφ` SATISFIABILITY/ROUTE SPIKE — RAN, RE-SCOPED (§(4.99)).** `hφ` is MIS-STATED, not a missing
  producer. Kernel-checked: the `congr_ends` route reduces `hφ` to the FALSE `endsσρ e = ends₀ e` on cycle edges;
  the only assembled transport `rigidityRow_chainData_relabel` lands at a three-way mismatch (twisted functional +
  `qρ` seed + split graph); the d=3 W9a precedent (`case_III_arm_realization_M3`) never uses the mixed framework.
  So §(4.98)'s "(C) build the `hφ` relabel-transport" is WRONG. Detail: §(4.99).
- [x] **THE RE-STATEMENT-ROUTE SPIKE — RAN, ROUTE SETTLED (§(4.100), this session).** NEITHER §(4.99)-named route
  closes; a THIRD route does (kernel-checked, both viable-route probes CLOSED SORRY-FREE, scratch green 2783 jobs,
  deleted, zero Lean diff). Route-1 (`shiftEndsAdv` through the fold) DEAD — incompatible with the per-step gate's
  `hends'_off` (Probe A residual FALSE). Route-2 (graph-iso) closes its first half sorry-free but lands at the SPLIT
  graph — engine forces `removeVertex vᵢ` (`hsplitG`), wrap-peel circular (Probe B1). `candidateEnds` is a GLOBAL
  relabel (Probe C residual FALSE), not sparse-reachable — the source of the mis-statement. VIABLE route (Probes
  E1+E2 sorry-free): existing fold at `ends := ends₀` lands at genuine `(G−vᵢ, ends₀, qρ)`; sparse `Function.update`
  override `endsσρ₁` (d=3 `ends₃`) bridges via `rigidityRows_ofNormals_congr_ends`. NO fold re-statement. Detail +
  signatures: §(4.100).
- [x] **(B′) RE-EXPOSE `_hρ₀Gv` + `hrec'` FROM THE DISCRIMINATOR — LANDED (§(4.100), this session).** Two
  conjunct-adds, exposing-not-proving (axiom-clean `[propext, Classical.choice, Quot.sound]`, build + lint green,
  `d=3` untouched, zero blast radius): (1) `chainData_split_w6b_gates` (`Realization.lean:889`) now RETURNS the full
  `Gab`-link recording `hrec'` (`∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u,w) ∨ (w,u)`, computed
  internally at `:979`, previously only the weaker `Gv`-only `hends'` returned) as a final conjunct — its two
  consumers (`chainData_split_realization` `:1228`, the discriminator `:2385`) get a binder; (2)
  `exists_shared_redundancy_and_matched_candidate` (`:2322`) now RETURNS both `_hρ₀Gv` (base redundancy span
  `hingeRow a b ρ₀ ∈ span R(G−v)` at the honest `ends`) + `hrec'` — it already obtained both, just dropped `_hρ₀Gv`
  at `:2385`. No live consumer of the discriminator yet, so zero downstream ripple. These are the inputs the leaf
  re-target's `hφ₀`/`hrec` slots consume.
- [x] **THE `hperp`-at-`ends₀` PERP PRODUCER `chainData_freshEdge_slot_perp_ends₀` — LANDED (§(4.101), prior session)**
  (`ChainColumn.lean:1409`, axiom-clean `[propext, Classical.choice, Quot.sound]`, build + lint green, `d=3` untouched).
  The genuinely-new piece the §(4.100) leaf re-target needs: the per-edge perp
  `ρ₀ ⊥ (ofNormals (G − vᵢ) ends₀ qρ).supportExtensor (edge s)` at the HONEST `ends₀` selector (NOT the relabel-image
  `endsσρ` the existing `chainData_freshEdge_slot_perp` lands at — the two support extensors at `edge s` coincide only up
  to sign). Reduces the `ends₀`-form panel via the recording `hrec`/`hrece₀` ((B′)'s `hrec'`) + `shiftPerm_apply_interior`
  (interior `s ≥ 1` → base support at `edge (s+1)`, base perp STEP 1 `chainData_freshEdge_perp_of_baseRedundancy`) /
  `shiftPerm_apply_vtx_off` (head `s = 0` → the `e₀` panel, base perp `hρe₀` via `hrece₀`); orientation absorbed by the
  new `private perp_panelSupportExtensor_swap` helper (the FRICTION 269–270 idiom). Reuses STEP 1 + `hρe₀` verbatim — no
  new redundancy hypothesis; the only new input is the genuine `ends₀`-selector recording. Below the C.0–C.6 contract +
  0-dof motive; no cert change.
- [x] **RE-TARGET `chainData_relabel_arm_hρGv`'s selector `candidateEnds → ends₀` (§(4.100) step 1) — LANDED (this
  session)** (`ChainColumn.lean:1519`, axiom-clean `[propext, Classical.choice, Quot.sound]`, build (2830 jobs) + lint
  green, `d=3` untouched). DROPPED the mixed `hφ`, REPLACED with the genuine
  `hφ : hingeRow (vtx 0)(vtx 2) ρ₀ ∈ span (ofNormals (G.removeVertex (vtx 1)) ends₀ q).rigidityRows` ((B′)-exposed);
  CHANGED the conclusion framework selector `endsσρ → ends₀`; restated `hrec` at the honest `ends₀` + the new `hrece₀`
  input. Body: the `chainData_freshEdge_slot_mem` (`:901`) call now passes `ends := ends₀`, making its `hφ`/conclusion
  the honest base/`ends₀` ones (Probe E1 ✓); its `hperp` slot is fed by the LANDED `chainData_freshEdge_slot_perp_ends₀`
  (NOT the existing `_perp`), bridged to the slot's fold seed by P3 `shiftSeedAdv_eq_funLeft_shiftPerm`. Dropped the
  now-unused `[DecidableEq β]`. The fold (`shiftBodyListAsc_foldl_mem_span_rigidityRows`) + `chainData_freshEdge_slot_mem`
  stay UNCHANGED (already selector-parametric). Zero blast radius (no live consumer). Below the C.0–C.6 contract +
  0-dof motive; no cert change.
- [x] **WIRE the arm's `congr_ends` override bridge `ends₀ → endsσρ₁` (§(4.100) step 2) — LANDED (prior session)**
  (`Realization.lean:1364`, axiom-clean `[propext, Classical.choice, Quot.sound]`, build (2830 jobs) + lint green, `d=3`
  untouched). RESTATED the arm's `hρGv`/`hwmem` input slots at `ends₀ qρ` (the §(4.100)-re-targeted leaf lands there
  directly, was the relabel-image `endsσρ qρ`); the override `endsσρ₁` + `hoff` (§(4.97)) now state agreement with `ends₀`
  (sparse `Function.update`, NOT `candidateEnds`). Body: dropped the relabel-image `set endsσρ`, re-pointed the existing
  `rigidityRows_ofNormals_congr_ends` step `endsσρ → endsσρ₁` ⇒ `ends₀ → endsσρ₁` (Probe E2: the two override edges LINK
  `vᵢ`, NOT `Gv`-links, so `ends₀`/`endsσρ₁` agree on every `Gv`-link), dropped the freed `[DecidableEq β]`. Engine refine
  + `case` slots UNCHANGED. Zero blast radius (no term-level consumer).
- [x] **THE §(4.102) ARM `hwmem` SELECTOR RE-STATEMENT — LANDED (prior session)** (`chainData_interior_realization_hρGv`,
  `Realization.lean:1463`, axiom-clean, build + lint green, `d=3` untouched). (1) ADDED the swap-tolerant congruence
  `rigidityRows_ofNormals_congr_ends_swap` (`:92`, ~30 lines, beside `rigidityRows_ofNormals_congr_ends`): two selectors
  recording each `G`-link UP TO ORDER ⇒ equal rigidity rows (support extensors `±`-coincide, `panelSupportExtensor_swap`
  + `-1`-unit `span_singleton`). (2) restated the arm's `hwmem` input selector `ends₀ → cd.candidateEnds i ends₀` (the
  producer's actual output — `hρGv` STAYS at `ends₀`) + added the (B′)-exposed `hrec'` arm input + re-added
  `[DecidableEq β]` (`candidateEnds` needs it). (3) the `hwmem₁` derivation bridges `candidateEnds i ends₀ → endsσρ₁` via
  the swap-congruence (LEAF-1 `candidateEnds_records_splitOff_isLink` for `candidateEnds` up-to-order, `hends_Gv` for
  `endsσρ₁` up-to-order); `hρGv₁` keeps the EXACT `hcongr`. Below the contract + motive/IH; no cert change.
- [x] **THE FULL `G`-LINK RECORDING SUPPLIER `fullLink_recording_of_splitOff_recording` — LANDED (prior session)**
  (`Relabel/Chain.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build (2830 jobs) + lint green, `d=3`
  untouched, zero blast radius). The dispatch's `hrec` supplier for the crux leaf `chainData_relabel_arm_hρGv`: that leaf
  needs `ends₀` to record EVERY `G`-link, but the discriminator only exposes the `Gab = G.splitOff (vtx 1)(vtx 0)(vtx 2)
  e₀`-link recording `hrec'` (`Gab` is a realization of the SPLIT — no edges at the removed base body `vtx 1`). The two
  missing `G`-edges are exactly the base-body chain edges `edge 0`/`edge 1` (degree-2 closure at `vtx 1`, `3 ≤ d`); the
  lemma takes `hrec'` + the two chain-edge orientations `he0`/`he1` (the dispatch supplies them via a `Function.update`
  override of the discriminator's `ends` — those two edges link `vtx 1`, so are NOT `Gv`-links and leave the arm's
  `hφ`/`hρe₀` `Gv`-rows untouched) and produces the full recording: a `G`-link either touches `vtx 1` (`edge 0`/`edge 1`,
  recorded by `he0`/`he1`) or has both endpoints surviving (so `f ≠ e₀`, a `Gab`-link recorded by `hrec'`). Generic in
  `ends₀`; no new LA, no motive/IH/contract change.
- [x] **THE DISPATCH'S INTERIOR BRANCH `chainData_dispatch_interior` — LANDED (prior session)**
  (`CaseIII/Realization.lean`, axiom-clean, gates green, `d=3` untouched). The load-bearing arm core: at a matched
  interior `i` (`2 ≤ i`, `3 ≤ cd.d`), wires `chainData_interior_realization_hρGv` to all per-slot suppliers from the
  `ends₀`-shaped discriminator data (crux `±r` ← `chainData_relabel_arm_hρGv` + `fullLink_recording_of_splitOff_
  recording`; `hρe₀` ← `interior_hρe₀_of_baseWidening`; override `endsσρ₁`; bottom `L ∘ w` ← `chainData_bottom_relabel`;
  gate ← `candidateVtx_succ_eq`). FRICTION (prior session): inline `(by omega)` in a heavy-result `exact` → named
  `have` (TACTICS-QUIRKS §43).
- [x] **THE DISPATCH'S INTERIOR `ends → ends₀` TRANSFER `chainData_dispatch_interior_of_discriminator` — LANDED (this
  session)** (`CaseIII/Realization.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, full build (2830 jobs) +
  lint green, `d=3` untouched, zero blast radius). The `ends₁` mechanical-plumbing half of the router: takes the
  base-`v₁`-split discriminator output VERBATIM (at the honest `ends`, the `Gab`-recording) and at a matched interior `i`
  produces the `G`-realization. Builds `ends₀ := Function.update³ ends` overriding `e₀ ↦ (vtx 2, vtx 0)`, `edge 0 ↦ (vtx
  0, vtx 1)`, `edge 1 ↦ (vtx 1, vtx 2)`; `fullLink_recording_of_splitOff_recording` gives the full `G`-recording
  `hrec_G`; the three override edges all link `vtx 1` (not `Gv`-links) so `hwmem'`/`hedgeGv`/`hρ₀Gv` transfer via
  `rigidityRows_ofNormals_congr_ends` (+ a per-edge `hingeRowBlock` congruence); then `chainData_dispatch_interior`. No
  new LA, no motive/IH/contract change. FRICTION: `set v₀/v₁/v₂` shadowed `w`'s type (the `w✝` proliferation,
  TACTICS-QUIRKS §43) — fixed by passing literal `cd.vtx ⟨_,_⟩`, abbreviating only `Gv`.
- [ ] **[NEXT] BUILD the `chainData_dispatch` ROUTER** (the interior transfer is now a single lemma call). Fire the
  discriminator `exists_shared_redundancy_and_matched_candidate` ONCE at the base `v₁`-split `(v,a,b) = (vtx 1, vtx 0,
  vtx 2)` (derive `h622lb` from `case_III_nested_rank_lower_all_k`; take `hdef_Gab`/`hsplitGP` as hypotheses — the
  `hdispatch` shape the ASSEMBLY/CHAIN-5 supplies, NOT the dispatch's to derive); `by_cases` on `(i : ℕ)`: interior
  `2 ≤ i` → `chainData_dispatch_interior_of_discriminator` (this session — DONE, just feed it the discriminator output);
  `i ≤ 1` base-candidate + the `d=3` floor → `chainData_split_realization` (`:1227`, its `htrans` from the same
  discriminator; the `(vtx 1, vtx 0, vtx 2)`-base vs `(vtx 1, vtx 2, vtx 0)`-candidate `a/b`-swap reconciled by
  `splitOff_swap_ab`). Lands with the approved C.3 `hIH` add. THEN discard the `_aug` fork. **The genuine remaining
  work: the discriminator-firing slots (`h622lb`/`hdef_Gab`/`hsplitGP` wiring) + the `i ≤ 1`/`i = 0` base-panel routing
  + the floor a/b-swap reconcile.**
- [x] **(D-substitution) S1–S5 + spine + 5c/5e/5f.hA/5f.hAeq — LANDED but DEAD/CONDITIONAL** (the corner `hA` hyp
  is unsatisfiable for the collapsed candidate; row 598 + §(4.91)). Detail: *Current state* + design
  §(4.84)–(4.90) + git. The make-or-break spikes (§(4.85)–(4.89)) all returned GO by ABSTRACTING the corner gate
  as a free hypothesis; the dispatch (sourcing it) found it unsatisfiable. The GO-cascade lesson is in *Promoted
  to* below. → discard/retire at the re-architecture or phase-close.
- [x] **A1–A5c backbones + D1 `interior_hsplitGP` + the route-refutation LA cores** — LANDED, REUSED/dead-but-
  correct. `_matrix`/`_rowOp`/chain dead arms + the (D-substitution) conditional bricks + the `C≠0` orphan
  5f.hAeq → αE6 retirement DEFERRED to phase-close (or the override-route landing).

## Blockers / open questions

- **THE LIVE BLOCKER: BUILD the `chainData_dispatch` ROUTER.** Both arms are now LANDED: the interior
  `2 ≤ i` arm is the one-call `chainData_dispatch_interior_of_discriminator` (this session — it takes the discriminator
  output directly and does the `ends → ends₀` override + transfer + interior wiring), and the `i ≤ 1`/`d=3`-floor arm is
  `chainData_split_realization`. What remains is the ROUTER: fire `exists_shared_redundancy_and_matched_candidate` ONCE
  at the base `v₁`-split (deriving `h622lb` from `case_III_nested_rank_lower_all_k`; taking `hdef_Gab`/`hsplitGP` as
  hypotheses — the `hdispatch` shape), `by_cases` on `(i : ℕ)` and route. **The genuine remaining work:** the
  discriminator-firing slot wiring (`h622lb`/`hdef_Gab`/`hsplitGP`), the `i ≤ 1`/`i = 0` base-panel routing, and the
  `chainData_split_realization` floor's `htrans`-from-discriminator + the `(vtx 1, vtx 0, vtx 2)`-base vs
  `(vtx 1, vtx 2, vtx 0)`-candidate `a/b`-swap reconcile (`splitOff_swap_ab`). Lands with the approved C.3 `hIH` add.
  Below the frozen contract + motive/IH (no cert change). Detail: the [NEXT] checklist entry.
- **THE CRUX LEAF'S `hrec`-OVER-`G`-LINKS GAP — SETTLED + LANDED (prior session).** `chainData_relabel_arm_hρGv` needs
  `ends₀` to record EVERY `G`-link, but the discriminator only exposes the `Gab`-link recording `hrec'` (Gab has no edges
  at the removed base body `vtx 1`). The two missing edges are the base-body chain edges `edge 0`/`edge 1`; the new
  supplier `fullLink_recording_of_splitOff_recording` takes `hrec'` + their dispatch-supplied orientations and produces
  the full recording (degree-2 closure at `vtx 1`). The override edges are NOT `Gv`-links, so the arm's `hφ`/`hρe₀`
  `Gv`-rows are untouched. See *Decisions made* + the checklist entry.
- **THE §(4.102) BOTTOM-RELABEL RECONCILE — SETTLED + LANDED (prior session).** `chainData_bottom_relabel`
  (`Chain.lean:353`) is pinned to the relabel-image `candidateEnds i ends₀` by its `hsupp` (NOT re-targetable to `ends₀`;
  the d=3 free-override `ends₃` works only because the swap is an involution). FIX (landed): the arm states `hwmem` at
  `candidateEnds i ends₀` (what the producer gives) and bridges to the engine override `endsσρ₁` via the new
  swap-tolerant congruence `rigidityRows_ofNormals_congr_ends_swap` (LEAF-1 + `hends_Gv`, both up-to-order); `hρGv` STAYS
  at `ends₀`. See *Decisions made* + §(4.102).
- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user, session #36, 2026-06-26; lands with the dispatch
  build). The interior arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH`
  via `splitOff_isMinimalKDof` — D1 `interior_hsplitGP` ✓ LANDED. A one-bundle add to the C.0
  producer/consumer/ENTRY lockstep trio (concrete ripple surface §(4.88.4)), NOT a motive/IH-strength change.
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert; tracked
  separately, lands with the dispatch.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape (the `cd : G.ChainData n` producer — it
  returns only the `d=3` 4-tuple today; `Induction/ForestSurgery/Reduction.lean:383`) + the CHAIN-5 C.0-trio
  reshape + the floor lift + OD-1, then ASSEMBLY. Design-pinned to 23g (§C.2/§C.5). The frozen contract
  (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**THE ROUTE (§(4.100), settled — full dead-end blow-by-blow in design §(4.100)):** the §(4.99) mis-statement fix is a
SELECTOR re-target, NOT a fold re-statement. The leaf targets the HONEST base selector `ends₀` (NOT the global
relabel-image `candidateEnds`, unreachable by the fold's per-step gate, the source of the mis-statement); the engine
framework's sparse `Function.update` override `endsσρ₁` (d=3 `ends₃` pattern) bridges to `ends₀` via
`rigidityRows_ofNormals_congr_ends` (the override's two chain-hinge edges link the removed `vᵢ`, so are NOT
`removeVertex vᵢ`-links — `congr_ends` only quantifies over links). The existing fold at `ends := ends₀` lands at the
genuine `(removeVertex vᵢ, ends₀, qρ)` (its W9a `±r` telescope absorbs the wrap); `chainData_freshEdge_slot_mem`/
`shiftBodyListAsc_foldl_mem_span_rigidityRows` UNCHANGED (already selector-parametric). Step 1 (leaf re-target) + step 2
(the arm `congr_ends` bridge) ✓ BOTH LANDED; the live blocker is now the dispatch. The §(4.98) head-on build (10/13
slots) + the landed infra SURVIVE.

**THIS SESSION LANDED the dispatch's interior `ends → ends₀` transfer
`PanelHingeFramework.chainData_dispatch_interior_of_discriminator`** (`CaseIII/Realization.lean`), axiom-clean
`[propext, Classical.choice, Quot.sound]`, full build (2830 jobs) + lint green, `d=3` untouched, zero blast radius (no
live consumer — the router is not yet wired). It is the `ends₁` mechanical-plumbing half of the router: it takes the
base-`v₁`-split discriminator output VERBATIM (at the honest `ends`, the `Gab`-recording) and at a matched interior `i`
(`2 ≤ i`, `3 ≤ cd.d`) builds the `ends₀` full-`G`-recording override (three `Function.update`s, `e₀`/`edge 0`/`edge 1`),
transfers the discriminator's `Gv`-stated facts via `rigidityRows_ofNormals_congr_ends` (+ per-edge `hingeRowBlock`
congruence for `hedgeGv`), and calls the landed `chainData_dispatch_interior`. So the interior arm is now ONE lemma
call off the discriminator output (see *Current state* for the per-slot map).

**FIRST ACTION NEXT SESSION: BUILD the `chainData_dispatch` ROUTER** (both arms are now single lemma calls: interior
`2 ≤ i` → `chainData_dispatch_interior_of_discriminator` (this session); `i ≤ 1`/`d=3` floor →
`chainData_split_realization`). Steps:

0–5. **✓ ALL LANDED** (the per-slot suppliers + the interior assembly + the interior transfer — detail in design
   §(4.100)–(4.104) + *Decisions made* + git): the `ends₀`-perp producer `chainData_freshEdge_slot_perp_ends₀`; the leaf
   `chainData_relabel_arm_hρGv → ends₀`; the arm `chainData_interior_realization_hρGv`; the §(4.102) `hwmem` re-statement
   + `rigidityRows_ofNormals_congr_ends_swap`; (B′)'s discriminator re-exposure of `_hρ₀Gv`/`hrec'`; the crux leaf's
   `hrec` supplier `fullLink_recording_of_splitOff_recording`; the interior branch `chainData_dispatch_interior`; and
   **the interior `ends → ends₀` transfer `chainData_dispatch_interior_of_discriminator` (this session)** feeding it.
6. **[NEXT] BUILD the ROUTER `chainData_dispatch`:** fire `exists_shared_redundancy_and_matched_candidate` ONCE at the
   base `v₁`-split (derive `h622lb` from `case_III_nested_rank_lower_all_k`; take `hdef_Gab`/`hsplitGP` as hypotheses —
   the `hdispatch` shape); `by_cases` on `(i : ℕ)`: interior `2 ≤ i` → `chainData_dispatch_interior_of_discriminator`
   (this session — just feed it the discriminator output, the `ends → ends₀` work is DONE), `i ≤ 1` base-candidate + the
   `d=3` floor → `chainData_split_realization` (`:1227`, its `htrans` from the same discriminator; the
   `(vtx 1, vtx 0, vtx 2)`-base vs `(vtx 1, vtx 2, vtx 0)`-candidate `a/b`-swap reconciled by `splitOff_swap_ab`). Lands
   with the approved C.3 `hIH` add. The genuine remaining work: the discriminator-firing slots + the `i ≤ 1`/`i = 0`
   routing + the floor a/b-swap reconcile.
6. **DISCARDS at the reshape** (complete lemmas, no `sorry`s — retire once the dispatch lands): the entire
   `_aug`/`rigidityMatrixEdgeAug` interior fork (`case_III_rank_certification_aug{,_ofNormals}`/`_matrix{,_sep}`/
   `_zero₁₂`/`_chain`, `case_III_arm_realization_aug_ofNormals`, `hingeRow_mem_ofNormals_rigidityRows_chainEdge`),
   the `caseIIICandidate` override + the (D-subst) `_ofNormals` siblings, AND the now-superseded interior
   wrappers `chainData_arm_realization_sep` (`Realization.lean`)/the `_zero₁₂` `D-CAN-3b` wrapper. Multi-commit,
   likely-multi-session. `d=3` stays green on the SAME honest engine via the `k=2` spine (untouched).

**SURVIVING infrastructure (read at `def`/`theorem` §(4.94)/(4.95)):** the honest engine `case_III_rank_
certification` (general-`k`!) + `case_III_arm_realization`/`_M2`; `chainData_split_realization` (base + the
interior template); the LANDED crux leaf `chainData_relabel_arm_hρGv` (`ChainColumn.lean:1519`, now at `ends₀`); the discriminator
`exists_shared_redundancy_and_matched_candidate` (matched `i` + gate + `hedgeGv` widening); `interior_hρe₀_of_
widening` (the `hρe₀` slot); the union-count `case_III_claim612_gen`. **DISCARDED under reshape:** the entire
`_aug`/`rigidityMatrixEdgeAug` interior fork.

Authoritative scoping: `notes/Phase23-design.md` §(4.95) (the crux-leaf-is-landed GO), §(4.94) (the `d=3`
mechanism + the divergence + the reshape), §(4.93) (the cert-interface obstruction), §(4.92) (the route-(a)
corner core), §(4.91)/(4.90) (the refuted override / (D-subst) arms).

## Decisions made during this phase

### The reshape ASSEMBLY (the honest interior arm + its LEAF-1 supplier; kept, the live route)
- **The dispatch's interior `ends → ends₀` transfer `chainData_dispatch_interior_of_discriminator` (this session)** —
  (`CaseIII/Realization.lean`, after `chainData_dispatch_interior`) the `ends₁` mechanical-plumbing half of the router:
  takes the base-`v₁`-split discriminator output VERBATIM (at the honest `ends`, the `Gab`-recording) + a matched
  interior `i` (`2 ≤ i`) → the `G`-realization. Builds `ends₀ := Function.update³ ends` (`e₀ ↦ (vtx 2, vtx 0)`,
  `edge 0 ↦ (vtx 0, vtx 1)`, `edge 1 ↦ (vtx 1, vtx 2)`); `fullLink_recording_of_splitOff_recording` → full `G`-recording;
  the three override edges all link the base body `vtx 1` (not `Gv`-links), so `hwmem'`/`hedgeGv`/`hρ₀Gv` transfer to
  `ends₀` via `rigidityRows_ofNormals_congr_ends` (+ a per-edge `hingeRowBlock` congruence for `hedgeGv`), and `hρ₀e₀`/
  `hLI`/`hgate` are selector-free; then `chainData_dispatch_interior`. Decision: takes the discriminator output as
  HYPOTHESES (the router fires it), so the interior arm is now ONE call off the discriminator. Axiom-clean, gates green,
  `d=3` untouched, zero blast radius; no new LA, no motive/IH/contract change. FRICTION: `set v₀/v₁/v₂` shadows `w`'s
  type (`w✝` proliferation, TACTICS-QUIRKS §43) — fixed by literal `cd.vtx ⟨_,_⟩`, abbreviating only `Gv`.
- **The dispatch's interior branch `chainData_dispatch_interior` (prior session)** — (`CaseIII/Realization.lean`) the
  load-bearing arm core consumed by the transfer above: at a matched interior `i` (`2 ≤ i`, `3 ≤ cd.d`), with the
  `ends₀`-shaped discriminator data as hypotheses, it wires `chainData_interior_realization_hρGv` to every per-slot
  supplier (crux `±r` ← `chainData_relabel_arm_hρGv` + `fullLink_recording_of_splitOff_recording` + the `hedgeGv`
  widening + (B′) `hρ₀Gv`; `hρe₀` ← `interior_hρe₀_of_baseWidening`; override `endsσρ₁`; bottom `L ∘ w` ←
  `chainData_bottom_relabel` + the `(v₀,v₂)→(v₂,v₀)` `ρ'→-ρ'` flip; gate ← `candidateVtx_succ_eq`). Axiom-clean, gates
  green, `d=3` untouched. FRICTION (prior): inline `(by omega)` in a heavy-result `exact` → named `have`
  (TACTICS-QUIRKS §43). Full per-slot detail: design §(4.103) + git.
- **The full `G`-link recording supplier `fullLink_recording_of_splitOff_recording` (prior session)** —
  (`Relabel/Chain.lean`, beside `candidateEnds_records_splitOff_isLink`) the dispatch's `hrec` supplier for the crux leaf
  `chainData_relabel_arm_hρGv`, closing its last per-slot gap: the leaf wants `ends₀` to record EVERY `G`-link, but the
  discriminator only exposes the `Gab`-link recording `hrec'` (`Gab` has no edges at the removed base body `vtx 1`). The
  two missing `G`-edges are exactly `vtx 1`'s degree-2 chain edges `edge 0`/`edge 1`; the supplier takes `hrec'` + their
  orientations `he0`/`he1` (dispatch-supplied by a `Function.update` override — those edges link `vtx 1`, so are NOT
  `Gv`-links and leave the arm's `hφ`/`hρe₀` `Gv`-rows untouched) and produces the full recording via the degree-2
  closure at `vtx 1`. Generic in `ends₀`; axiom-clean, gates green, `d=3` untouched, zero blast radius; no new LA, no
  motive/IH/contract change.
- **The §(4.102) `hwmem` selector re-statement + swap-tolerant congruence (prior session)** —
  (`chainData_interior_realization_hρGv`, `Realization.lean:1463`) the §(4.100)-step-2 commit OVER-REACHED by stating the
  bottom `hwmem` slot at `ends₀`, but `chainData_bottom_relabel` is pinned to the relabel-image `candidateEnds i ends₀`
  by its transport's `hsupp` (NOT re-targetable; the d=3 free-override `ends₃` works only because the swap is an
  involution). FIX: added `rigidityRows_ofNormals_congr_ends_swap` (`:92`, ~30 lines — two selectors recording each
  `G`-link UP TO ORDER ⇒ equal rigidity rows, support extensors `±`-coincide via `panelSupportExtensor_swap` + a `-1`-unit
  `span_singleton`); restated `hwmem` at `candidateEnds i ends₀` (the producer's output) + added the `hrec'` arm input +
  re-added `[DecidableEq β]`; the `hwmem₁` derivation bridges `candidateEnds i ends₀ → endsσρ₁` via the swap-congruence
  (LEAF-1 `candidateEnds_records_splitOff_isLink` + `hrec'` for `candidateEnds`; `hends_Gv` for `endsσρ₁`). `hρGv` STAYS
  at `ends₀` (EXACT `hcongr`). Axiom-clean, build + lint green, `d=3` untouched; zero blast radius. No cert change.
- **The §(4.100) step-2 arm `congr_ends` bridge `chainData_interior_realization_hρGv → ends₀` (prior session)** —
  (`Realization.lean`) the arm consumes the step-1 `ends₀`-re-targeted leaf via the EXACT `rigidityRows_ofNormals_congr_
  ends` on `Gv`-links (override `endsσρ₁` + `hoff` agree with `ends₀` off the two chain hinges, Probe E2). Superseded on
  the `hwmem` slot by §(4.102) above (the bottom producer lands at `candidateEnds`, not `ends₀`); `hρGv` still uses it.
- **The §(4.100) leaf re-target `chainData_relabel_arm_hρGv → ends₀` (prior session)** — (`ChainColumn.lean:1519`) the
  step-1 fix of the §(4.99) mis-statement: the leaf's `hρGv` slot now lands at `span (ofNormals (G−vᵢ) ends₀ qρ)` at
  the HONEST base selector, NOT the global relabel-image `endsσρ`(=`candidateEnds`, no producer). DROPPED the mixed `hφ`,
  REPLACED with the genuine base redundancy at `ends₀` ((B′)-exposed); conclusion selector `endsσρ → ends₀`;
  `hrec`/`hrece₀` honest. Body = `chainData_freshEdge_slot_mem` at `ends := ends₀` (Probe E1, the selector-parametric
  slot core UNCHANGED) + the `ends₀`-perp producer for `hperp` (bridged by P3). Dropped the now-unused `[DecidableEq β]`.
  Axiom-clean, build + lint green, `d=3` untouched; zero blast radius (no live consumer). Below the contract + motive/IH;
  no cert change.
- **`chainData_freshEdge_slot_perp_ends₀` — the `hperp`-at-`ends₀` perp producer (§(4.101), prior session)** —
  (`ChainColumn.lean:1406`) the `ends₀`-selector per-edge perp the leaf re-target's `hperp` consumes (the existing
  `_perp` lands at the relabel-image `endsσρ` — coincides only up to sign). Reduces the `ends₀`-form panel via the
  recording `hrec`/`hrece₀` + `shiftPerm_apply_interior`/`_vtx_off` to `±` the base panel (interior → STEP 1; head
  `s=0` → the `e₀` panel `hρe₀`); orientation via `perp_panelSupportExtensor_swap` (FRICTION 269–270). No cert change.
- **(B′) the discriminator re-exposes `_hρ₀Gv` + `hrec'` (§(4.100), prior session)** — `chainData_split_w6b_gates`
  RETURNS `hrec'` (full `Gab`-link recording incl. `e₀`), and `exists_shared_redundancy_and_matched_candidate`
  RETURNS both `_hρ₀Gv` (base redundancy span `hingeRow a b ρ₀ ∈ span R(G−v)` at the honest `ends`) + `hrec'` (it
  already obtained both, dropped `_hρ₀Gv`). Two conjunct-adds, exposing-not-proving; consumers updated
  (`chainData_split_realization`, the discriminator); zero blast radius. Axiom-clean, build + lint green, `d=3`
  untouched. The leaf re-target's `hφ₀`/`hrec`/`hrece₀` inputs are now surfaced (the perp producer above consumes them).
- **The re-statement-route spike → SELECTOR re-target, not a fold re-statement (§(4.100), this session)** — SETTLED
  §(4.99)'s "thread-selector / graph-iso" choice: NEITHER named route closes; a THIRD does (kernel-checked, Probes
  E1+E2 sorry-free). ROOT: the leaf targets the GLOBAL relabel `candidateEnds`, unreachable by the fold's per-step
  gate (which permits only sparse 2-edge selector changes). FIX (not a fold re-statement): the existing fold at
  `ends := ends₀` lands at genuine `(G−vᵢ, ends₀, qρ)`; the SPARSE override `endsσρ₁` (d=3 `ends₃`) bridges via
  `rigidityRows_ofNormals_congr_ends` (the override's chain-hinge edges link the removed `vᵢ`, so aren't `G−vᵢ`-links).
  Route-1 (`shiftEndsAdv`) DEAD (incompatible with `seedAdvance_wstep_hstep`'s `hends'_off`); Route-2 (graph-iso) lands
  at the SPLIT graph (engine forces `removeVertex`). Below contract + motive/IH, no cert change. Detail: §(4.100).
- **The `hφ` satisfiability spike → `chainData_relabel_arm_hρGv` is MIS-STATED (§(4.99), this session)** — RE-SCOPED
  the §(4.98) blocker. Kernel-checked (read-only, scratch deleted): the leaf's `hφ` slot (base redundancy at the
  mixed `(G−v₁, RELABELLED selector `endsσρ`, base seed `q`)` framework) is NOT satisfiable — the `congr_ends` route
  reduces to the FALSE `endsσρ e = ends₀ e` on cycle edges; the only assembled transport `rigidityRow_chainData_
  relabel` lands at a three-way mismatch (twisted functional + `qρ` seed + split graph); the d=3 W9a precedent never
  uses the mixed framework. So §(4.98)'s "(C) build the `hφ` relabel-transport producer" is WRONG (no such producer).
  FIX = RE-STATE the leaf + its fold (`chainData_freshEdge_slot_mem`/`shiftBodyListAsc_foldl_mem_span_rigidityRows`)
  to take the genuine `_hρ₀Gv` at `ends₀`, threading `q→qρ` with the selector (d=3 W9a lifted to the cycle). (B′)
  STANDS. FLAG-DON'T-FORCE; below the frozen contract + motive/IH. Detail: §(4.99).
- **The `hends_i` disjunction-relaxation + `splitOff_swap_ab` (§(4.98), prior session)** — discharged the §(4.96)
  `hends_i` orientation residual: `baseRedundancy_perp_interior_reproduced_panel`/`interior_hρe₀_of_widening`/
  `interior_hρe₀_of_baseWidening` (`ForkedArm.lean`) now take `hends_i` as the recording DISJUNCTION (the conclusion
  `ρ₀ ⊥ panel = 0` is orientation-invariant; the swapped branch flips a sign `panelSupportExtensor_swap`/`map_neg`
  absorb). `Graph.splitOff_swap_ab` (`Operations.lean`) = the base-split a/b-symmetry graph equality. Both
  axiom-clean, gate-green, below-contract, `d=3` untouched. The head-on dispatch build (§(4.98)) is BLOCKED on the
  remaining `hφ` mixed-framework transport (C) + the discriminator exposure (B′).
- **Orientation-override shim (§(4.96) fix (A), §(4.97), prior session)** — gave the arm the `Function.update` override
  selector `endsσρ₁` + the `hoff` off-the-chain-edges agreement (the M₃ `ends₀`/`ends₃` split), with the
  `rigidityRows_ofNormals_congr_ends` bridge on `Gv`-links. Superseded-into by the §(4.100) step-2 re-target (top entry):
  the bridge now runs `ends₀ → endsσρ₁`.
- **LEAF-1 `candidateEnds_records_splitOff_isLink`** (`Relabel/Chain.lean:312`) — the three interior-arm
  selector slots `hends_ea`/`hends_eb`/`hends_Gv` unified into one generic recording: `candidateEnds i ends₀`
  records every candidate-`i`-split link when `ends₀` records every `v₁`-base-split link (`1 < i`). Proof =
  `splitOff_isLink_shiftRelabel_iff` `.mp` + recording + `Equiv.symm_apply_apply`. No `d=3` content, no new LA.

### The six route refutations (verdicts only; full blow-by-blow in design §§(4.77)–(4.83) + git)
- **routes (b)/(α) DEAD** (§(4.77)): the corner 3-normal-LI `_escape` side-condition `∃ i, p i ⬝ᵥ q b ≠ 0` is
  provably false for reachable matched joins.
- **route (D) DEAD** (§(4.80)): the `_aug` ladder on the D-canonical pin-zero bottom fires the corner `hA` but
  `hr` re-hits the §(4.73.2) seam (the discriminator's `hedgeGv` yields the chain-edge panel `(i+1,i)`, never the
  short-circuit `(i+1,i−1)`).
- **route (γ) DEAD** (§(4.81)): the short-circuit perp needs a degree-2 coplanarity false for the generic seed.
- **route (β) DEAD as a finish line** (§(4.82)): Q1 (union-dimension) LANDED general-`k`, but (β) only re-selects
  `i`; the false `hr` is in the override, downstream of selection. *[The §(4.90) recon disputes the "false `hr`"
  framing — claims it examined an arbitrary `q`, not the discriminator-co-chosen seed; UNRESOLVED, the decisive
  spike settles it.]*
- **narrow chain-edge-re-key DEAD** (§(4.83)): re-keying the reproduced slot fixes `hr` but un-matches the bottom
  (the chain-edge second normal is the deleted `v ∉ V(Gab)`). *[Same §(4.90) dispute.]*

### (D-substitution) arc → OFF-BY-ONE corner; superseded by §(4.90) (verdicts; detail in design §(4.84)–(4.90) + git)
- The session built the (D-substitution) re-architecture (genuine `ofNormals` candidate, no override): S1–S5 +
  the spine all LANDED axiom-clean, with five make-or-break spikes (§(4.85)–(4.89)) each returning GO. But the
  final `chainData_dispatch` build (row 598) found the corner `hA` UNSATISFIABLE: the corner gate
  `ρ₀(C(e_a)) ≠ 0` is the exact negation of the S1 `hr` chain-edge perp `ρ₀(C(e_a)) = 0` (same `ρ₀`, same panel),
  so the corner is rank `D−1` (off-by-one). Root: the genuine candidate collapsed the free-panel + the redundant
  `±r` onto ONE chain edge — the §§(4.77)–(4.83) root re-surfacing. **§(4.90):** KT's `+1` (and the override)
  keep them on TWO separate edges; the (D-substitution) detour was the wrong fix.
- **The GO-cascade lesson** (the durable one, → *Promoted to*): five spikes each ABSTRACTED the corner gate as a
  free hypothesis and returned GO; none traced it to its source (the discriminator). The dispatch (the first to
  source it) found it unsatisfiable — the deferred-hypothesis-unsatisfiable trap at the ARCHITECTURE level.

### (D-canonical) — the LANDED bottom machinery (kept; reusable under either arm; design §(4.71)/(4.72))
- `canonBlockBasis`/`canonBlock` + `_congr` re-keyed `blockBasisOn` on the support extensor, making the
  cross-framework basis equality PROVABLE → the literal `R(Gab)`-bottom bridge `submatrix_columnOp_toBlocks₂₂_eq_
  Gab` (`Concrete.lean:2387`). D1 `interior_hsplitGP` (`Realization.lean:758`) = the IH full-rank `R(Gab)` (the
  `Q` source), consuming the C.3 `hIH` add. LANDED, REUSED.

### Promoted to FRICTION / TACTICS-QUIRKS / DESIGN
- **The GO-cascade deferred-hypothesis-unsatisfiable trap** (a deferred GATE/side-condition carried through
  MULTIPLE GO spikes, each abstracting it, must be traced to its SOURCE/producer — not type-checked at each
  consumer; a cascade of GO spikes all deferring the same crux hypothesis is a red flag). → DESIGN.md
  *Constructibility recon* + the coordinate-phase command (this session, 2026-06-28).
- **route-composition satisfiability must be COMPILER-CHECKED, not prose-argued** (the §(4.62) lesson; the
  §(4.90) reversal is the latest instance — a prose re-route reversing a refutation needs a spike). → FRICTION;
  DESIGN.md *Constructibility recon*.
- **`set`-folding a carried hypothesis's heavy type breaks `exact`/whnf** → TACTICS-QUIRKS §43. **`ℤ→ℕ`
  cast-subtraction** → TACTICS-QUIRKS §47. **A projecting argument-lambda fed to an implicit-domain parameter
  needs a binder type ascription** → FRICTION *[idiom] Feeding …'s `cols`*. **Case-split an *applied* `Equiv`:
  `cases h : f x`** → FRICTION. **Two defeq-but-not-syntactic `Matrix.of` lambdas: `rw [show … from h.symm]`
  with the explicit `Matrix.of` ascription** → FRICTION (the route-(D) `_aug` defeq-bridge family).
