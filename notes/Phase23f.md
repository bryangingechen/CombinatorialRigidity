# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **THE HONEST INTERIOR ARM + ITS LEAF-1 SUPPLIER ARE LANDED; the §(4.96)
INTERIOR-BRANCH SATISFIABILITY SPIKE found the live blocker = a SELECTOR-ORIENTATION INTERFACE GAP in
the interior arm (NOT row-598, NOT §(4.91)). Next step = add the orientation-override shim (M₃ `ends₃`
pattern), THEN the `chainData_dispatch` router. See §(4.96) + *Hand-off*.**
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

**THE RESHAPE (§(4.94)/(4.95)) — THE INTERIOR ARM IS LANDED.** The honest engine
`case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine, ALREADY general-`k`) sources
`±r` via the eq.-(6.27) ROW-OP `hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ` (genuine present-body `e_b`-row
− BOTTOM `G−v`-row `hρGv`), decoupling the gate from the membership. The interior `hρGv` row membership is the
LANDED crux leaf `chainData_relabel_arm_hρGv` (`ChainColumn.lean:1390`). **This session BUILT the honest interior
arm `chainData_interior_realization_hρGv` (`Realization.lean:1322`, axiom-clean, warning-clean):**
`case_III_arm_realization` re-indexed at the interior split tuple, candidate functional `−ρ₀`, at the
candidate-relabelled framework `ofNormals (G − vᵢ) endsσρ qρ` (`endsσρ` the `(shiftPerm i.castSucc).symm`-shifted
`ends₀`, `qρ = q ∘ shiftPerm i.castSucc`). The gate slots `hLn`/`hgab`/`hρgate`/`hρe₀` reduce through the landed
seed reads `seedShift_succ_/pred_castSucc` (the engine `b`-role reads at the SPLIT BODY, so `hgab`'s pair is
`(a,v)`, the cycle analogue of `M₃`'s `hqρv`); `hρGv` is the crux leaf defeq-exact; `hρe₀` from
`interior_hρe₀_of_widening` with the `−ρ₀` flip. **The build CONFIRMED the real satisfiability test:** the bottom
family `w`/`hwmem` (the `chainData_bottom_relabel` disjunction shape) + the relabelled-`endsσρ` structural slots
fill the honest engine defeq-clean for the interior. The relabel-framework structural facts
(`hends_ea`/`hends_eb`/`hends_Gv`/`hne_Gv`) are taken as hypotheses the dispatch supplies — and **this session
landed their LEAF-1 supplier** `candidateEnds_records_splitOff_isLink` (`Relabel/Chain.lean:312`): the three
selector slots `hends_ea`/`hends_eb`/`hends_Gv` all reduce to "every candidate-split link is recorded by
`cd.candidateEnds i ends₀`", which this lemma proves generically in `ends₀` via `splitOff_isLink_shiftRelabel_iff`
(`hne_Gv` is the remaining slot, off general position). NEXT = the rest of the `chainData_dispatch` router
wiring. See *Hand-off* + §(4.94)/(4.95).

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched):**
- **THE LANDED LEAF-1 SELECTOR-RECORDING SUPPLIER (this session):** `candidateEnds_records_splitOff_isLink`
  (`Relabel/Chain.lean:312`) — IF `ends₀` records every `v₁`-base-split link THEN `cd.candidateEnds i ends₀`
  records every candidate-`i`-split link (`1 < i`); the unified supplier for the interior arm's three selector
  slots `hends_ea`/`hends_eb`/`hends_Gv`. Generic in `ends₀`; proof = `splitOff_isLink_shiftRelabel_iff` `.mp` +
  recording + `Equiv.symm_apply_apply`.
- **THE LANDED HONEST INTERIOR ARM (prior session):** `chainData_interior_realization_hρGv`
  (`Realization.lean:1322`) — the all-`i` generalization of `case_III_arm_realization_M3` (its `i=2` single-swap
  instance), routing the interior matched candidate through the honest engine. Takes the shared-base bundle
  (gate / `hρe₀` / `hρGv` / bottom `w`/`hwmem`) + the `endsσρ` structural facts as hypotheses the dispatch fills.
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

**THE PATH IS FOUND (§(4.95)): the crux leaf is LANDED; the reshape is pure ASSEMBLY. Next = build the honest
interior arm + the `chainData_dispatch` router — see *Hand-off*.**

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
- [x] **THE RESHAPE BUILD — the honest interior arm `chainData_interior_realization_hρGv` — LANDED**
  (`Realization.lean:1322`, axiom-clean `[propext, Classical.choice, Quot.sound]`, warning-clean). §(4.94)
  Part 4: `case_III_arm_realization` (the honest general-`k` engine) re-indexed at the interior split tuple
  `(v,a,b,e_a,e_b) = (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc, edge i, edge (i−1))`, candidate functional
  `ρ̃ = −ρ₀`, at the candidate-relabelled framework `ofNormals (G − vᵢ) endsσρ qρ`. The gate slots
  `hLn`/`hgab`/`hρgate`/`hρe₀` reduce through the landed seed reads `seedShift_succ_/pred_castSucc`
  (the engine `b`-role reads at the SPLIT BODY `q(vtx i.castSucc,·)` — the cycle analogue of `M₃`'s `hqρv`,
  so `hgab`'s pair is `(a,v)` not `(a,b)`), the `hρGv` slot is the landed crux leaf `chainData_relabel_arm_hρGv`
  (defeq-exact), `hρe₀` from `interior_hρe₀_of_widening` (defeq, with the `−ρ₀` flip). **The build CONFIRMED the
  real satisfiability test:** the relabelled-`endsσρ` structural slots + the per-member relabelled bottom family
  `w`/`hwmem` (the `chainData_bottom_relabel` disjunction shape) fill the honest engine for the interior — all
  defeq-clean. The relabel-framework structural facts (`hends_ea`/`hends_eb`/`hends_Gv`/`hne_Gv`) are taken as
  hypotheses the dispatch supplies (the `M₃`-`hne_Gva`/`hends₃_*` pattern), `hwcard` is the `screwDim k ·
  (V(G).ncard − 2)` count. Structural is the all-`i` generalization of `case_III_arm_realization_M3` (its `i=2`
  single-swap instance).
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
- [ ] **[NEXT] THE ORIENTATION-OVERRIDE SHIM, THEN the `chainData_dispatch` ROUTER (the live next step, fix (A)).**
  Reshape `chainData_interior_realization_hρGv` to take a `Function.update` override selector `endsσρ₁` (the M₃
  `ends₃` pattern, `Realization.lean:528`) decoupling the raw-`ends₀` bottom role from the orientation-forced hinge
  role — `hends_ea`/`hends_eb` then `rfl`, the `hρGv`/`hwmem`/`hρe₀` congruences via `rigidityRows_ofNormals_congr_
  ends` (`Realization.lean:1282`). THEN build the router: case-split matched `idsc` on `(i:ℕ)`, base/floor via
  `chainData_split_realization`, interior `2 ≤ idsc` via the reshaped arm (gate via `candidateVtx_succ_eq`, `hρe₀`
  via `interior_hρe₀_of_baseWidening` + a `hingeRow_swap`/index-form bridge, `hρGv` via `chainData_relabel_arm_hρGv`,
  `L ∘ w`/`hwmem` via `chainData_bottom_relabel`, `hends_Gv`/`hne_Gv` via LEAF-1 + GP). Lands with the approved C.3
  `hIH` add. The §(4.96) probe confirmed everything EXCEPT the orientation slots is already satisfiable. Then discards
  the `_aug` fork + the override/(D-subst) siblings. See *Hand-off* leaf 1-3.
- [x] **(D-substitution) S1–S5 + spine + 5c/5e/5f.hA/5f.hAeq — LANDED but DEAD/CONDITIONAL** (the corner `hA` hyp
  is unsatisfiable for the collapsed candidate; row 598 + §(4.91)). Detail: *Current state* + design
  §(4.84)–(4.90) + git. The make-or-break spikes (§(4.85)–(4.89)) all returned GO by ABSTRACTING the corner gate
  as a free hypothesis; the dispatch (sourcing it) found it unsatisfiable. The GO-cascade lesson is in *Promoted
  to* below. → discard/retire at the re-architecture or phase-close.
- [x] **A1–A5c backbones + D1 `interior_hsplitGP` + the route-refutation LA cores** — LANDED, REUSED/dead-but-
  correct. `_matrix`/`_rowOp`/chain dead arms + the (D-substitution) conditional bricks + the `C≠0` orphan
  5f.hAeq → αE6 retirement DEFERRED to phase-close (or the override-route landing).

## Blockers / open questions

- **THE INTERIOR-BRANCH SATISFIABILITY SPIKE (§(4.96)) FOUND THE LIVE BLOCKER: a SELECTOR-ORIENTATION INTERFACE GAP
  in the interior arm — fix it (the override shim) BEFORE the dispatch.** The head-on kernel-checked spike confirmed
  the honest-engine reshape AVOIDS row-598 / §(4.91) (the eq.-(6.27) decoupling works) and that 6/11 arm slots
  discharge clean from the discriminator's ACTUAL outputs (incl. the `w`/`hwmem` bottom test). But
  `chainData_interior_realization_hρGv`'s `hends_ea`/`hends_eb` (+ `hρe₀`'s `hends_i` + the bottom-relabel's `he₀rec`)
  demand a SPECIFIC split-body-first orientation of `ends₀` at the re-inserted hinges + the fresh `e₀`, which the
  discriminator's IH-derived `ends₀ = Q.ends` provides only up to a FREE disjunction (LEAF-1 gives `(v,a)∨(a,v)`).
  The d=3 M₃ arm forces this via a `Function.update` OVERRIDE selector (`ends₃`); the general arm has NO such slot.
  **Fix (recommended A):** give the interior arm an override selector parameter (M₃ `ends₃` pattern), restate the
  hinge slots against it (`rfl`), the span slots via `rigidityRows_ofNormals_congr_ends`. Alternatively (B): expose
  an orientation-normalized `ends₀` from the discriminator (witness internal). Then the dispatch lands. Detail:
  §(4.96). Multi-commit/likely-multi-session; user's standing priority (full faithful KT, redoing work is fine, NO
  shortcuts) holds — the override shim is below the frozen contract + motive/IH (no new math, no cert change).
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

**THE `chainData_dispatch` INTERIOR-BRANCH SATISFIABILITY SPIKE RAN (§(4.96), this session): BLOCKED-with-exact-residual
— a SELECTOR-ORIENTATION INTERFACE GAP (NOT row-598, NOT §(4.91)).** The head-on kernel-checked spike fired the
discriminator `exists_shared_redundancy_and_matched_candidate` ONCE at the base `v₁`-split, `obtain`-ed its full
20-field output verbatim, `by_cases`-split to the interior branch (`2 ≤ idsc`), and `refine`-d
`chainData_interior_realization_hρGv` against those ACTUAL outputs. The composition TYPECHECKS; **6 of 11 arm slots
discharge clean exit-0** (`hLn`/`hρgate` via `candidateVtx_succ_eq`; `hgab` via `hgp`; `hw` VERBATIM the d=3 M₃
`case hw`; `hwcard`; `hwmem` via `chainData_bottom_relabel` once `he₀rec` supplied) — the bottom family + relabelled
structural slots fill the honest engine defeq-clean, so the prior hand-off's "real satisfiability test of `w`/`hwmem`"
PASSES. **The genuine blocker:** `hends_ea`/`hends_eb` (and `hρe₀`'s `hends_i`, and the bottom-relabel's `he₀rec`)
demand the SPECIFIC split-body-first ORIENTATION of `ends₀` at the two re-inserted chain hinges + the fresh `e₀`; the
discriminator's `ends₀ = Q.ends` (the IH realization) records each edge in a GENUINELY FREE order (LEAF-1
`candidateEnds_records_splitOff_isLink` yields only a `(v,a) ∨ (a,v)` disjunction). The d=3 path forces this via a
`Function.update` OVERRIDE selector (M₃ takes BOTH raw `ends₀` for the bottom AND `ends₃` for the hinges,
`Realization.lean:528/588`); **the general arm `chainData_interior_realization_hρGv` has NO override slot** — it
conflates both roles into the single raw relabel `endsσρ`, so its hinge-orientation hypotheses are unsatisfiable from
the free-orientation discriminator output. Full residual breakdown + the two fixes: design §(4.96).

**FIRST ACTION NEXT SESSION: add the orientation-override shim (fix (A)), then build `chainData_dispatch`.**

**The next concrete step — the override shim THEN the dispatch (the §(4.96) BLOCKED residual is the live work):**
1. **Reshape `chainData_interior_realization_hρGv` to take a `Function.update` OVERRIDE selector** (fix (A), the
   M₃ `ends₃` pattern, below the frozen contract + motive/IH — NO new math, NO cert change): add an `endsσρ₁`
   parameter = `Function.update (Function.update endsσρ (edge idsc) (v,a)) (edge (idsc−1)) (v,b)` decoupling the
   raw-`ends₀` bottom role from the orientation-forced hinge role; state `hends_ea`/`hends_eb` against the
   override (now `rfl`-discharged), and the `hρGv`/`hwmem`/`hρe₀` congruences via `rigidityRows_ofNormals_congr_ends`
   (the d=3 dispatch's step, `Realization.lean:1282`). **Alternatively (fix (B))** strengthen the discriminator
   `exists_shared_redundancy_and_matched_candidate` to RETURN an orientation-normalized `ends₀` recording every
   `Gab`-link (incl. `e₀`) split-body-first — it has the witness internally (`hrec'`/`Q.ends`, `Realization.lean:322`),
   so exposing-not-proving. **Recommended: (A)** (mirrors the GREEN d=3 M₃; keeps the discriminator generic).
2. **THEN build the `chainData_dispatch` router:** case-split the matched candidate `idsc` on `(i:ℕ)` — base/floor via
   `chainData_split_realization` (`Realization.lean:1164`), interior `2 ≤ idsc` via the (reshaped) interior arm.
   Source the gate from the discriminator (gate bridge `candidateVtx_succ_eq`, ✓ probe-confirmed plumbing); `hρe₀`
   from `interior_hρe₀_of_baseWidening` (`ForkedArm.lean:814`; the `hedgeGv` feed needs a `hingeRow_swap`
   `(vtx 2,vtx 0)`→`(vtx 0,vtx 2)` pair-flip + the `vtx ⟨1⟩` vs `vtx ⟨1⟩.castSucc` index-form bridge — plumbing);
   `hρGv` from `chainData_relabel_arm_hρGv` (`ChainColumn.lean:1390`); the RELABELLED bottom `L ∘ w`/`hwmem` from
   `chainData_bottom_relabel` (`Chain.lean:353`, ✓ probe-confirmed once `he₀rec` from the override/discriminator);
   `hends_Gv`/`hne_Gv` from LEAF-1 + general position (orientation-free, ✓ plumbing). Lands with the approved C.3
   `hIH` add. The probe confirmed everything EXCEPT the orientation slots is satisfiable; fix (A)/(B) closes those.
3. **DISCARDS at the reshape** (complete lemmas, no `sorry`s — retire once the dispatch lands): the entire
   `_aug`/`rigidityMatrixEdgeAug` interior fork (`case_III_rank_certification_aug{,_ofNormals}`/`_matrix{,_sep}`/
   `_zero₁₂`/`_chain`, `case_III_arm_realization_aug_ofNormals`, `hingeRow_mem_ofNormals_rigidityRows_chainEdge`),
   the `caseIIICandidate` override + the (D-subst) `_ofNormals` siblings, AND the now-superseded interior
   wrappers `chainData_arm_realization_sep` (`Realization.lean`)/the `_zero₁₂` `D-CAN-3b` wrapper. Multi-commit,
   likely-multi-session. `d=3` stays green on the SAME honest engine via the `k=2` spine (untouched).

**SURVIVING infrastructure (read at `def`/`theorem` §(4.94)/(4.95)):** the honest engine `case_III_rank_
certification` (general-`k`!) + `case_III_arm_realization`/`_M2`; `chainData_split_realization` (base + the
interior template); the LANDED crux leaf `chainData_relabel_arm_hρGv` (`ChainColumn.lean:1390`); the discriminator
`exists_shared_redundancy_and_matched_candidate` (matched `i` + gate + `hedgeGv` widening); `interior_hρe₀_of_
widening` (the `hρe₀` slot); the union-count `case_III_claim612_gen`. **DISCARDED under reshape:** the entire
`_aug`/`rigidityMatrixEdgeAug` interior fork.

Authoritative scoping: `notes/Phase23-design.md` §(4.95) (the crux-leaf-is-landed GO), §(4.94) (the `d=3`
mechanism + the divergence + the reshape), §(4.93) (the cert-interface obstruction), §(4.92) (the route-(a)
corner core), §(4.91)/(4.90) (the refuted override / (D-subst) arms).

## Decisions made during this phase

### The reshape ASSEMBLY (the honest interior arm + its LEAF-1 supplier; kept, the live route)
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
