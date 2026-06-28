# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **THE PATH IS FOUND: the crux leaf is LANDED (§(4.95), 2026-06-28 session #48); next
step = BUILD the honest interior arm + the `chainData_dispatch` router.** After three kernel-checked refutations
converged on the cert-interface wall, the `d=3`-anchored design-pass (§(4.94)) found the honest engine
`case_III_rank_certification` (`Candidate.lean:1662`, ALREADY general-`k`) sources `±r` via the eq.-(6.27) ROW-OP
of a BOTTOM `G−v`-row (decoupling the gate from the membership — no §(4.91) collision), and the
interior-`hρGv` spike (§(4.95)) then returned **GO**: the one genuinely-new leaf, the interior `hρGv` ROW
membership, is TRUE, honestly provable from the SINGLE base `ρ₀`, and **ALREADY LANDED sorry-free** as
`Graph.ChainData.chainData_relabel_arm_hρGv` (`Relabel/ChainColumn.lean:1390`; coordinator-verified — right
conclusion, axiom-clean, green; built for the dead override route but collision-free in the honest engine). **So
no genuinely-new linear-algebra leaf remains; the reshape is pure ASSEMBLY:** route the interior matched
candidate through the honest engine (`chainData_split_realization` `Realization.lean:1164` already wraps it for
`0<i`), feeding the LANDED `hρGv` + gate + `hρe₀` + the bottom family; then the `chainData_dispatch` router;
abandoning the diverged `_aug`/`rigidityMatrixEdgeAug` fork. Below the C.0–C.6 contract + the 0-dof motive; NO
shortcut. The build is the real satisfiability test of the bottom family `w`/`hwmem` for the interior. `d=3`
stays fully green (it runs the SAME honest engine via the `k=2` spine). Authoritative scoping:
`notes/Phase23-design.md` §(4.95) (crux-leaf-landed GO), §(4.94) (the reshape + the `d=3` mechanism), §(4.93)
(the cert-interface obstruction), §(4.92) (route-(a) corner core), §(4.91)/(4.90)/(4.84)–(4.89) (the refuted
(D-substitution)/override arc), §§(4.77)–(4.83) (the six route refutations). Program map:
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`). 23f built the geometry-arm cert
infrastructure (interior-corner cert, D-CAN bottom, the `_aug` ladder), refuted six narrow corner routes, then
spent a full session building the (D-substitution) re-architecture — which a final dispatch found is OFF-BY-ONE
at the corner. When the geometry arm closes, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE RESHAPE (§(4.94)/(4.95)) — THE PATH IS FOUND.** The three refuted arms (override §(4.91); (D-subst) row
598/§(4.90); route-(a) `hr` slot §(4.93)) all died because the general-`d` interior cert is the diverged
`_aug`/`rigidityMatrixEdgeAug` fork, which demands the single `±r` row be in `span(G-rows)` ALONE — only fillable
by a `v`-incident edge whose membership = `ρ₀(C(e_a))=0` = negation of the corner gate. The `d=3`-anchored
design-pass found the honest engine they diverged FROM: `case_III_rank_certification` (`Candidate.lean:1662`, the
`hρGv`-collapse engine, ALREADY general-`k`) sources `±r` via the eq.-(6.27) ROW-OP `hingeRow v a ρ =
hingeRow v b ρ − hingeRow a b ρ` (genuine present-body `e_b`-row − BOTTOM `G−v`-row `hρGv`), decoupling the gate
from the membership. **The §(4.95) spike then RESOLVED the one genuinely-new leaf = GO: the interior `hρGv` row
membership is ALREADY LANDED sorry-free as `chainData_relabel_arm_hρGv` (`ChainColumn.lean:1390`) — it propagates
the single base `ρ₀` to the interior (KT eq. (6.59)), and is collision-free in the honest engine.** So the
reshape is now pure ASSEMBLY: route the interior through the honest engine (`chainData_split_realization` wraps it
for `0<i`), feeding the LANDED `hρGv` + gate + `hρe₀` + the bottom family. The build is the real satisfiability
test of `w`/`hwmem` for the interior. See *Hand-off* + §(4.94)/(4.95).

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched):**
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
- [ ] **[NEXT] THE RESHAPE BUILD — the honest interior arm `chainData_interior_realization_hρGv`** (§(4.94)
  Part 4): `case_III_arm_realization`/`case_III_rank_certification` at the interior split tuple, fed `hρGv` from
  the LANDED `chainData_relabel_arm_hρGv` + gate (discriminator) + `hρe₀` (`interior_hρe₀_of_widening`) + the
  bottom family `w`/`hwmem`, reducing the `hLn`/`hgab`/`hρgate`/`hρe₀` gate slots through the now-landed seed
  reads (above). Structural slots all exist as `ChainData` accessors (`notMem_/succ_mem_/pred_castSucc_mem_
  vertexSet_removeVertex_castSucc`, `isLink_succ_/pred_edge`, `isLink_eq_succ_or_pred_or_removeVertex`,
  `removeVertex_isLink_edge_succ_pred_off`). The build is the real satisfiability test of the relabelled-`endsσρ`
  slots (`hends_ea`/`hends_eb`/`hends_Gv`/`hne_Gv`) + the bottom family `w`/`hwmem` for the interior (BLOCKED
  with the precise gap if a hypothesis isn't dischargeable — NO shortcut). See *Hand-off* leaf 1.
- [ ] **THE `chainData_dispatch` ROUTER (after the interior arm).** Case-split matched `i` on `(i:ℕ)`: base/floor
  via `chainData_split_realization`; interior via the new arm. Lands with the approved C.3 `hIH` add. Then
  discards the `_aug` fork + the override/(D-subst) siblings. See *Hand-off* leaf 2-3.
- [x] **(D-substitution) S1–S5 + spine + 5c/5e/5f.hA/5f.hAeq — LANDED but DEAD/CONDITIONAL** (the corner `hA` hyp
  is unsatisfiable for the collapsed candidate; row 598 + §(4.91)). Detail: *Current state* + design
  §(4.84)–(4.90) + git. The make-or-break spikes (§(4.85)–(4.89)) all returned GO by ABSTRACTING the corner gate
  as a free hypothesis; the dispatch (sourcing it) found it unsatisfiable. The GO-cascade lesson is in *Promoted
  to* below. → discard/retire at the re-architecture or phase-close.
- [x] **A1–A5c backbones + D1 `interior_hsplitGP` + the route-refutation LA cores** — LANDED, REUSED/dead-but-
  correct. `_matrix`/`_rowOp`/chain dead arms + the (D-substitution) conditional bricks + the `C≠0` orphan
  5f.hAeq → αE6 retirement DEFERRED to phase-close (or the override-route landing).

## Blockers / open questions

- **THE RESHAPE IS SCOPED (§(4.94)); the live blocker is the interior-`hρGv`-membership SPIKE, and its TRUTH is
  OPEN.** The reshape direction (route the interior through the LANDED honest `case_III_rank_certification`
  engine, abandon the `_aug`/`rigidityMatrixEdgeAug` fork) is a confident GO at the ENGINE level (already
  general-`k`, already wrapped by `chainData_split_realization`). The ONE genuinely-new leaf — the interior
  `hρGv` ROW membership `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ₀ ∈ span(G − vtx i rows)` — is SPIKE-FLAGGED
  AND its truth is genuinely uncertain: the landed degree-2 carry produces the column/perp, not the row
  membership, and the target row is a non-edge. The spike either lands it (eq.-(6.27) combination of
  `(G − vtx i)`-rows, find the shared `w`) or REFUTES it (KT's interior membership needs a mechanism the base
  widening does not supply → genuine-math escalation to the user). Multi-commit/likely-multi-session rebuild on
  GO; user's standing priority (full faithful KT, redoing work is fine, NO shortcuts) holds.
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

**THE CRUX LEAF IS LANDED — THE PATH IS FOUND (§(4.95), this session). FIRST ACTION NEXT SESSION: build the
honest interior arm `chainData_interior_realization_hρGv`, then the `chainData_dispatch` router.** The
interior-`hρGv`-membership spike returned **GO**: the interior `hρGv` row membership is TRUE, honestly provable
from the SINGLE base `ρ₀`, and **ALREADY LANDED sorry-free** as `Graph.ChainData.chainData_relabel_arm_hρGv`
(`Relabel/ChainColumn.lean:1390`, coordinator-verified: right conclusion, axiom-clean, green). It was built for
the dead override route (labelled "dead" at `Chain.lean:497`) but is **collision-free in the honest engine** —
the eq.-(6.27) row-op decouples the gate from the membership. So §(4.94)'s one open leaf is DISCHARGED; **no
genuinely-new linear-algebra leaf remains on the `hρGv` axis.** The reshape is now pure ASSEMBLY.

**The next concrete step (the smallest complete deliverable) — a BUILD:**
1. **Build the honest interior arm `chainData_interior_realization_hρGv`** (§(4.94) Part 4 signature; the
   `chainData_split_realization` `Realization.lean:1164` shape, generalized off the base-split requirement):
   instantiate `case_III_arm_realization`/`case_III_rank_certification` (`Candidate.lean:1662`, the honest
   general-`k` engine) at the interior split tuple `(Gv, ends, q, a, b, ρ) = (G − vtx i.castSucc, endsσρ, qρ,
   vtx i.succ, vtx (i−1).castSucc, −ρ₀)`, feeding: `hρGv` from the LANDED `chainData_relabel_arm_hρGv`; `hρe₀`
   from `interior_hρe₀_of_widening`/`_of_baseWidening` (LANDED); `hgate` from the discriminator (LANDED, gate
   bridge `candidateVtx_succ_eq` LANDED); and the bottom family `w`/`hwmem` (per-member relabel
   `chainData_bottom_relabel` LANDED). **Seed reads now LANDED** (this session) —
   `seedShift_succ_castSucc`/`seedShift_pred_castSucc` (`Induction/Operations.lean`): `qρ(a,·) = q(vtx i.succ,·)`,
   `qρ(b,·) = q(vtx i.castSucc,·)`, the M₃-`hqρc`/`hqρv` analogues the `hLn`/`hgab`/`hρgate`/`hρe₀` slots reduce
   through. **The build is the REAL satisfiability test of `w`/`hwmem` (and the relabelled-`endsσρ`
   `hends_ea`/`hends_eb`/`hends_Gv`/`hne_Gv` wiring) for the interior** — the spike confirmed the `hρGv` slot
   fills defeq-exact, but the bottom family is "landed shape", not yet sourced for the interior consumer; if a
   hypothesis is not dischargeable, return BLOCKED with the precise gap (do NOT abstract it as a hypothesis — NO
   shortcuts). Structural template = `case_III_arm_realization_M3` (`Relabel/Arm.lean:54`, the `i=2` instance).
2. **Then the `chainData_dispatch` router:** case-split the matched candidate `i` on `(i:ℕ)` — base/floor via
   `chainData_split_realization`, interior `0<i` via the new arm. Lands with the approved C.3 `hIH` add.
3. **DISCARDS at the reshape** (complete lemmas, no `sorry`s — retire once the honest arm lands): the entire
   `_aug`/`rigidityMatrixEdgeAug` interior fork (`case_III_rank_certification_aug{,_ofNormals}`/`_matrix{,_sep}`/
   `_zero₁₂`/`_chain`, `case_III_arm_realization_aug_ofNormals`, `hingeRow_mem_ofNormals_rigidityRows_chainEdge`),
   the `caseIIICandidate` override + the (D-subst) `_ofNormals` siblings. Multi-commit, likely-multi-session.
   `d=3` stays green on the SAME honest engine via the `k=2` spine (untouched).

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
