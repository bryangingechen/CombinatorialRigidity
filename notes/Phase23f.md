# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **CERT-INTERFACE RESHAPE SCOPED (§(4.94), 2026-06-28 session #48); next step = the
interior-`hρGv`-membership SPIKE (the ONE genuinely-new leaf, truth OPEN).** The `d=3`-anchored design-pass
(§(4.94)) found the decisive fact: **the WORKING `d=3` cert is `case_III_rank_certification`
(`Candidate.lean:1662`, the `hρGv`-collapse engine), which is ALREADY general-`k` and sources `±r` HONESTLY via
the eq.-(6.27) ROW-OP of a BOTTOM `G−v`-row** (`hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ`, with
`hingeRow a b ρ ∈ span(G−v rows) = hρGv`) — NOT the `_matrix`/`_aug` cert the §(4.93) wall lives in. §(4.93)'s
"`_matrix`/M₃ template" was IMPRECISE: the `_matrix`/`_aug` certs are the Phase-23d/23e general-`d` FORKS that
introduced the diverged `rigidityMatrixEdgeAug` + `hr ∈ span F.rigidityRows` interface — exactly the wall. **The
reshape: route the INTERIOR matched candidate through the honest `case_III_rank_certification` engine (already
general-`k`; `chainData_split_realization` `Realization.lean:1164` already wraps it for `0 < i`), abandoning the
`_aug` fork.** The interior arm is then `chainData_split_realization`'s shape with the base-split-derived W6b
bundle swapped for the single shared base `ρ₀` + the interior inputs: gate (LANDED, discriminator), `hρe₀`
(LANDED, `interior_hρe₀_of_widening`), and the **interior `hρGv` ROW membership** —
`hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ₀ ∈ span(G − vtx i.castSucc rows)` — **the ONE genuinely-new leaf,
SPIKE-FLAGGED, its TRUTH OPEN.** The landed degree-2 carry produces the COLUMN read
(`interior_group_acolumn_eq_neg_baseRedundancy`) and the PERP (`interior_hρe₀_of_widening`), NOT the row
membership; the target row is a NON-edge (`vtx i.succ — vtx (i−1)` is not a chain edge) needing an eq.-(6.27)
combination of `(G − vtx i)`-rows. **The reshape REVERTS to the older honest engine + ONE leaf — consistent with
"redoing old work is fine"; below the C.0–C.6 contract + the 0-dof motive; NO shortcut (`hρGv` is honestly
discharged or the spike refutes the route).** `d=3` stays fully green (hard constraint; it runs the SAME honest
engine via the `k=2` spine). Authoritative scoping: `notes/Phase23-design.md` §(4.94) (the `d=3` mechanism + the
divergence + the reshape + the spike-flagged leaf), §(4.93) (the cert-interface obstruction), §(4.92) (the
route-(a) corner core, confirmed right), §(4.91)/(4.90)/(4.84)–(4.89) (the refuted (D-substitution)/override
arc), §§(4.77)–(4.83) (the six route refutations). Program map: `notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`). 23f built the geometry-arm cert
infrastructure (interior-corner cert, D-CAN bottom, the `_aug` ladder), refuted six narrow corner routes, then
spent a full session building the (D-substitution) re-architecture — which a final dispatch found is OFF-BY-ONE
at the corner. When the geometry arm closes, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE RESHAPE (§(4.94)).** The three refuted arms (override §(4.91); (D-subst) row 598/§(4.90); route-(a) `hr`
slot §(4.93)) all died because the general-`d` interior cert is the diverged `_aug`/`rigidityMatrixEdgeAug`
fork, which demands the single `±r` row be in `span(G-rows)` ALONE — only fillable by a `v`-incident edge whose
membership = `ρ₀(C(e_a))=0` = negation of the corner gate. The `d=3`-anchored design-pass found the honest
engine they diverged FROM: `case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine,
ALREADY general-`k`) sources `±r` via the eq.-(6.27) ROW-OP `hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ`
(genuine present-body `e_b`-row − BOTTOM `G−v`-row `hρGv`), decoupling the gate from the membership. The reshape:
route the interior through that engine (already wrapped by `chainData_split_realization` for `0<i`), abandon the
`_aug` fork. The ONE missing input is the interior `hρGv` ROW membership — the genuinely-new SPIKE-FLAGGED leaf
(truth OPEN; the landed degree-2 carry lands the column/perp, not the row). See *Hand-off* + §(4.94).

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched):**
- **SURVIVES the reshape (the honest engine + its general-`k` infrastructure, §(4.94)):** the honest cert
  `case_III_rank_certification` (`Candidate.lean:1662`, general-`k`!) + arm `case_III_arm_realization`/`_M2`
  (`Arms.lean:310`); `chainData_split_realization` (`Realization.lean:1164`, base/floor route + interior arm
  template); the base `hρGv` producer `exists_candidateRow_bottomRows_of_rigidOn` (`Candidate.lean:401`) +
  `chainData_split_w6b_gates` (`Realization.lean:889`); the discriminator `exists_shared_redundancy_and_matched_
  candidate` (`Realization.lean:2134`) + `case_III_claim612_gen` (`Claim612.lean:1333`); `interior_hρe₀_of_
  widening` (`ForkedArm.lean:768`, the `hρe₀` slot); the column carry `interior_group_acolumn_eq_neg_base
  Redundancy` (`ChainColumn.lean:729`, ingredient for the new leaf); `hingeRow_sub_hingeRow_eq` (`Basic.lean:612`).
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

**The cert-interface reshape is SCOPED (§(4.94)); the next step is the interior-`hρGv`-membership SPIKE (the ONE
genuinely-new leaf, truth OPEN) — see *Hand-off*. No reshape build until the spike returns GO/REFUTE.**

- [x] **THE OVERRIDE-COMPOSITION SPIKE — RAN, REFUTED (§(4.91), row 600).** §(4.82)/(4.83) STAND. Detail: §(4.91).
- [x] **THE KT-FAITHFULNESS SCOPING (§(4.92)) + THE ROUTE-(a) CORNER SPIKE (§(4.93)) — DONE.** Corner core
  `corner_hA'_of_gate` composes (sub-Q A GO), but the `_aug` cert's `hr : rRow ∈ span F.rigidityRows` slot
  REFUTES route (a) — the TRUE obstruction is the cert INTERFACE (`rigidityMatrixEdgeAug` forces `±r` onto a
  framework edge, colliding with the gate). Detail: §(4.93).
- [x] **THE `d=3`-ANCHORED CERT-INTERFACE DESIGN-PASS — DONE (§(4.94), session #48).** The WORKING `d=3` cert is
  `case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine, ALREADY general-`k`),
  sourcing `±r` via the eq.-(6.27) ROW-OP of a BOTTOM `G−v`-row, NOT the `_matrix`/`_aug` fork. Reshape = route
  the interior through that engine. SURVIVES/DISCARDS + the spike-flagged new leaf in §(4.94).
- [ ] **[NEXT] THE INTERIOR-`hρGv`-MEMBERSHIP SPIKE (truth OPEN).** Compiler-check the genuinely-new leaf
  `Graph.ChainData.interior_hρGv_of_baseWidening`:
  `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ₀ ∈ span(ofNormals (G − vtx i.castSucc) ends q).rigidityRows`,
  from the base widening `hingeRow (v₀)(v₂) ρ₀ = ∑ cGv • hingeRow(…)(G − v₁ links)`, SORRY-FREE. The landed
  degree-2 carry lands the COLUMN/PERP, NOT the ROW membership; the target row is a NON-edge needing an
  eq.-(6.27) combination of `(G − vtx i)`-rows. Do NOT GO from prose (§(4.90)/(4.93) lesson). If REFUTED → a
  genuine-math finding, escalate to user. See *Hand-off* leaf 1.
- [ ] **THE RESHAPE BUILD (on spike GO).** The new honest interior arm `chainData_interior_realization_hρGv`
  (the `chainData_split_realization` shape with the base-split W6b bundle swapped for the shared base `ρ₀` +
  gate (LANDED) + `hρe₀` (LANDED) + the new `hρGv` leaf) + the `chainData_dispatch` router (base/floor via
  `chainData_split_realization`; interior via the new arm). Discards the `_aug` fork. See *Hand-off* leaf 2.
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

**THE CERT-INTERFACE RESHAPE IS SCOPED (§(4.94), this session). FIRST ACTION NEXT SESSION: run the
interior-`hρGv`-membership SPIKE (the ONE genuinely-new leaf; its TRUTH is OPEN).** The design-pass established:
the WORKING `d=3` cert is `case_III_rank_certification` (`Candidate.lean:1662`, the `hρGv`-collapse engine,
ALREADY general-`k`), sourcing `±r` via the eq.-(6.27) ROW-OP of a BOTTOM `G−v`-row — `hingeRow v a ρ =
hingeRow v b ρ − hingeRow a b ρ`, where `hingeRow v b ρ` is a genuine present-body `e_b`-row and `hingeRow a b ρ`
is the BOTTOM membership `hρGv : hingeRow a b ρ ∈ span(ofNormals Gv ends q).rigidityRows`. The `_matrix`/`_aug`
certs (`Candidate.lean:2429`+) are the diverged Phase-23d/23e forks (the `rigidityMatrixEdgeAug` + `hr ∈ span G`
wall). The reshape: route the interior through the honest engine (`chainData_split_realization`
`Realization.lean:1164` already wraps it for `0 < i`); the only missing input is the interior `hρGv` row
membership.

**The next concrete step (the smallest one that moves work forward) — a SPIKE, not a build:**
1. **[THE INTERIOR-`hρGv`-MEMBERSHIP SPIKE] Compiler-check the ONE genuinely-new leaf** (throwaway scratch
   `.lean`, deleted before commit; §(4.94)'s flagged leaf): `Graph.ChainData.interior_hρGv_of_baseWidening`,
   `hingeRow (vtx i.succ) (vtx (i−1).castSucc) ρ₀ ∈ span(ofNormals (G − vtx i.castSucc) ends q).rigidityRows`,
   from the LANDED base widening `hedgeGv : hingeRow (vtx 0)(vtx 2) ρ₀ = ∑ⱼ cGv • hingeRow(uvⱼ)(vvⱼ)(rvⱼ)` over
   `(G − vtx 1)`-links. **The target row is a NON-edge** (`vtx i.succ — vtx (i−1)` is not a chain edge; the
   chain edges `edge i`/`edge (i−1)` at `vtx i` are both deleted in `G − vtx i`), so the membership must be an
   eq.-(6.27) COMBINATION: `hingeRow (vtx i.succ)(vtx (i−1)) ρ₀ = hingeRow (vtx i.succ) w ρ₀ −
   hingeRow (vtx (i−1)) w ρ₀` for some shared `w ≠ vtx i`, each a genuine `(G − vtx i)`-row — FIND `w` + the
   combination from the base widening regrouped at `vtx i`. Ingredients: the landed COLUMN carry
   `interior_group_acolumn_eq_neg_baseRedundancy` (`ChainColumn.lean:729`) + `interior_group_eq_baseRedundancy`
   (`:648`) + `hingeRow_sub_hingeRow_eq` (`Basic.lean:612`). **Do NOT GO from prose (§(4.90)/(4.93) lesson).**
   The landed carry produces the column/perp, NOT the row membership — so the spike could REFUTE; if it does,
   that is a genuine-math finding (KT's interior membership needs a mechanism the base widening doesn't supply)
   → ESCALATE to the user, do not auto-pivot.
2. **On spike GO:** build the new honest interior arm `chainData_interior_realization_hρGv` (the
   `chainData_split_realization` shape with the base-split W6b bundle swapped for the shared base `ρ₀` + gate
   (LANDED, discriminator) + `hρe₀` (LANDED, `interior_hρe₀_of_widening`) + the new `hρGv` leaf) + the
   `chainData_dispatch` router (base/floor via `chainData_split_realization`, interior `0<i` via the new arm).
   DISCARDS the `_aug` fork (`case_III_rank_certification_aug{,_ofNormals}`/`_matrix{,_sep}`/`_zero₁₂`/`_chain`,
   `case_III_arm_realization_aug_ofNormals`, `hingeRow_mem_ofNormals_rigidityRows_chainEdge`, the
   `caseIIICandidate` override). Multi-commit, likely-multi-session. `d=3` stays green on the SAME honest engine
   via the `k=2` spine (untouched).
3. **SURVIVING infrastructure (read at `def`/`theorem` §(4.94)):** the honest engine `case_III_rank_
   certification` (general-`k`!) + `case_III_arm_realization`/`_M2`; `chainData_split_realization` (base + the
   interior template); `exists_candidateRow_bottomRows_of_rigidOn`/`chainData_split_w6b_gates` (the base `hρGv`
   producer); the discriminator `exists_shared_redundancy_and_matched_candidate` (matched `i` + gate +
   `hedgeGv` widening); `interior_hρe₀_of_widening` (the `hρe₀` slot); the column carry
   `interior_group_acolumn_eq_neg_baseRedundancy` (ingredient for the new leaf); the union-count
   `case_III_claim612_gen`. **DISCARDED under reshape:** the entire `_aug`/`rigidityMatrixEdgeAug` interior fork.

Authoritative scoping: `notes/Phase23-design.md` §(4.94) (the `d=3` mechanism + the divergence + the reshape +
the spike-flagged leaf), §(4.93) (the cert-interface obstruction), §(4.92) (the route-(a) corner core), §(4.91)
(override refutation), §(4.90) (superseded).

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
