# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **THE KT-FAITHFUL ARCHITECTURE IS SCOPED (§(4.92), 2026-06-28 session #48); next step
= the flagged corner composition SPIKE, then the dispatch build.** After BOTH built arms were kernel-refuted
(override §(4.91); (D-substitution) §(4.90)/row 598), the KT-faithfulness design-pass settled the path: **route
(a)** — KT's disjunction-over-all-`Mᵢ` union-count with a GENUINE per-candidate corner `Mᵢ = [r(Lᵢ); ρ₀]`
whose `±r` row IS the shared redundancy `ρ₀` ITSELF (KT eq. (6.64)/(6.66)), NOT a reproduced/second edge.
**Decisive re-read finding (correcting §(4.90)):** KT's corner `±r` row is the redundant `(v₀v₁)ᵢ*` row reduced
by the eq.-(6.63) row-op to the bare functional `ρ₀` — NEVER a framework edge-row. Both built arms erred by
reifying it as an edge (override → short-circuit panel `(vtx(i+1),vtx(i−1))`, residual `q(vtx(i−1))=q(vtx i)`
FALSE; (D-subst) → COLLAPSE onto the single chain edge `e_a`, gate `ρ₀(C(e_a))≠0` = exact negation of the perp
`ρ₀(C(e_a))=0`, off-by-one). The faithful corner is ALREADY LANDED + framework-general
(`corner_hA'_of_gate` `Concrete.lean:810` = KT eq. (6.64)/(6.65) verbatim); route (a) DROPS the
`caseIIICandidate` reproduced-slot override AND the (D-subst) second-edge `e_b`. **The architecture is a GO;
the FIRST BUILD LEAF (the corner `hr = ρ₀` composition with the one-slot candidate) is FLAGGED for a
compiler-checked spike before the dispatch is wired (the §(4.91) refutation class; §(4.90)'s confident
prose-GO cost a refuted spike). See *Hand-off*.** `d=3` stays fully green (hard constraint). Authoritative
scoping: `notes/Phase23-design.md` §(4.92) (the faithful-architecture verdict + diagnosis + decomposition +
survives/discards inventory + the flagged spike), §(4.91) (override refutation), §(4.90) (superseded GO),
§(4.84)–(4.89) (the refuted (D-substitution) arc), §§(4.77)–(4.83) (the six route refutations). Program map:
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`). 23f built the geometry-arm cert
infrastructure (interior-corner cert, D-CAN bottom, the `_aug` ladder), refuted six narrow corner routes, then
spent a full session building the (D-substitution) re-architecture — which a final dispatch found is OFF-BY-ONE
at the corner. When the geometry arm closes, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE RESOLVED DECISION (the §(4.91) spike, option A).** The user adjudicated the §(4.90) reversal = option A
(decisive compiler-checked spike before discarding the (D-substitution) work). The spike (§(4.91)) **REFUTED**
the override: the override spine's `hr` slot is filled ONLY by `hingeRow_mem_caseIIICandidate_rigidityRows_
reproduced`, which at `t=0` demands the perp on the **short-circuit panel `(vtx(i+1),vtx(i−1))`** (PROBE 1,
sorry-free), but the perp producer §(4.90) named (`interior_hρe₀_of_widening`, consuming the discriminator's
ACTUAL `hedgeGv`) delivers the perp on the **chain-edge panel `(vtx(i+1),vtx i)`** — kernel residual
`q(vtx(i−1))=q(vtx i)`, FALSE (`vtx_ne`). The §(4.90) "they used an arbitrary `q`" dispute is itself refuted:
the spike sourced from the discriminator's own seed + co-chosen outputs, with adversarial negative controls all
failing; the chain-edge→short-circuit bridge needs a coplanarity §(4.81) already kernel-refuted for the
discriminator's `AlgebraicIndependent ℚ q`. **So §(4.82)/(4.83) STAND.**

**THE SHARED ROOT (both arms refuted, different seams).** The override fails because its short-circuit
REPRODUCTION reads the wrong panel; the (D-substitution) genuine-`ofNormals` arm failed (row 598) by collapsing
KT's two corner conditions onto ONE chain edge `e_a` (gate `ρ₀(C(e_a))≠0` = exact negation of `hr` perp
`ρ₀(C(e_a))=0`, off-by-one). Both trace to the project's `splitOff` + `caseIIICandidate` extensor-OVERRIDE
architecture (the §(4.69.2) divergence KT does NOT have): it DELETES the body `v=vtx i`, so KT's redundant-row
edge `vᵢ₋₁vᵢ` (eq. (6.59), incident to the still-present `vᵢ`) doesn't exist — neither arm reproduces KT's TWO
distinct edges (`vᵢvᵢ₊₁` free, `vᵢ₋₁vᵢ` redundant, both at the present `vᵢ`). **The honest KT-faithful path is a
foundational re-architecture (KT's disjunction-over-all-`Mᵢ` union-count / a CHAIN-2c dispatch-spine reshape),
NOT a finish of either built arm — surfaced to the user; see *Hand-off*.**

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched):**
- **REUSABLE through the re-architecture (genuinely landed + satisfiable; KT-faithful infrastructure):** the
  union-count `case_III_claim612_gen` (`Claim612.lean:1333`); the discriminator `exists_shared_redundancy_and_
  matched_candidate` (`Realization.lean:1481`/`:2134`) + `chainData_split_w6b_gates` (`:889`); the `_aug`
  block-data bricks 5c `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` + 5e `exists_aug_bottom_blockData_
  of_Gab` (`Concrete.lean`); the D-CAN bottom machinery (`submatrix_columnOp_toBlocks₂₂_eq_Gab` `:2387`); the
  block-rank backbones (`Rank.lean:480/574/622`); D1 `interior_hsplitGP` (`Realization.lean:758`). The recon
  must confirm which of these survive the union-count reshape (expected: most — they are below the override).
- **DEAD — to discard at the re-architecture (both refuted arms):** the OVERRIDE pieces — spine
  `chainData_arm_realization_aug_zero₁₂` (`:1625`), corner `chainData_arm_corner_hA_of_discriminator_gate`
  (`:1761`), `±r` `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` ← `interior_hρe₀_of_widening`, and the
  whole `caseIIICandidate` extensor-OVERRIDE device — refuted §(4.91); the **(D-substitution) `_ofNormals`
  siblings** — S1 `hingeRow_mem_ofNormals_rigidityRows_chainEdge` (`ForkedArm.lean:621`), S2
  `case_III_rank_certification_aug_ofNormals` (`Candidate.lean:2782`), S3 `case_III_realization_of_rank_ofNormals`
  (`ForkedArm.lean:1238`), S4 `case_III_arm_realization_aug_ofNormals` (`ForkedArm.lean:1309`), spine
  `chainData_arm_realization_ofNormals` (`Realization.lean:1769`), corner `chainData_arm_corner_hA_ofNormals_of_
  gate` (`:1840`), the `C≠0` read — refuted row 598. Correct conditional lemmas, but their corner `hA` is
  unsatisfiable; retire once the reshape route is scoped (no `sorry`s — they are complete lemmas, just unused).

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

**The faithful architecture is SCOPED (§(4.92)); the next step is the flagged corner composition spike, then
the dispatch build — see *Hand-off*. No dispatch build until the spike returns GO.**

- [x] **THE DECISIVE OVERRIDE-COMPOSITION SPIKE — RAN, REFUTED (§(4.91), row 600, session #48).** The override
  `chainData_dispatch` does NOT compose for the discriminator-co-chosen seed: its `hr` slot demands the
  short-circuit-panel perp `(vtx(i+1),vtx(i−1))`, but the discriminator emits the chain-edge-panel perp
  `(vtx(i+1),vtx i)` — residual `q(vtx(i−1))=q(vtx i)` FALSE. §(4.82)/(4.83) STAND. Detail: design §(4.91).
- [x] **THE KT-FAITHFULNESS SCOPING / DESIGN-PASS — DONE (§(4.92), session #48).** Route (a): union-count +
  genuine corner `Mᵢ = [r(Lᵢ); ρ₀]`, `±r = ρ₀` (KT eq. (6.64)/(6.66)), NOT a reproduced/second edge. Drops the
  `caseIIICandidate` reproduced-slot override + the (D-subst) `e_b`. Corner core ALREADY LANDED
  (`corner_hA'_of_gate`). Survives/discards inventory + decomposition in §(4.92).
- [ ] **[NEXT] THE FLAGGED CORNER `hr = ρ₀` COMPOSITION SPIKE.** Compiler-check that the `_aug` corner's
  `inr ()` row, fed the discriminator's `ρ₀`/`hedgeGv` bundle through the eq.-(6.63) `Lrow` row-op, composes to
  the `−ρ₀` read SORRY-FREE with a ONE-SLOT genuine candidate (no reproduced slot, no second edge). §(4.89) is
  strong evidence GO; the spike confirms end-to-end + resolves the keep-`vᵢ`-vs-`_aug`-`inr ()` sub-question.
  Do NOT GO from prose (§(4.90) lesson). See *Hand-off* leaf 1.
- [ ] **THE DISPATCH BUILD (on spike GO).** `chainData_dispatch` (never-built router) + the route-(a) arm
  restate `case_III_arm_realization_chain` (drops reproduced-slot hyps, feeds the cert from the one-slot
  candidate + `corner_hA_*_of_gate`). Below contract; wiring = `ends₁`-congruence + C.3 `hIH`-fed
  `interior_hsplitGP`. See *Hand-off* leaf 2.
- [x] **(D-substitution) S1–S5 + spine + 5c/5e/5f.hA/5f.hAeq — LANDED but DEAD/CONDITIONAL** (the corner `hA` hyp
  is unsatisfiable for the collapsed candidate; row 598 + §(4.91)). Detail: *Current state* + design
  §(4.84)–(4.90) + git. The make-or-break spikes (§(4.85)–(4.89)) all returned GO by ABSTRACTING the corner gate
  as a free hypothesis; the dispatch (sourcing it) found it unsatisfiable. The GO-cascade lesson is in *Promoted
  to* below. → discard/retire at the re-architecture or phase-close.
- [x] **A1–A5c backbones + D1 `interior_hsplitGP` + the route-refutation LA cores** — LANDED, REUSED/dead-but-
  correct. `_matrix`/`_rowOp`/chain dead arms + the (D-substitution) conditional bricks + the `C≠0` orphan
  5f.hAeq → αE6 retirement DEFERRED to phase-close (or the override-route landing).

## Blockers / open questions

- **THE FAITHFUL ARCHITECTURE IS SCOPED (§(4.92)); the live blocker is the flagged corner composition SPIKE.**
  Both built arms refuted (override §(4.91); (D-subst) row 598); the design-pass settled route (a) (union-count
  + genuine corner `Mᵢ = [r(Lᵢ); ρ₀]`, `±r = ρ₀`, NOT an edge — KT eq. (6.64)/(6.66)). Architecture = GO; the
  FIRST BUILD LEAF (corner `hr = ρ₀` with the one-slot candidate) is FLAGGED for a compiler-checked spike before
  the dispatch — the §(4.91) refutation class, and §(4.90)'s prose-GO cost a refuted spike. Multi-commit/
  likely-multi-session rebuild on GO; the user's standing priority (full faithful KT, redoing work is fine) holds.
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

**THE FAITHFUL ARCHITECTURE IS SCOPED (§(4.92), this session). FIRST ACTION NEXT SESSION: run the
flagged corner composition SPIKE (leaf 1 below), then — on GO — wire `chainData_dispatch`.** The KT-
faithfulness design-pass settled the architecture: route (a), KT's disjunction-over-all-`Mᵢ` union-count
with a GENUINE per-candidate corner `Mᵢ = [r(Lᵢ); ρ₀]` whose `±r` row IS the shared redundancy `ρ₀`
ITSELF (NOT a reproduced/second edge). This DROPS the `caseIIICandidate` reproduced-slot override AND the
(D-substitution) second-edge `e_b` reproduction — both were detours. **Decisive re-read finding (correcting
§(4.90)):** KT's corner `±r` row (eq. (6.64)) is the redundant `(v₀v₁)ᵢ*` row reduced by the eq.-(6.63)
row-op to the bare functional `±r = ρ₀` — it is NEVER a framework edge-row. Both built arms erred by
reifying it as an edge (override → wrong panel; (D-subst) → collapse onto `e_a`). The corner-as-`ρ₀` is
ALREADY LANDED + framework-general (`corner_hA'_of_gate` `Concrete.lean:810` = KT eq. (6.64)/(6.65) verbatim).

**The next concrete step (the smallest one that moves work forward):**
1. **[THE FLAGGED SPIKE — DO FIRST, do NOT skip] The corner `hr = ρ₀` composition spike.** Confirm,
   COMPILER-CHECKED (the §(4.91) refutation class, re-run for the corner-as-`ρ₀` shape), that the `_aug`
   corner's `inr ()` row — fed the discriminator's `ρ₀`/`hedgeGv` bundle through the eq.-(6.63) `Lrow`
   row-op — composes to the `−ρ₀` read SORRY-FREE with a ONE-SLOT genuine candidate (only `e_a ↦` free
   panel; no reproduced slot, no second edge). §(4.89) is strong evidence the `_aug` route needs no genuine
   `(v₀v₁)ᵢ*` corner edge (the `inr ()` slot reads `−ρ₀` directly, `L₀` a free unused arg, `C = 0`); the
   spike confirms it end-to-end against the one-slot candidate. **NAMED OPEN sub-question the spike
   resolves:** keep `vᵢ` (so a `(v₀v₁)ᵢ*`-analog row exists in `m₁`) vs the `_aug` `inr ()` route that needs
   no genuine corner edge. Do NOT declare GO from prose (§(4.90) lesson). Spike file deleted before commit.
2. **On GO:** build `chainData_dispatch` (the never-built router, case-split matched `i` on `(i:ℕ)`: base
   via `chainData_split_realization`, interior via the route-(a) arm) + the route-(a) arm restate
   `case_III_arm_realization_chain` (drops reproduced-slot hyps, feeds the cert from the one-slot candidate +
   `corner_hA_*_of_gate`). Wiring = the `ends₁`-override congruence + the approved C.3 `hIH`-fed
   `interior_hsplitGP`; below contract, NOT new math.
3. **Scope/estimate:** multi-commit, likely-multi-session (the dead override + `_ofNormals` siblings thread
   through 23c–23f and are discarded at the reshape). `d=3` stays on its separate `_matrix`/M₃ engine
   (untouched, green) regardless. SURVIVING infrastructure (read at `def`/`theorem` §(4.92)): the union-count
   `case_III_claim612_gen` (already general-`d`), the discriminator, the corner core `corner_hA'_of_gate`/
   `_aug`, the `_aug`/D-CAN literal-`R(Gab)` bottom, the LA backbones, D1 `interior_hsplitGP`.

Authoritative scoping: `notes/Phase23-design.md` §(4.92) (this session's verdict + diagnosis + decomposition
+ survives/discards inventory + the flagged spike), §(4.91) (the override refutation), §(4.90) (the
superseded GO).

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
