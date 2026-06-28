# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **AT A FOUNDATIONAL DECISION POINT (surfaced to user, session paused 2026-06-28).**
The §(4.90) recon recommends **GO via the LANDED `caseIIICandidate` OVERRIDE route**, REVERSING the 2026-06-28
(D-substitution) authorization — but the verdict is **UNVERIFIED** (prose, no composition spike) and
**CONTRADICTS the compiler-checked §(4.82)/(4.83) override refutations**, so the coordinator did NOT act on it.
The user stopped the loop to hand off to a fresh session. **First action next session: re-present the §(4.90)
decision (the recommended move = a decisive compiler-checked spike confirming the override dispatch composes,
BEFORE discarding the (D-substitution) work) — see *Hand-off*.** `d=3` stays fully green (hard constraint).
Authoritative recon: `notes/Phase23-design.md` §(4.90) (the override verdict + reuse map), §(4.84)–(4.89) (the
now-superseded (D-substitution) arc), §§(4.77)–(4.83) (the six route refutations). Program map:
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`). 23f built the geometry-arm cert
infrastructure (interior-corner cert, D-CAN bottom, the `_aug` ladder), refuted six narrow corner routes, then
spent a full session building the (D-substitution) re-architecture — which a final dispatch found is OFF-BY-ONE
at the corner. When the geometry arm closes, the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE DECISION (surfaced; do NOT pick unilaterally).** The §(4.90) recon (KT eqs. 6.46–6.67, adversarial; NO
spike) reads KT's `+1`-rank as a full-rank `D×D` corner `Mᵢ = [r(Lᵢ); ±r]` (eqs. 6.61/6.64/6.65) — the project's
`corner_hA'_of_gate` shape — but with the panel block on chain edge `vᵢvᵢ₊₁` (a FREE `(d−2)`-affine subspace via
the discriminator transversal `n'`) and the redundant `±r` on the SEPARATE chain edge `vᵢ₋₁vᵢ`. **Two distinct
edges.** The LANDED `caseIIICandidate` override implements exactly this; the discriminator
`exists_shared_redundancy_and_matched_candidate` co-chooses `(q, ρ₀, n')` so the corner gate `ρ₀(C(a,n')) ≠ 0`
AND the IH redundancy `ρ₀(C(ab)) = 0` hold simultaneously. **Verdict: finish the never-built override
`chainData_dispatch` `Fin cd.d` router on the LANDED `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`);
discard the (D-substitution) `_ofNormals` siblings (~2–4 commits, no new leaf).**

**WHY THE COORDINATOR DID NOT ACT ON IT (the caveat):** the verdict (a) reverses a user authorization, (b)
CONTRADICTS the compiler-checked §(4.82)/(4.83) refutations (which said the override's short-circuit perp is
"false for generic `q`" — the recon claims they examined an arbitrary `q`, not the discriminator-co-chosen seed),
and (c) was delivered as PROSE with no spike of the full override-dispatch composition (the override
`chainData_dispatch` was NEVER built — whether the `±r` `hr` + the corner gate + all hyps actually discharge
from the discriminator's seed is UNVERIFIED). The coordinator SOURCE-CONFIRMED only the pivotal landed fact:
`chainData_split_w6b_gates` (`Realization.lean:889`, conclusion `:919`) proves `ρ(C(ab)) = 0` for a
discriminator-chosen `ρ`. **A re-route claiming "the refuted route actually works" is the §(4.82) over-optimism
pattern — it needs compiler confirmation before the (D-substitution) work is discarded.**

**WHY (D-substitution) FAILED (the off-by-one, kernel-confirmed — row 598).** The `chainData_dispatch` build for
the genuine `ofNormals` candidate hit a contradiction: the corner `hA` needs the gate `ρ₀(F.supportExtensor e_a)
≠ 0` (`corner_hA'_of_gate` `Concrete.lean:810`), but the genuine candidate's only `v`-incident corner edges are
the chain edges (`F.supportExtensor e_a = panelSupportExtensor (q v)(q a)`), and the S1 `hr` membership needs
`ρ₀(F.supportExtensor e_a) = 0` (the chain-edge perp) — **same `ρ₀`, same panel, exact negation.** So `ρ₀` lies
in the `(D−1)`-dim panel block, `[blockBasisOn(e_a); ρ₀]` is dependent, the corner is rank `D−1`, off-by-one.
The genuine candidate COLLAPSED both corner conditions onto one chain edge; the override keeps them on two
separate edges (the free-panel degree of freedom), which is why §(4.90) says the override avoids it.

**LANDED INVENTORY (axiom-clean, gates green, `d=3` untouched):**
- **(D-substitution) bricks — LANDED but CONDITIONAL (the corner `hA` hyp is unsatisfiable for the collapsed
  candidate; §(4.90) recommends DISCARDING them):** S1 `hingeRow_mem_ofNormals_rigidityRows_chainEdge`
  (`ForkedArm.lean:621`); S2 `case_III_rank_certification_aug_ofNormals` (`Candidate.lean:2782`); S3
  `case_III_realization_of_rank_ofNormals` (`ForkedArm.lean:1238`); S4 `case_III_arm_realization_aug_ofNormals`
  (`ForkedArm.lean:1309`); the spine `chainData_arm_realization_ofNormals` (`Realization.lean:1769`); the corner
  leaf `chainData_arm_corner_hA_ofNormals_of_gate` (`:1840`); the `C≠0` read `submatrix_columnOp_toBlocks₁₁_sub_
  mul_toBlocks₂₁_aug_eq_coordEquiv`. These are CORRECT conditional lemmas (they fire IF the corner `hA` is
  supplied); the `hA` is what's unsatisfiable. → phase-close/discard cleanup if the override route is confirmed.
- **Reusable for BOTH arms (genuinely landed + satisfiable):** the discriminator `case_III_claim612_gen`
  (`Claim612.lean:1333`) + `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:1481`/`:2134`) +
  `chainData_split_w6b_gates` (`:889`); the `_aug` block-data bricks 5c `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_
  toBlocks₂₂` + 5e `exists_aug_bottom_blockData_of_Gab` (`Concrete.lean`); the D-CAN bottom machinery
  (`submatrix_columnOp_toBlocks₂₂_eq_Gab` `:2387`); the block-rank backbones (`Rank.lean:480/574/622`); D1
  `interior_hsplitGP` (`Realization.lean:758`).
- **The OVERRIDE route's pieces (LANDED; §(4.90) says these are the route):** the override spine
  `chainData_arm_realization_aug_zero₁₂` (`:1625`); the override corner `chainData_arm_corner_hA_of_discriminator_
  gate` (`:1761`); the override `±r` membership `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` ←
  `interior_hρe₀_of_widening` (the relabelled-seed perp). What is NOT built: the `chainData_dispatch` `Fin cd.d`
  router that fires the override spine per `i` off the discriminator.

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

**The LIVE forward plan hinges on the §(4.90) decision (the override route, UNVERIFIED) — see *Hand-off*.**

- [→] **THE DECISIVE OVERRIDE-COMPOSITION SPIKE (recommended next, §(4.90)).** Does the never-built override
  `chainData_dispatch` compose for the discriminator-co-chosen `(q, ρ₀, n')` — i.e. do the override spine
  `chainData_arm_realization_aug_zero₁₂`'s hypotheses (the `±r` `hr` via `hingeRow_mem_caseIIICandidate_rigidity
  Rows_reproduced` ← `interior_hρe₀_of_widening`; the corner gate via `chainData_arm_corner_hA_of_discriminator_
  gate`; `hB`/`L₀`/bottom via 5c/5e; `hM'eq`) all discharge from `exists_shared_redundancy_and_matched_candidate`
  + `chainData_split_w6b_gates`? Compiler-checked (the contradiction with §(4.82)/(4.83) makes prose unreliable).
  **If GO → build the override dispatch (below). If REFUTED → §(4.82)/(4.83) stand; back to the cert-architecture
  question.**
- [→] **The override `chainData_dispatch` build (~2–4 commits, only if the spike GO's).** Fire the discriminator
  ONCE at the base `v₁`-split → `(ρ₀, matched i, n')`; per `i` construct the override block data + fire the
  override spine; case-split on `(i : ℕ)` (base/floor via `chainData_split_realization`, interior via the
  override arm). Lands with the APPROVED C.3 `hIH` add. Then CHAIN-5 + the `cd` producer → 23g/ENTRY (option A).
  DISCARD the (D-substitution) `_ofNormals` siblings (the *Current state* inventory).
- [x] **(D-substitution) S1–S5 + spine + 5c/5e/5f.hA/5f.hAeq — LANDED but CONDITIONAL** (the corner `hA` hyp is
  unsatisfiable for the collapsed candidate; §(4.90) recommends discard). Detail: *Current state* inventory +
  design §(4.84)–(4.89) + git. The make-or-break spikes (§(4.85) S2, §(4.86) S3, §(4.87) S2-shape, §(4.88) S5,
  §(4.89) `L₀`/`hφ`) all returned GO by ABSTRACTING the corner gate as a free hypothesis; the dispatch (sourcing
  it) found it unsatisfiable (row 598). The GO-cascade lesson is in *Promoted to* below.
- [x] **A1–A5c backbones + D1 `interior_hsplitGP` + the route-refutation LA cores** — LANDED, REUSED/dead-but-
  correct. `_matrix`/`_rowOp`/chain dead arms + the (D-substitution) conditional bricks + the `C≠0` orphan
  5f.hAeq → αE6 retirement DEFERRED to phase-close (or the override-route landing).

## Blockers / open questions

- **THE §(4.90) GO-via-override verdict is UNVERIFIED + reverses the (D-substitution) authorization — USER
  ADJUDICATION (surfaced, session paused).** It contradicts the compiler-checked §(4.82)/(4.83) refutations;
  the coordinator confirmed only `chainData_split_w6b_gates:919 ⊢ ρ(C(ab))=0`. The recommended resolution is the
  decisive override-composition spike (above) BEFORE acting. The next coordinator re-presents this to the user.
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

**FIRST ACTION NEXT SESSION: re-present the §(4.90) decision to the user, then run the recommended decisive
spike.** The §(4.90) recon recommends abandoning the (D-substitution) detour and finishing the LANDED override
route — but the coordinator did NOT act on it because it's unverified prose that reverses a user authorization
and contradicts the §(4.82)/(4.83) refutations (the user stopped the loop here to hand off). The disciplined
path:

1. **Re-present the reversal to the user** (it reverses their 2026-06-28 (D-substitution) authorization). Options
   the prior coordinator framed: (A) run a decisive compiler-checked spike that the override `chainData_dispatch`
   composes for the discriminator-co-chosen seed [RECOMMENDED — confirms the reversal before discarding the
   (D-subst) work]; (B) trust the recon and build the override dispatch directly; (C) the user reviews §(4.90)
   vs §(4.82)/(4.83) themselves (the contradiction between compiler-checked recons is worth their eyes).
2. **The decisive spike (option A) settles it:** does the override spine `chainData_arm_realization_aug_zero₁₂`
   FIRE when fed the discriminator's `(q, ρ₀, n')` (`exists_shared_redundancy_and_matched_candidate` +
   `chainData_split_w6b_gates`)? Specifically, do the override's `±r` `hr` (`hingeRow_mem_caseIIICandidate_
   rigidityRows_reproduced` ← `interior_hρe₀_of_widening`) AND the corner gate (`chainData_arm_corner_hA_of_
   discriminator_gate`, gate at the FREE panel `(q a, n')`) BOTH discharge from the SAME discriminator-chosen
   seed? The §(4.82)/(4.83) refutations say no; §(4.90) says yes (they examined an arbitrary `q`). A
   compiler-checked spike (build the dispatch composition, `sorry` peripheral, read the kernel residual) is
   decisive. → §(4.90) carries the reuse map + the build plan.
3. **If the spike GO's:** build the override `chainData_dispatch` (~2–4 commits + the C.3 `hIH` add); discard the
   (D-substitution) `_ofNormals` siblings; then CHAIN-5 + the `cd` producer → 23g/ENTRY (option A — 23f closes
   at the `cd`-taking dispatch). **If the spike REFUTES:** the §(4.82)/(4.83) refutations stand, the off-by-one
   corner obstruction is real for BOTH arms, and the cert-architecture question (KT's actual `+1` mechanism) is
   genuinely open → STOP-for-user (shelve vs a deeper cert rethink).

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
