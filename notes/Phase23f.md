# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress, **BLOCKED on a USER-ADJUDICATION DECISION, not a build.** All six narrow
geometry-arm routes (b / α / D / γ / β / chain-edge-re-key) are decisively REFUTED — they reduce to ONE
root: the project's `caseIIICandidate` OVERRIDES the support extensors at two slots, creating an
`hr : ±r-row ∈ span` obligation KT never has, and rigidly pinning the reproduced-slot panel to the
short-circuit `(vtx(i+1), vtx(i−1))` whose perp is FALSE for the generic seed. The full refutation arc is
recorded in design §§(4.77)–(4.83) + git; do NOT re-derive it. **The ONE un-refuted route is
(D-substitution)** (design §(4.84), scoped this session): rebuild the candidate's non-chain + reproduced
rows as LITERAL rows of the IH framework `Q` (KT's eq. 6.59/6.61 substitution `pᵢ(e)=q₁(e)` + the 6.61
column op), so the `±r` row is the literal chain-edge `(vᵢvᵢ₊₁)`-row (`hr` automatic / discharged by the
LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640`) and the bottom
is the literal `R(G,pᵢ)`. **(D-substitution) is FAITHFUL (KT's actual argument is sound; Q1 the
union-dimension half is LANDED general-`k`) but a GENUINE FOUNDATIONAL CHANGE** — it forces the candidate to
thread the existential opaque IH framework `Q` (the C.3 dispatch's base seed), which (a) breaks the
closed-form `t`-family the W6f shear realization-tail rests on, and (b) re-confronts the §(4.70) PROBE-2a
opaque-`blockBasisOn`-defeq wall for the `v`-incident `±r` corner row (D-canonical fixed this for the BOTTOM
but not a corner row keyed on `v ∉ V(Gab)`). Estimate **~9–17 commits**, with the make-or-break **S2** (the
`Q`-threaded literal-bottom bridge) and the **S3** W6f-shear coupling NOT yet kernel-confirmed.
**The next action is a DECISION** (authorize the foundational re-architecture, S2 spiked first) or shelve the
geometry arm — NOT a build. `d=3` stays fully green (hard constraint). Authoritative recon:
`notes/Phase23-design.md` §(4.84) (feasibility + blast radius + S1–S6 decomposition), on top of §(4.82)/(4.83)
(the route refutations) and §(4.70.4) (the (D-canonical)/(D-substitution) foundational-change naming).
Program map: `notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`); 23f built the geometry arm's cert
infrastructure (the interior-corner cert, the D-CAN bottom, the `_aug` ladder), then ran the route
refutations that found the dispositive blocker is the candidate-construction device itself. On (D-substitution)
landing (if authorized) the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE ROUTE IS (D-substitution); THE PHASE IS BLOCKED ON A USER DECISION (§(4.84)).** The six narrow routes
are all dead — verdict pointers only (full arc in design §§(4.77)–(4.83) + git):
- **routes (b)/(α)** — DEAD (§(4.77): the corner 3-normal-LI `_escape` side-condition is false for reachable joins).
- **route (D)** (the `_aug` ladder on the D-canonical pin-zero bottom) — DEAD (§(4.80): `hr` re-hits the
  §(4.73.2) seam; the discriminator's `hedgeGv` yields the chain-edge panel, not the short-circuit panel).
- **route (γ)** (re-derive the spliced perp) — DEAD (§(4.81): needs a degree-2 coplanarity false for generic `q`).
- **route (β)** (swap the discriminator for KT's union-count) — DEAD as a finish line (§(4.82): Q1 the
  union-dimension half is LANDED, but (β) only re-selects WHICH `i`; the false `hr` is downstream, in the
  `caseIIICandidate` override — (β) relocates it, does not remove it).
- **narrow chain-edge-re-key** — DEAD (§(4.83): the reproduced-slot panel and the bottom split edge `e₀`
  are a SHARED `(a,b)` binding through `splitOff`; re-keying fixes `hr` but un-matches the bottom; the
  chain-edge second normal is the deleted `v ∉ V(Gab)`. The re-key IS (triggers) (D-substitution)).

**THE FORWARD PLAN — (D-substitution), design §(4.84) (scoped this session):**
- **Q1 (feasibility, §(4.84.2)):** the literal-row cert DOES discharge `hr` mathematically (via the LANDED
  chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640`, conclusion at the
  chain-edge panel `(q(vtx i+1), q(vtx i))`, second normal `q(vtx i) = q(v)`). But it is NOT constructible as
  a below-architecture tweak: the IH hands an EXISTENTIAL OPAQUE `Q` (`HasGenericFullRankRealization`,
  `PanelHinge.lean:1035`, no literal `R(Gab)` matrix — §(4.70) PROBE 1), and the literal `±r`-row identity
  re-hits the opaque-`blockBasisOn`-defeq wall (§(4.70) PROBE 2a) — which D-canonical solved for the BOTTOM
  (support-extensor-keyed basis) but NOT for a corner row keyed on `v ∉ V(Gab)` (§(4.83) PROBE E).
- **Q2 (blast radius, §(4.84.3)) — the ESCALATION FLAG:** (D-substitution) is BELOW the C.0–C.6 contract
  TYPES + the 0-dof motive (no new motive conjunct, no IH-strength change, no `ChainData` field), BUT it
  CROSSES the C.3 motive/producer SEAM in its body — it re-architects `caseIIICandidate` (`Candidate.lean:940`)
  to thread the existential `Q`, which breaks the closed-form `t`-family the W6f shear realization-tail
  `case_III_realization_of_rank` (`Arms.lean:63`) rests on (the pervasive `F₀`/`Ft`/`caseIIICandidate_exists_good_shear`
  usage), and re-shapes the dispatch body's `Q`-usage from "read finrank" to "build the candidate from `Q`".
  **This is a genuine foundational change, NAMED for user adjudication — not a clean below-contract reshape.**
- **Q3 (decomposition, §(4.84.4)):** REUSED = Q1 union-count, the block-rank backbones, D1 `interior_hsplitGP`,
  the chain-edge perp, the corner-`hA` gate (all unchanged); the `_aug` ladder + 5c/5e reuse is PROBABLE for
  the bottom, UNCERTAIN for the corner. NEW = S1 the `Q`-threaded candidate def (HIGH RISK, foundational core);
  **S2 the literal-`R(G,pᵢ)`-as-cert-matrix bridge (NEW-MATH, the make-or-break — spike FIRST)**; S3 the W6f
  realization-tail re-statement (OPEN: does the `Q`-threaded candidate admit the `t`-linear shear?); S4 the
  cert wiring; S5 the C.3 dispatch-body reshape (the motive/producer-seam crossing); S6 CHAIN-5 + router.
  **~9–17 commits; at least S1/S2/S3/S5 carry uncompiled feasibility risk.**

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean + SATISFIABLE; 23f only *produces*
  its block data. Build against the literal `Lrow * M * U` product, NOT the component leaves in isolation
  (the §(4.46)/(4.54) lesson — compiler-check the FULL composition before declaring "remaining = assembly").
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the general-`d` arm
  routes through the general-`d` cert. Do NOT unify the two. (The reproduced→chain-edge panel coincidence is
  a `d=3` single-swap `shiftPerm 2` body-rename; the seam is a `d ≥ 4`-only phenomenon, §(4.83).)
- **Below the CHAIN↔ENTRY contract TYPES + the motive/IH.** The geometry arm + dispatch are below the C.0–C.6
  signatures and the 0-dof motive. (D-substitution) crosses the C.3 motive/producer SEAM in its body (Q2) but
  does NOT change the contract types or the motive strength — see §(4.84.3) for the precise escalation flag.

## Lemma checklist

**The LIVE forward plan is the §(4.84) (D-substitution) S1–S6 sequence — BLOCKED on a user decision (not a build).**

**Route-(α)/(D) `_aug`/`_rowOp`/chain-arm ladders — LANDED-but-DEAD** (the interior-corner strategies the
refutations killed; settled detail in git + design §§(4.66)/(4.77)–(4.83)). REUSED-under-any-re-architected-cert
items are tracked in *Still-live*.

- [→] **(D-substitution) — BUILD (§(4.84)), BLOCKED on user adjudication.** Ordered sub-commits:
  - [→] **S1 — the `Q`-threaded candidate def** (a new `caseIIISubstCandidate` / a `Q`-taking reshape of
    `caseIIICandidate`). Build the candidate on `G` (keeping `v`) whose non-chain edges carry `Q`'s support
    extensors (KT 6.59) + the two genuine chain-edge rows. **HIGH RISK, foundational core; signature not
    de-risked. ~2–4 commits** (a foundational def + its accessor API, the analogue of `Candidate.lean:940`–`1191`).
  - [→] **S2 — the literal-`R(G,pᵢ)`-as-cert-matrix bridge** (KT 6.61): the operated S1-candidate matrix
    `= fromBlocks Mᵢ 0 ∗ R(Gab)` with `R(Gab)` the LITERAL `Q` matrix. **NEW-MATH, the make-or-break** — the
    §(4.69.6)(1)/§(4.70) PROBE-2a-blocked bridge; with S1 threading `Q`'s OWN basis (bottom rows ARE `Q`'s
    rows, no cross-framework basis equality) it MAY become provable. **SPIKE THIS FIRST. ~2–3 commits.
    FLAGGED feasibility-unknown.**
  - [→] **S3 — the W6f realization-tail re-statement** over the new candidate (`case_III_realization_of_rank`
    `Arms.lean:63` + the shear `caseIIICandidate_exists_good_shear`/`_panelRow_eq_add_smul`). **OPEN: does the
    `Q`-threaded candidate admit the `t`-linear shear? ~2–4 commits. FLAGGED.**
  - [→] **S4 — the cert wiring** over the S1 candidate + S2 bridge → the tail (S3); reuses the block-rank
    backbones + the chain-edge perp for `hr` (now automatic). **~1–2 commits, modulo S1/S2/S3.**
  - [→] **S5 — the C.3 dispatch-body reshape** (thread `Q` from the dispatch `obtain` into the candidate;
    surface `Q`'s GP/link-recording/alg-indep conjuncts). **The motive/producer-seam crossing — USER
    ADJUDICATION. ~1–2 commits + the (approved) C.3 `hIH` add.**
  - [→] **S6 — CHAIN-5 + router** (the `Fin cd.d` dispatch; reuses §(4.79.1)'s composition skeleton
    re-pointed at S4). **~1–2 commits.**
  - **Build order:** SPIKE S2 first (the make-or-break); only if confirmed build S1's full def; S3's
    shear-coupling spike next; then S4/S5/S6. **Gate:** full `lake build` green + `lake lint` clean + axiom-clean.

  A1–A5c (matrix model + column op + block-additivity backbones `Rank.lean:480/574/622`) + D1
  `interior_hsplitGP` ✓ LANDED and REUSED. The `_aug` ladder reuse is PROBABLE for the bottom, UNCERTAIN for
  the corner (the override-candidate's `rigidityMatrixEdgeAug` entry reads may differ under a `Q`-threaded
  candidate — not yet checked, §(4.84.4)). `_matrix`/`_rowOp`/chain dead arms stay landed-but-dead (αE6 retire
  DEFERRED to phase-close).

## Blockers / open questions

- **THE PHASE IS BLOCKED ON A USER DECISION (§(4.84)).** All six narrow routes are REFUTED (the SAME root:
  the `caseIIICandidate` override creates the false-for-generic-`q` short-circuit `hr` perp KT never has,
  downstream of candidate selection). The only un-refuted route is **(D-substitution)** — faithful (KT's
  actual eq. 6.59/6.61; Q1 the union-dimension half LANDED general-`k` `case_III_claim612_gen`
  `Claim612.lean:1333`), but a GENUINE FOUNDATIONAL CHANGE: it threads the existential opaque IH framework `Q`
  into the candidate, breaking the W6f shear realization-tail and re-confronting the §(4.70) PROBE-2a
  opaque-basis wall for the `v`-incident `±r` corner row. **Decision for the user:** authorize the
  ~9–17-commit re-architecture (S2 spiked first, S1/S2/S3/S5 feasibility uncompiled) or shelve the geometry
  arm. NOT a build until adjudicated. Full verdict: design §(4.84).
- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; lands with
  the C.3 dispatch reshape, S5). The interior arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`),
  derivable only from `hIH` via `splitOff_isMinimalKDof` — D1 `interior_hsplitGP` ✓ LANDED; the C.3
  consume-shape gets the `hIH` field added when the dispatch is wired (a one-bundle add touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change). Context: §(4.43) + §C.3 + §(4.79.4).
  Distinct from the (D-substitution) `Q`-threading (Q2/S5), which is the new escalation.
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with the dispatch.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe (independent
  of the (D-substitution) decision — it owns the chain/cycle dichotomy + the `hD`-floor lift, not the cert).

## Hand-off / next phase

**THE NEXT ACTION IS A USER DECISION, NOT A COMMIT.** Every narrow route is refuted; (D-substitution) is the
one un-refuted route and a foundational re-architecture. The scoping is DONE (design §(4.84)). The user
adjudicates one of:
- **Authorize (D-substitution).** Then the smallest concrete first move is **the S2 kernel spike** (NOT a
  build): does threading `Q`'s own basis into a `Q`-dependent candidate make the literal
  `R(G,pᵢ) = fromBlocks Mᵢ 0 ∗ R(Gab)`-bottom-submatrix bridge provable, sidestepping the §(4.70) PROBE-2a
  opaque-basis defeq failure? S2 is the make-or-break; S1's full def is built only if S2 confirms. (Honest
  unknown: whether S2 confirms is not predictable from prose — it is exactly what the spike settles.)
- **Shelve the geometry arm** (keep `d=3` green; the general-`d` interior arm stays the one open node).

**LANDED-FEASIBLE + REUSED under (D-substitution) (build only once the route is authorized; none touches `hr`):**
the Q1 union-count discriminator (`case_III_claim612_gen` `Claim612.lean:1333` + the moving-member pick
`exists_shared_redundancy_and_matched_candidate` `Realization.lean:1481`); the D-CAN bottom machinery
(`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387`, `bottom_selection_of_crossFramework_span_Gab`
`:2880`, `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`); the LANDED chain-edge perp
`baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`, the `hr`-discharger); the corner-`hA`
gate `corner_hA'_of_gate` (`Concrete.lean:810`, `e_r`-independent); D1 `interior_hsplitGP`
(`Realization.lean:758`, the `Q` source); the block-rank backbones (`Rank.lean:480/574/622`); the §(4.79.1)
dispatch composition skeleton (re-pointable at the S4 cert). The `_aug` ladder + 5c/5e reuse is PROBABLE for
the bottom, UNCERTAIN for the corner (§(4.84.4)). The αE6 retirement of the dead arms (`_matrix`/`_rowOp`/the
dual-space chain arm + the route-(a)/route-α correct-but-unused leaves) is DEFERRED to phase-close.

## Decisions made during this phase

### The route refutations (verdicts only; full blow-by-blow in design §§(4.77)–(4.84) + git)

- **routes (b)/(α) DEAD** (§(4.77)): the corner 3-normal-LI `_escape` side-condition `∃ i, p i ⬝ᵥ q b ≠ 0`
  is provably false for reachable matched joins. The LA core `exists_independent_perp_family_escape`
  (`Claim612.lean`) is correct-but-unused (consumer feasibility, not LA shape, was the wall).
- **route (D) DEAD** (§(4.80)): the `_aug` ladder on the D-canonical pin-zero bottom fires the corner `hA`
  from the discriminator gate alone (PROBE 4/5, the `−ρ₀` v-pin read), but `hr` re-hits the §(4.73.2) seam —
  the discriminator's `hedgeGv` widening yields the DIRECT-`q` CHAIN-EDGE panel `(vtx(i+1), vtx i)`, never
  the short-circuit `(vtx(i+1), vtx(i−1))` the direct-`q` augmented candidate demands. The two framings
  (direct-`q` for `hA`, relabel-`q` for the landed short-circuit perp) are mutually exclusive.
- **route (γ) DEAD** (§(4.81)): the short-circuit perp IS derivable from the chain-edge perp by ONE
  bilinearity step (`panelSupportExtensor` IS bilinear/alternating — the §(4.80) "nonlinear" reason was
  WRONG), but the step needs a degree-2 coplanarity `m = α'•a + β'•b` provably FALSE for the generic seed.
  USEFUL BYPRODUCT: `pse_add_right`/`pse_smul_right`/`pse_self` (would land under any panel-meet route).
- **route (β) DEAD as a finish line** (§(4.82)): Q1 (union-dimension `dim span(⋃ C(Lᵢ)) = D ⟹ ∃ i,
  ρ₀(C(Lᵢ)) ≠ 0`) is FULLY LANDED general-`k` (`case_III_claim612_gen`); but Q2 (make-or-break) is NEGATIVE —
  the false `hr` is introduced by the `caseIIICandidate` extensor-OVERRIDE (the §(4.69.2) divergence KT does
  not have), DOWNSTREAM of selection, so swapping the discriminator for the union-count RELOCATES it
  unchanged. KT's `±r` is the LITERAL chain-edge `(vᵢvᵢ₊₁)`-row of a GENUINE framework (eq. 6.64, NO `hr`).
- **narrow chain-edge-re-key DEAD** (§(4.83)): the reproduced-slot panel `(a,b)` and the bottom split edge
  `e₀=(a,b)` are the SAME `(a,b)` by construction (rigidly coupled through `splitOff`, which short-circuits
  the surviving neighbours `a=vtx(i+1)`, `b=vtx(i−1)` of the deleted `v=vtx i`). Re-keying the reproduced
  slot to the chain edge FIXES `hr` (PROBE D) but UN-MATCHES the bottom `hsupp` (PROBE B/C, the same false
  coplanarity), and the chain-edge second normal IS the deleted `v ∉ V(Gab)` (PROBE E). The re-key IS
  (triggers) (D-substitution).

### (D-substitution) — the live route (design §(4.84); scoped this session, no fresh spike — the make-or-break was kernel-settled by §(4.70) PROBE 1/2a + §(4.83) PROBE E)

- **(D-substitution) = rebuild the candidate's non-chain + reproduced rows as LITERAL rows of the IH
  framework `Q`** (KT eq. 6.59/6.61): the `±r` row becomes the literal chain-edge `(vᵢvᵢ₊₁)`-row (`hr`
  automatic / discharged by the LANDED chain-edge perp), the bottom becomes the literal `R(G,pᵢ)` (keeping
  `v`). The discharging perp `baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`) is in tree.
- **WHY IT IS FOUNDATIONAL (Q1b/Q2, the constructibility verdict).** The IH hands an EXISTENTIAL OPAQUE `Q`
  (`HasGenericFullRankRealization`, `PanelHinge.lean:1035`) — no literal `R(Gab)` matrix; `Q`'s
  `normal`/`ends`/`blockBasisOn` are all `∃`-chosen (§(4.70) PROBE 1, `rfl`). So the candidate must thread
  `Q`, which (a) breaks the closed-form `t`-family the W6f shear tail rests on (`case_III_realization_of_rank`
  `Arms.lean:63` uses `caseIIICandidate`/`Ft`/`caseIIICandidate_exists_good_shear` pervasively), and (b)
  re-confronts the §(4.70) PROBE-2a opaque-`blockBasisOn`-defeq wall for the `v`-incident `±r` corner row —
  D-canonical solved this for the BOTTOM (`canonBlockBasis`, `submatrix_columnOp_toBlocks₂₂_eq_Gab`) but NOT
  for a corner row keyed on the chain-edge panel whose second normal is `v ∉ V(Gab)` (§(4.83) PROBE E).
- **The cert object must change shape.** Because the `±r` chain-edge row is `v`-incident and `v ∉ V(Gab)`,
  the cert's bottom CANNOT be the `v`-free `R(Gab)` (the D-canonical bottom) — it must be the literal
  `R(G,pᵢ)` keeping `v`, KT's actual 6.59/6.61 object. A fundamentally different cert from the LANDED
  `(caseIIICandidate …).rigidityRows`-span-bound cert + the `R(Gab)` bottom.
- **Blast radius CROSSES the C.3 motive/producer SEAM** (Q2, the escalation flag): below the contract TYPES +
  the 0-dof motive, but it re-architects `caseIIICandidate`, threads `Q` through candidate + cert + W6f tail,
  and re-shapes the dispatch body's `Q`-usage. NAMED for user adjudication, not forced.

### (D-canonical) — the LANDED bottom machinery (kept; the BOTTOM half of any literal-IH cert; design §(4.71)/(4.72))

- **(D-canonical) re-keyed `blockBasisOn` on the support extensor** (`canonBlockBasis`/`canonBlock` +
  `_congr`), making the cross-framework basis equality PROVABLE and transportable to the literal `Matrix`-row
  equality `submatrix_columnOp_toBlocks₂₂_eq_Gab` (`Concrete.lean:2387`) — so the (C) bottom is the literal
  IH matrix `R(Gab)` full rank (`linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`). This SOLVES
  the §(4.70) PROBE-2a wall FOR THE BOTTOM. The D-CAN-4 feeders (`hsupp`/`hgp`/`Gab`-bottom/`hfr₂`) are all
  GATE-FREE (§(4.72)). **This is the BOTTOM half (D-substitution) reuses** — but the CORNER `±r` row still
  needs the foundational change (the bottom trick does not extend to a `v`-incident row, §(4.84.2)).
- **D1 `interior_hsplitGP`** (`Realization.lean:758`) = the IH full-rank `R(Gab)` (the `Q` source), taking
  the all-`k` `hIH` (`splitOff_isMinimalKDof` + simplicity + `splitOff_vertexSet_ncard_lt`). Consumes the C.3
  `hIH` add. LANDED, REUSED.

### Promoted to FRICTION / TACTICS-QUIRKS / DESIGN
- **The §(4.62) durable lesson — route-composition satisfiability must be COMPILER-CHECKED, not prose-argued**
  (the deferred-hypothesis-satisfiability trap; fired §(4.62)/(4.65)/(4.66.F)/(4.70)/(4.74)/(4.80), and the
  recon-before-build rule that caught the D-CAN-2 `hsupp` deferral at §(4.72)). → FRICTION; DESIGN.md
  *Constructibility recon*.
- **`set`-folding a carried hypothesis's heavy type breaks the downstream `exact`/whnf match** → TACTICS-QUIRKS
  § 43. **`ℤ→ℕ` cast-subtraction (`push_cast`/`ring` leaves a `.pred`)** → the explicit `Nat.cast_mul`/`Nat.cast_sub`
  route, TACTICS-QUIRKS §47.
- **A projecting argument-lambda fed to an implicit-domain parameter needs a binder type ascription** (the
  `cols` arg of `matrix_eq_mul_of_dual_row_comb`) → FRICTION *[idiom] Feeding …'s `cols`*.
- **Case-splitting an *applied* `Equiv`/function value the goal still mentions: `cases h : f x`, not
  `rcases f x`** (sub-commit-4 `reAug_injective` cross-disjointness) → FRICTION *[idiom] case-splitting …*.
