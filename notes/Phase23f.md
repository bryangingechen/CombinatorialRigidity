# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **(D-substitution) AUTHORIZED (user, 2026-06-28); BOTH make-or-break spikes DONE and
GO. S2 (the rank cert's two defeq faces, §(4.85)) AND S3 (the W6f realization-tail coupling, §(4.86)) are
KERNEL-CONFIRMED buildable. The next action is the S1 BUILD at the now-CONFIRMED shape: a PURE `ofNormals G
ends q` candidate (NO `t`-slot, NO override, NO `t`-layer) + a NEW simpler realization tail (the W6f shear is
NOT needed — it was an artifact of the override).** All six narrow geometry-arm routes (b / α / D / γ / β /
chain-edge-re-key) are decisively REFUTED — they reduce to ONE root: the project's `caseIIICandidate`
OVERRIDES the support extensors at two slots, creating an `hr : ±r-row ∈ span` obligation KT never has, and
rigidly pinning the reproduced-slot panel to the short-circuit `(vtx(i+1), vtx(i−1))` whose perp is FALSE for
the generic seed. The full refutation arc is recorded in design §§(4.77)–(4.83) + git; do NOT re-derive it.
**The ONE un-refuted route is (D-substitution)** (design §(4.84) scoping + §(4.85) S2-GO + §(4.86) S3-GO):
rebuild the candidate as a pure `ofNormals G ends q` on `G` (keeping `v`, `q := Q.normal`, NO override), so the
`±r` row is the genuine chain-edge `(vᵢvᵢ₊₁)`-row (`hr` discharged by the LANDED chain-edge perp
`baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640`) and the bottom is the literal `R(G,pᵢ)`
whose non-chain rows transport to `R(Gab)` via the **LANDED** D-canonical bottom bridge.

**S2 MAKE-OR-BREAK = GO (§(4.85), spike `SpikeDSubst.lean`, 5 probes SORRY-FREE).** Both faces compose:
(BOTTOM) the literal-`R(Gab)` submatrix bridge is **already LANDED** (D-canonical
`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387` + `blockBasisOn_congr` `:610`) — threading `Q` only
RE-DERIVES it; (CORNER) the genuine chain-edge `±r` row's membership reduces EXACTLY to the chain-edge-panel
perp the LANDED lemma delivers. The §(4.84) "S2 re-hits the §(4.70) PROBE-2a opaque-basis wall" was an OUTDATED
flag (that wall is dissolved by D-canonical). **S3 MAKE-OR-BREAK = GO (§(4.86), spike `SpikeDSubstS3.lean`, 7
probes A–G SORRY-FREE, `Build completed (2784 jobs)`, deleted).** The realization tail COMPOSES for a genuine
`ofNormals G ends q` cert — and is STRUCTURALLY SIMPLER: the W6f shear is NOT needed (it was an artifact of the
override's fictional candidate line, not an intrinsic need of the realization). PROBE G compiles the full
`hrank` (at the genuine framework) → motive composition end-to-end (`goals_after: []`): W6e re-extracts `F`'s
OWN panelRows (framework-general), they are LITERAL rigidity rows, `isInfinitesimallyRigidOn_vertexSet_of_
independent_rigidityRows` gives rigidity AT THE CERT FRAMEWORK, `hasGenericFullRankRealization_of_rigidOn_
ofNormals` upgrades to the motive — no `caseIIICandidate`, no `t`-family, no good-`t`. **The §(4.84.3)/(4.85.5)
"a pure-`ofNormals` candidate breaks the W6f `t`-family" was an over-PESSIMISTIC flag, corrected at the kernel
(symmetric to §(4.85)'s correction of the over-pessimistic "S2 re-hits PROBE 2a").** **STILL OPEN (FLAGGED,
the ONE remaining): S5** the C.3 dispatch-body reshape / motive-producer seam (thread `q := Q.normal`/`Q.ends`
consistently into candidate + bottom selector + surface the `Q`-conjuncts the genuine candidate's `hne`/`hends`
need) — a dispatch-wiring question, NOT a make-or-break (both S2 cert + S3 realization are kernel-confirmed).
(D-substitution) stays FAITHFUL (KT's eq. 6.59/6.61; Q1 the union-dimension half LANDED general-`k`) and below
the C.0–C.6 contract TYPES + 0-dof motive, crossing the C.3 SEAM in its body. Estimate **~7–13 commits**
(REVISED DOWN from ~9–17: S1+S2 core confirmed, S2 bottom largely landed, S3 now ~½–1 commit not ~2–4). The
geometry arm stays in 23f. `d=3` stays fully green (hard constraint). Authoritative recon:
`notes/Phase23-design.md` §(4.86) (the S3-GO verdict + the CONFIRMED S1 shape), on top of §(4.85) (S2-GO) +
§(4.84) (scoping/blast radius) + §§(4.77)–(4.83) (the route refutations). Program map:
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`); 23f built the geometry arm's cert
infrastructure (the interior-corner cert, the D-CAN bottom, the `_aug` ladder), then ran the route
refutations that found the dispositive blocker is the candidate-construction device itself. On (D-substitution)
landing (if authorized) the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**THE ROUTE IS (D-substitution), USER-AUTHORIZED (2026-06-28); BOTH S2 (§(4.85)) AND S3 (§(4.86)) MAKE-OR-BREAK
= GO; NEXT = THE S1 BUILD at the CONFIRMED shape** (a pure `ofNormals G ends q` candidate, NO `t`-slot, + the
NEW simpler realization tail = PROBE G's composition; the W6f shear is NOT needed). The six narrow routes are
all dead — verdict pointers only (full arc in design §§(4.77)–(4.83) + git):
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

**THE FORWARD PLAN — (D-substitution), design §(4.84) scoping + §(4.85) S2-GO + §(4.86) S3-GO:**
- **S2 make-or-break = GO (§(4.85), kernel-confirmed).** Both faces compose SORRY-FREE. (BOTTOM) the
  literal-`R(Gab)` submatrix bridge is **already LANDED** (`submatrix_columnOp_toBlocks₂₂_eq_Gab`
  `Concrete.lean:2387` + `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`); threading `Q` RE-DERIVES
  it. (CORNER) the genuine chain-edge `±r` row's membership reduces EXACTLY to the LANDED chain-edge-panel perp
  `baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`). The §(4.84) "S2 re-hits PROBE-2a" was
  OUTDATED (the wall is dissolved by D-canonical). The real blocker was the OVERRIDE, which (D-substitution)
  removes.
- **S3 make-or-break = GO (§(4.86), kernel-confirmed; the W6f shear is NOT needed).** The realization tail
  COMPOSES for a genuine `ofNormals G ends q` cert, and is SIMPLER than the override tail: PROBE G compiles
  `hrank` (at the genuine framework) → motive end-to-end SORRY-FREE (`goals_after: []`) via W6e
  (`exists_independent_panelRow_subfamily_of_le_finrank`, framework-general) → literal `hmem`
  (`panelRow_mem_rigidityRows`) → `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` →
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`. The §(4.84.3)/(4.85.5) "pure-`ofNormals` breaks the W6f
  `t`-family" was over-PESSIMISTIC: the shear was an artifact of the override's FICTIONAL candidate line (PROBE
  B.1), dissolved when the candidate is genuine. (Affine-in-`t` IS native to a pure-`ofNormals` seed-move
  family if ever needed — PROBES E/F — so a shape-(c) `t`-layer is a live fallback, but PROBE G shows it
  UNNEEDED.)
- **Q2 (blast radius, §(4.84.3)) — the ESCALATION FLAG (now narrowed to S5 only):** (D-substitution) is BELOW
  the C.0–C.6 contract TYPES + the 0-dof motive (no new motive conjunct, no IH-strength change, no `ChainData`
  field), BUT it CROSSES the C.3 motive/producer SEAM in its body — it replaces `caseIIICandidate`
  (`Candidate.lean:940`) with a pure-`ofNormals` candidate threading `q := Q.normal` (`Q` already
  `ofNormals`-concretized in the dispatch, `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`
  `Realization.lean:836`). The W6f-tail worry §(4.84.3) raised is GONE (§(4.86)); the seam is now JUST the
  dispatch-wiring (S5). **NAMED for user adjudication.**
- **Q3 (decomposition, §(4.84.4) refined by §(4.85.4)/(4.86.4)):** REUSED = Q1 union-count, the block-rank
  backbones, D1 `interior_hsplitGP`, the chain-edge perp, the corner-`hA` gate, **AND the entire bottom
  bridge**, **AND the framework-general realization closers** (`exists_independent_panelRow_subfamily_of_le_
  finrank`, `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`,
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`). NEW = **S1** the pure-`ofNormals` candidate (no new
  `def` — `ofNormals` IS it) + the genuine-`±r` membership leaf (`hingeRow_mem_ofNormals_rigidityRows_chainEdge`,
  ~5 lines, the §(4.86.4) skeleton); **S2** the cert wiring (mostly RE-WIRING — the literal-bottom bridge is in
  tree); **S3** the NEW simpler realization tail (PROBE G's ~10-line composition; **~½–1 commit, not the ~2–4
  estimated**); S4 cert assembly; **S5** the C.3 dispatch-body reshape (the one open seam, dispatch-wiring); S6
  CHAIN-5 + router. **~7–13 commits (REVISED DOWN from ~9–17); S1/S2/S3 all kernel-confirmed; S5 the one
  remaining open seam.**

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

- [→] **(D-substitution) — BUILD (§(4.84) scoping + §(4.85) S2-GO + §(4.86) S3-GO).** BOTH make-or-break
  spikes are kernel-confirmed GO; next is the **S1 BUILD at the CONFIRMED shape** (a pure `ofNormals G ends q`,
  NO `t`-slot). Ordered sub-commits:
  - [→] **S1 — the genuine-`±r` membership leaf (NO new candidate `def` — `ofNormals` IS the candidate).** The
    candidate is a pure `ofNormals G ends q` on `G` keeping `v`, `q := Q.normal`, NO override, NO `t`-slot, NO
    `t`-layer — the genuine `R(G,pᵢ)` of KT 6.59 (SHAPE (a), CONFIRMED by §(4.86), the S3 `t`-slot caveat
    DISSOLVED). The one new leaf: `hingeRow_mem_ofNormals_rigidityRows_chainEdge` (~5 lines, the §(4.86.4)
    skeleton) — the `±r` membership at the genuine chain-edge slot, `hperp` discharged by the LANDED chain-edge
    perp `baseRedundancy_perp_interior_reproduced_panel` (mind the orientation swap, §(4.86.4)). **De-risked by
    §(4.85.4)/(4.86.4); CHEAP** (`Q` already `ofNormals`-concretized in the dispatch). **~½–1 commit.**
  - [→] **S2 — the cert wiring** (the literal-`R(G,pᵢ)`-as-cert-matrix bridge). **The bottom bridge is ALREADY
    IN TREE** (`submatrix_columnOp_toBlocks₂₂_eq_Gab` + `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`); S2
    is mostly RE-WIRING the `_aug` cert (`case_III_rank_certification_aug`, framework-general) over the
    `ofNormals`-candidate, delivering `hrank` AT THE GENUINE `ofNormals G ends q` framework. **CONFIRMED-buildable
    (§(4.85)). ~1–2 commits.**
  - [→] **S3 — the NEW simpler realization tail (NOT `case_III_realization_of_rank`; that one is the override
    tail, KEPT for `d=3`/`caseIIICandidate`).** Build PROBE G's composition: W6e at the genuine `F` (framework-
    general `exists_independent_panelRow_subfamily_of_le_finrank`) → literal `hmem` (`panelRow_mem_rigidityRows`)
    → `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` → `hasGenericFullRankRealization_of_
    rigidOn_ofNormals`. **The W6f shear is NOT needed (§(4.86)). ~½–1 commit** (all off LANDED framework-general
    lemmas). CONFIRMED-buildable.
  - [→] **S4 — the cert assembly** over the S1 candidate + S2 wiring → the S3 tail. **~1–2 commits, modulo
    S1/S2/S3.**
  - [→] **S5 — the C.3 dispatch-body reshape** (thread `q := Q.normal`/`Q.ends` from the dispatch into the
    candidate + bottom selector consistently; surface `Q`'s GP/link-recording/alg-indep conjuncts the genuine
    candidate's `hne`/`hends`/discriminator need). **The ONE remaining open seam — dispatch-wiring, NOT a
    make-or-break (S2 cert + S3 realization both kernel-confirmed). USER ADJUDICATION. ~1–2 commits + the
    (approved) C.3 `hIH` add.**
  - [→] **S6 — CHAIN-5 + router** (the `Fin cd.d` dispatch; reuses §(4.79.1)'s composition skeleton
    re-pointed at S4). **~1–2 commits.**
  - **Build order:** S2 (§(4.85)) ✓ + S3 (§(4.86)) ✓ kernel-confirmed → **build S1** (the `±r` membership leaf,
    SHAPE (a) confirmed) → **S3-tail** (PROBE G's composition) → S2-wiring/S4 → S5 (the dispatch seam) → S6. (The
    coordinator re-ordered S3's SPIKE ahead of the S1 build per L5b — that spike is DONE, GO; S1 is now built at
    the confirmed shape with no dead-leaf re-wire risk.) **Gate:** full `lake build` green + `lake lint` clean +
    axiom-clean.

  A1–A5c (matrix model + column op + block-additivity backbones `Rank.lean:480/574/622`) + D1
  `interior_hsplitGP` ✓ LANDED and REUSED. The `_aug` ladder reuse is PROBABLE for the bottom, UNCERTAIN for
  the corner (the override-candidate's `rigidityMatrixEdgeAug` entry reads may differ under a `Q`-threaded
  candidate — not yet checked, §(4.84.4)). `_matrix`/`_rowOp`/chain dead arms stay landed-but-dead (αE6 retire
  DEFERRED to phase-close).

## Blockers / open questions

- **(D-substitution) AUTHORIZED (user, 2026-06-28) — staying in 23f; BOTH S2 (§(4.85)) AND S3 (§(4.86))
  make-or-break = GO.** All six narrow routes are REFUTED (the SAME root: the `caseIIICandidate` override
  creates the false-for-generic-`q` short-circuit `hr` perp KT never has, downstream of candidate selection).
  The route is the foundational re-architecture (D-substitution) — faithful (KT's actual eq. 6.59/6.61; Q1 the
  union-dimension half LANDED general-`k` `case_III_claim612_gen` `Claim612.lean:1333`). **S2 = GO** (§(4.85)):
  both faces compose SORRY-FREE — bottom already LANDED (D-canonical), corner's genuine chain-edge `±r`
  membership reduces to the LANDED chain-edge perp. **S3 = GO** (§(4.86)): the realization tail COMPOSES for a
  genuine `ofNormals G ends q` cert and is SIMPLER — the W6f shear is NOT needed (it was an artifact of the
  override's fictional candidate line); PROBE G compiles `hrank` → motive end-to-end SORRY-FREE. The §(4.84)
  "S2 re-hits PROBE-2a" AND the §(4.84.3)/(4.85.5) "pure-`ofNormals` breaks the W6f `t`-family" were BOTH
  over-pessimistic flags, corrected at the kernel. **The ONE residual is S5** (the C.3 dispatch-wiring seam,
  user adjudication — NOT a make-or-break). Est. ~7–13 commits (REVISED DOWN; S1/S2/S3 all confirmed). Full
  verdict: design §(4.86) (S3-GO + the CONFIRMED S1 shape); §(4.85) (S2-GO); scoping/blast radius §(4.84).
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

**THE NEXT ACTION IS THE S1 BUILD at the CONFIRMED shape** (BOTH make-or-break spikes are DONE — S2 GO §(4.85),
S3 GO §(4.86)). (D-substitution) is USER-AUTHORIZED (2026-06-28: "do the foundational re-architecture with any
recons/spikes necessary") and the geometry arm stays in 23f (not a new sub-phase). **The CONFIRMED S1 shape
(§(4.86.4), shape (a)):** a PURE `ofNormals G ends q` candidate on `G` keeping `v`, `q := Q.normal`, NO override,
**NO `t`-slot, NO `t`-layer** — the genuine `R(G,pᵢ)` of KT 6.59. The S3 spike (§(4.86)) DISSOLVED the
"does S1 need a `t`-slot for the W6f shear" worry: the shear was an artifact of the override's fictional
candidate line, and a genuine `ofNormals` cert realizes DIRECTLY (no shear) — so S1 needs no `t`-slot and the
realization tail is a NEW, simpler ~10-line composition (PROBE G), NOT the override's `case_III_realization_of_
rank`. **The smallest next commit:** the `±r` membership leaf `hingeRow_mem_ofNormals_rigidityRows_chainEdge`
(§(4.86.4) skeleton, ~5 lines: `Submodule.subset_span` of the genuine `e_a`-link, `hperp` discharged by the
LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640` — mind the
orientation swap) — then the S3 tail (PROBE G's composition), then the S2 cert re-wiring, then S4/S5/S6.
`Q` is already `ofNormals`-concretized in the dispatch (`exists_ofNormals_finrank_span_rigidityRows_eq_of_
hsplitGP` `Realization.lean:836`); the bottom bridge (S2 proper) is ALREADY IN TREE (§(4.85.2)). The ONE open
seam is S5 (the C.3 dispatch-wiring — thread `q`/`Q.ends` + surface the `Q`-conjuncts; user adjudication, NOT a
make-or-break). Authoritative recon: design §(4.86) (the S3-GO verdict + the CONFIRMED S1 shape + the leaf
skeleton), on top of §(4.85) (S2-GO).

**LANDED-FEASIBLE + REUSED under (D-substitution) (build only once the route is authorized; none touches `hr`):**
the Q1 union-count discriminator (`case_III_claim612_gen` `Claim612.lean:1333` + the moving-member pick
`exists_shared_redundancy_and_matched_candidate` `Realization.lean:1481`); the D-CAN bottom machinery
(`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387`, `bottom_selection_of_crossFramework_span_Gab`
`:2880`, `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`); the LANDED chain-edge perp
`baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`, the `hr`-discharger); the corner-`hA`
gate `corner_hA'_of_gate` (`Concrete.lean:810`, `e_r`-independent); D1 `interior_hsplitGP`
(`Realization.lean:758`, the `Q` source); the block-rank backbones (`Rank.lean:480/574/622`); the §(4.79.1)
dispatch composition skeleton (re-pointable at the S4 cert); **the framework-general realization closers the
S3 tail reuses verbatim (§(4.86)): `exists_independent_panelRow_subfamily_of_le_finrank` (`GenericityDevice.
lean:718`), `panelRow_mem_rigidityRows` (`Pinning.lean:116`), `isInfinitesimallyRigidOn_vertexSet_of_
independent_rigidityRows` (`CaseI.lean:1099`), `hasGenericFullRankRealization_of_rigidOn_ofNormals`
(`CaseI.lean:1478`).** The `_aug` ladder + 5c/5e reuse is RESOLVED for the corner too (§(4.85.4), cleaner
without the override accessor); the override realization tail `case_III_realization_of_rank` (`Arms.lean:63`) +
its shear are KEPT for the `d=3`/`caseIIICandidate` arms (NOT reused by D-substitution). The αE6 retirement of
the dead arms (`_matrix`/`_rowOp`/the dual-space chain arm + the route-(a)/route-α correct-but-unused leaves)
is DEFERRED to phase-close.

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

### (D-substitution) — the live route, S2 make-or-break = GO (design §(4.84) scoping + §(4.85) S2-spike)

- **AUTHORIZED + stay in 23f** (user, 2026-06-28): pursue the foundational re-architecture with any
  recons/spikes necessary; the geometry arm stays ONE sub-phase (23f closes ✓ when the arm lands — no new
  sub-phase, no renumber; ENTRY = 23g, ASSEMBLY = 23h unchanged). Next = the S1 build (BOTH S2 §(4.85) and S3
  §(4.86) are DONE, GO).
- **(D-substitution) = rebuild the candidate as a pure `ofNormals G ends q` on `G`, `q := Q.normal`, NO
  override** (KT eq. 6.59/6.61): the `±r` row is the genuine chain-edge `(vᵢvᵢ₊₁)`-row (`hr` discharged by the
  LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640`), the bottom is
  the literal `R(G,pᵢ)` keeping `v`, whose non-chain rows transport to `R(Gab)` via the LANDED D-canonical
  bottom bridge. `Q` is already `ofNormals`-concretized in the dispatch (`Realization.lean:836`).
- **S2 MAKE-OR-BREAK = GO (§(4.85), kernel-confirmed spike).** Both faces compose SORRY-FREE. The bottom bridge
  is ALREADY LANDED (D-canonical `submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387`); the genuine
  chain-edge `±r` membership reduces EXACTLY to the chain-edge-panel perp. **The §(4.84) "S2 re-hits the §(4.70)
  PROBE-2a opaque-basis defeq wall" was OUTDATED** — D-canonical's support-extensor-keyed `canonBlockBasis`
  (`Concrete.lean:213`) dissolved that wall (`blockBasisOn_congr` = `subst hsupp; rfl`); the §(4.70) residual
  was on the PRE-D-canonical opaque basis. The real blocker the six routes died on was the OVERRIDE (forcing
  the short-circuit-panel perp), NOT a defeq wall; (D-substitution) removes it.
- **S3 make-or-break = GO; the W6f shear is NOT needed** (§(4.86), kernel-confirmed spike `SpikeDSubstS3.lean`,
  7 probes A–G SORRY-FREE). The realization tail COMPOSES for a genuine `ofNormals G ends q` cert and is
  SIMPLER than the override tail: PROBE G compiles `hrank` (at the genuine framework) → motive end-to-end
  (`goals_after: []`) via W6e (framework-general) → literal `hmem` → `isInfinitesimallyRigidOn_vertexSet_of_
  independent_rigidityRows` → `hasGenericFullRankRealization_of_rigidOn_ofNormals`. The §(4.84.3)/(4.85.5)
  "pure-`ofNormals` breaks the W6f `t`-family" was over-PESSIMISTIC: the shear was an artifact of the override's
  FICTIONAL candidate line (PROBE B.1, `e_a` reads `panelSupportExtensor na n'` not a `q`-vertex normal),
  dissolved when the candidate is genuine. The CONFIRMED S1 shape is (a): pure `ofNormals`, NO `t`-slot, NO
  `t`-layer. (Affine-in-`t` IS native to a pure-`ofNormals` seed-move family — PROBES E/F — so a shape-(c)
  `t`-layer is a live fallback, but UNNEEDED.)
- **WHY IT IS STILL FOUNDATIONAL (Q2, narrowed to S5).** It crosses the C.3 motive/producer SEAM in its body:
  replace `caseIIICandidate` (`Candidate.lean:940`) with the `ofNormals`-candidate threading `q :=
  Q.normal`/`Q.ends` consistently into candidate + bottom selector + the (new, simpler) realization tail. The
  W6f-tail worry §(4.84.3) raised is GONE (§(4.86)); the seam is now JUST the C.3 dispatch-wiring — **S5, the
  ONE remaining open item** (a dispatch-wiring question, NOT a make-or-break). Below C.0–C.6 TYPES + 0-dof
  motive; NAMED for user adjudication.
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
