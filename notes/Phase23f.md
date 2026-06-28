# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **(D-substitution) AUTHORIZED (user, 2026-06-28); ALL THREE make-or-break/shape spikes
DONE and GO; S1 + S2 + S3 + S4 ALL LANDED (2026-06-28): S1 the genuine-`±r` membership leaf, S2 the cert wrapper
`case_III_rank_certification_aug_ofNormals`, S3 the realization tail, S4 the arm assembly
`case_III_arm_realization_aug_ofNormals` (`ForkedArm.lean:1309`, axiom-clean, gates green — the kernel-de-risked
clean assembly §(4.87) predicted, clean first pass).** **The S5 dispatch-wiring interface is now KERNEL-SETTLED
(§(4.88), spike `SpikeDSubstS5.lean`, 4 probes — the interface map SORRY-FREE): S5 is a CLEAN BUILD under the
standing authorizations, NO fresh adjudication. The S4 arm FIRES from the genuine candidate's conjuncts (PROBE 1);
each non-block hypothesis is SOURCED — `hgp` from the discriminator's GP via the GRAPH-FREE `IsGeneralPosition`
(PROBE 2), `hr` from the S1 leaf ← the LANDED chain-edge perp (PROBE 3), the `obtain` chain off `hsplitGP` (PROBE
4). The §(4.86.5) "open interface question" is answered YES — the 0-dof motive + the approved `hIH` supply every
`Q`-conjunct the candidate needs. The S5 BUILD is now started: **(5c) the ONE genuinely-new matrix brick — the
augmented `hB`/`L₀` factoring `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` (+ its prerequisite
`_toBlocks₂₂_aug_eq_mixedBottom`) — LANDED 2026-06-28** (`Concrete.lean`, axiom-clean, gates green, clean first
pass). Next = (5e) the `re`/`hre`/`L₀` + bottom assembly, then (5f) the dispatch body + C.3 `hIH` add + CHAIN-5
(~1–2 commits).** The
wrapper `case_III_rank_certification_aug` IS
`caseIIICandidate`-hard-wired (the coordinator's read confirmed), BUT the framework-general object is one level
down (`finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` `Concrete.lean:1258`, abstract `F`), so
the swap is a thin RE-STATEMENT calling the same backbone — a CLEAN ASSEMBLY, not a discovery. AUGMENTED framing
is the natural one (the augmentation is NOT vestigial — the `±r` row carries a redundancy functional `ρ₀`, not a
`blockBasisOn` basis vector; structurally required, independent of override↔genuine). ALL bricks REUSED, NONE
needs a re-key (§(4.87.4)). All six narrow geometry-arm
routes (b / α / D / γ / β / chain-edge-re-key) are decisively REFUTED — they reduce to ONE root: the project's
`caseIIICandidate` OVERRIDES the support extensors at two slots, creating an `hr : ±r-row ∈ span` obligation
KT never has, and rigidly pinning the reproduced-slot panel to the short-circuit `(vtx(i+1), vtx(i−1))` whose
perp is FALSE for the generic seed. The full refutation arc is recorded in design §§(4.77)–(4.83) + git; do NOT
re-derive it. **The ONE un-refuted route is (D-substitution)** (design §(4.84) scoping + §(4.85) S2-GO + §(4.86)
S3-GO): rebuild the candidate as a pure `ofNormals G ends q` on `G` (keeping `v`, `q := Q.normal`, NO override),
so the `±r` row is the genuine chain-edge `(vᵢvᵢ₊₁)`-row (`hr` discharged by the LANDED chain-edge perp
`baseRedundancy_perp_interior_reproduced_panel` `ForkedArm.lean:640`) and the bottom is the literal `R(G,pᵢ)`
whose non-chain rows transport to `R(Gab)` via the **LANDED** D-canonical bottom bridge.

**S2 MAKE-OR-BREAK = GO (§(4.85), spike `SpikeDSubst.lean`, 5 probes SORRY-FREE).** Both faces compose:
(BOTTOM) the literal-`R(Gab)` submatrix bridge is **already LANDED** (D-canonical
`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387` + `blockBasisOn_congr` `:610`) — threading `Q` only
RE-DERIVES it; (CORNER) the genuine chain-edge `±r` row's membership reduces EXACTLY to the chain-edge-panel
perp the LANDED lemma delivers. The §(4.84) "S2 re-hits the §(4.70) PROBE-2a opaque-basis wall" was an OUTDATED
flag (that wall is dissolved by D-canonical). **S3 MAKE-OR-BREAK = GO (§(4.86), spike `SpikeDSubstS3.lean`, 7
probes A–G SORRY-FREE, `Build completed (2784 jobs)`, deleted; the tail is now LANDED as
`case_III_realization_of_rank_ofNormals` `ForkedArm.lean:1238`, axiom-clean).** The realization tail COMPOSES
for a genuine `ofNormals G ends q` cert — and is STRUCTURALLY SIMPLER: the W6f shear is NOT needed (it was an
artifact of the override's fictional candidate line, not an intrinsic need of the realization). The LANDED tail
takes `hrank` (at the genuine framework) → motive: W6e re-extracts `F`'s OWN panelRows (framework-general),
they are LITERAL rigidity rows, `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` gives rigidity
AT THE CERT FRAMEWORK, `hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades to the motive — no
`caseIIICandidate`, no `t`-family, no good-`t`. **The §(4.84.3)/(4.85.5)
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
= GO; S1 + S2 + S3 + S4 ALL LANDED; S5's DISPATCH-WIRING INTERFACE KERNEL-SETTLED (§(4.88)) — A CLEAN BUILD, NO
FRESH ADJUDICATION; NEXT = THE S5 BUILD (the `_aug` block-data assembly + the dispatch body + the C.3 `hIH` add).**
S4 LANDED 2026-06-28 (`PanelHingeFramework.case_III_arm_realization_aug_ofNormals` `ForkedArm.lean:1309`,
axiom-clean, gates green): the `_ofNormals` sibling of `case_III_arm_realization_aug` — built `Lrow` (B1
`exists_rowOp_of_strictInjection`) + the (6.61) column-op `U`, reshaped `fromBlocks A B C D → fromBlocks
(A−L₀C) 0 C D` via `hB` (B2 `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`), called the LANDED S2
wrapper `case_III_rank_certification_aug_ofNormals` for `hrank`, fed the LANDED S3 tail
`case_III_realization_of_rank_ofNormals`. Only the two seam calls swap vs the override arm; the much simpler S3
tail let `Gv/v/a/b/e_a/e_b`'s chain-arm machinery drop (the tail's `IsLink`-shaped `hne`/`hends` are derived
in-body from the cert's edge-set forms via `IsLink.edge_mem`/`exists_isLink_of_mem_edgeSet`, `V(G).Nonempty`
from `hVcard`/`hVone`). Clean first pass, exactly the §(4.87.3) kernel-de-risked prediction. S2 LANDED 2026-06-28
(`PanelHingeFramework.case_III_rank_certification_aug_ofNormals` `Candidate.lean:2782`, axiom-clean, gates
green): the cert wrapper — the `caseIIICandidate … 0 → (ofNormals G ends q).toBodyHinge` mechanical
substitution of `case_III_rank_certification_aug` (`Candidate.lean:2694`), body verbatim (the `hends'`
graph-rewrite via `toBodyHinge_graph`/`ofNormals_graph`, the framework-general backbone call
`finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` at `F = (ofNormals G ends q).toBodyHinge`,
the `Nat.mul_succ` count) — delivering `hrank` AT `(ofNormals G ends q).toBodyHinge.rigidityRows` (the exact
LANDED-S3-tail hypothesis). Clean first pass, exactly as §(4.87) PROBE 1 predicted. S1
(`hingeRow_mem_ofNormals_rigidityRows_chainEdge` `ForkedArm.lean:621`, axiom-clean) confirms the §(4.86.4)
shape (a): the genuine chain-edge `±r` row IS a rigidity row of the pure `ofNormals G ends q` framework, its
`hperp` the LANDED chain-edge perp — NO override, NO false `hr`. **S3** (`case_III_realization_of_rank_ofNormals`
`ForkedArm.lean:1238`, axiom-clean, LANDED 2026-06-28) is PROBE G's tail verbatim: from `hrank` AT the genuine
`(ofNormals G ends q).toBodyHinge`, W6e (`exists_independent_panelRow_subfamily_of_le_finrank`) → inline
literal `hmem` (the §38 `hrow_mem` link-witness idiom) → `isInfinitesimallyRigidOn_vertexSet_of_independent_
rigidityRows` → `hasGenericFullRankRealization_of_rigidOn_ofNormals`. No `caseIIICandidate`, no shear, no
good-`t`. The six narrow routes are all dead — verdict pointers only (full arc in design §§(4.77)–(4.83) + git):
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
- **S2 make-or-break (two defeq faces) = GO (§(4.85)); the cert-WRAPPER SHAPE = SETTLED, a CLEAN ASSEMBLY
  (§(4.87), kernel-clean).** Both faces compose SORRY-FREE (BOTTOM `submatrix_columnOp_toBlocks₂₂_eq_Gab`
  `Concrete.lean:2387` + `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`, LANDED; CORNER the genuine
  chain-edge `±r` membership = the LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel`
  `ForkedArm.lean:640`). **§(4.87) settles the WRAPPER:** `case_III_rank_certification_aug` (`Candidate.lean:2694`)
  IS `caseIIICandidate`-hard-wired (the coordinator's read confirmed), but the framework-general object is one
  level down — `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1258`, abstract
  `F`); the S2 wrapper `case_III_rank_certification_aug_ofNormals` is the `caseIIICandidate → ofNormals` mechanical
  substitution (PROBE 1, built SORRY-FREE + axiom-clean), calling the same backbone. **AUGMENTED is the natural
  framing — NOT vestigial** (the `±r` row carries a redundancy functional `ρ₀`, not a `blockBasisOn` basis vector;
  structurally required, independent of override↔genuine, unlike the S3 shear which WAS an override artifact).
  **ALL bricks REUSED at the `ofNormals` level, NONE needs a re-key** (PROBES 1–5: backbone, S1-leaf `hr`,
  `corner_hA'_of_gate` `Concrete.lean:810`, the bottom bridge). The "signature swap, not new math" framing is
  precision-CORRECTED (the wrapper is candidate-specific, not framework-general) but CONFIRMED substantively
  (§(4.87.5)). NO hidden new leaf — the trap is absent.
- **S3 LANDED (§(4.86)); the W6f shear is NOT needed.** `case_III_realization_of_rank_ofNormals`
  (`ForkedArm.lean:1238`, axiom-clean) is PROBE G's composition verbatim — `hrank` (at the genuine
  `(ofNormals G ends q).toBodyHinge`) → motive via W6e (`exists_independent_panelRow_subfamily_of_le_finrank`,
  framework-general) → inline literal `hmem` (the §38 `hrow_mem` link-witness; `panelRow_mem_rigidityRows`'s
  body, kept inline to avoid `whnf`-ing the carrier) → `isInfinitesimallyRigidOn_vertexSet_of_independent_
  rigidityRows` → `hasGenericFullRankRealization_of_rigidOn_ofNormals`. The §(4.84.3)/(4.85.5) "pure-`ofNormals`
  breaks the W6f `t`-family" was over-PESSIMISTIC: the shear was an artifact of the override's FICTIONAL
  candidate line (PROBE B.1), dissolved when the candidate is genuine. (Affine-in-`t` IS native to a
  pure-`ofNormals` seed-move family if ever needed — PROBES E/F — so a shape-(c) `t`-layer is a live fallback,
  but the LANDED tail shows it UNNEEDED.)
- **Q2 (blast radius, §(4.84.3)) — RESOLVED, NO escalation (§(4.88)):** (D-substitution) is BELOW
  the C.0–C.6 contract TYPES + the 0-dof motive (no new motive conjunct, no IH-strength change, no `ChainData`
  field), and CROSSES the C.3 motive/producer SEAM only in its BODY — replacing `caseIIICandidate`
  (`Candidate.lean:940`) with a pure-`ofNormals` candidate threading `q := Q.normal` (`Q` already
  `ofNormals`-concretized in the dispatch, `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`
  `Realization.lean:822`). The W6f-tail worry §(4.84.3) raised is GONE (§(4.86)); the dispatch-wiring interface
  (S5) is now KERNEL-SETTLED (§(4.88)) — the 0-dof motive's GP conjunct supplies the candidate's `hgp`
  GRAPH-FREELY (PROBE 2), so the seam crossing is the AUTHORIZED re-architecture, NO fresh adjudication.
- **Q3 (decomposition, §(4.84.4) refined by §(4.85.4)/(4.86.4)):** REUSED = Q1 union-count, the block-rank
  backbones, D1 `interior_hsplitGP`, the chain-edge perp, the corner-`hA` gate, **AND the entire bottom
  bridge**, **AND the framework-general realization closers** (`exists_independent_panelRow_subfamily_of_le_
  finrank`, `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`,
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`), **AND the entire `_aug` cert backbone + every slot brick
  (§(4.87.4) — NONE re-keyed)**. NEW = **S1** ✓ the genuine-`±r` membership leaf
  (`hingeRow_mem_ofNormals_rigidityRows_chainEdge`, LANDED); **S2** ✓ the cert wrapper
  `case_III_rank_certification_aug_ofNormals` (`Candidate.lean:2782`, LANDED — the `caseIIICandidate → ofNormals`
  restatement); **S4** ✓ the arm assembly `case_III_arm_realization_aug_ofNormals` (`ForkedArm.lean:1309`,
  LANDED); **S3** ✓ the realization tail (LANDED); **S5** the C.3 dispatch-body reshape — INTERFACE KERNEL-SETTLED
  (§(4.88), a clean build, NO fresh adjudication), now a BUILD (the `_aug` block-data assembly + dispatch body +
  the C.3 `hIH` add); S6 CHAIN-5 + router (folds into S5). **~2–3 commits remaining (REVISED DOWN; S1/S2/S3/S4
  LANDED, S5 interface kernel-confirmed).**

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

- [→] **(D-substitution) — BUILD (§(4.84) scoping + §(4.85) S2-GO + §(4.86) S3-GO + §(4.87) S2-shape).** ALL
  three spikes kernel-confirmed GO; **S1 + S3 LANDED, the S2 cert-wrapper shape SETTLED (§(4.87))** — next is
  **S2 (the cert wrapper) + S4 (the arm assembly)**. Ordered sub-commits:
  - [x] **S1 — the genuine-`±r` membership leaf (NO new candidate `def` — `ofNormals` IS the candidate).** LANDED
    2026-06-28 (`PanelHingeFramework.hingeRow_mem_ofNormals_rigidityRows_chainEdge` `ForkedArm.lean:604`,
    axiom-clean): the `±r` membership at the genuine chain-edge slot reads `e_a`'s GENUINE support panel
    (`ofNormals_supportExtensor_eq_panel_of_ends`), so `hperp` is the chain-edge perp the LANDED
    `baseRedundancy_perp_interior_reproduced_panel` delivers — NO override panel, NO false short-circuit-panel
    `hr` obligation. Same `Submodule.subset_span ⟨e_a, v, a, hlink, ρ₀, hblock, rfl⟩` shape as the override leaf
    `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`, but `hblock` reduced through the genuine `ofNormals`
    support. The candidate stays a pure `ofNormals G ends q` (no new `def`; SHAPE (a), §(4.86.4)).
  - [x] **S2 — the cert WRAPPER `case_III_rank_certification_aug_ofNormals`** (the `caseIIICandidate → ofNormals`
    mechanical substitution of `case_III_rank_certification_aug` `Candidate.lean:2694`). LANDED 2026-06-28
    (`PanelHingeFramework.case_III_rank_certification_aug_ofNormals` `Candidate.lean:2782`, axiom-clean, gates
    green): exactly §(4.87) PROBE 1, clean first pass. The wrapper is candidate-specific, but its body calls the
    framework-general backbone `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`
    (`Concrete.lean:1258`, abstract `F`) at `F = (ofNormals G ends q).toBodyHinge` + the `Nat.mul_succ` count — a
    thin RE-STATEMENT (body byte-for-byte the override wrapper's, only `hends'` rewrites via
    `toBodyHinge_graph`/`ofNormals_graph` instead of `caseIIICandidate_graph`), NOT new math. AUGMENTED framing
    (the `±r` row's `ρ₀` is a redundancy functional, not a `blockBasisOn` basis vector → the augmentation is
    structurally required, NOT vestigial). Conclusion = the exact S3-consumer `hrank` at
    `(ofNormals G ends q).toBodyHinge.rigidityRows`. `hr` (= the LANDED S1 leaf), `hA` (= `corner_hA'_of_gate`),
    `hD` (= the LANDED bottom bridge), `Lrow`/`U`/`hblock` enter as hypotheses, supplied by the S4 arm assembly.
  - [x] **S3 — the NEW simpler realization tail (NOT `case_III_realization_of_rank`; that one is the override
    tail, KEPT for `d=3`/`caseIIICandidate`).** LANDED 2026-06-28 (`case_III_realization_of_rank_ofNormals`
    `ForkedArm.lean:1238`, axiom-clean, gates green): PROBE G's composition verbatim — W6e at the genuine `F`
    (framework-general `exists_independent_panelRow_subfamily_of_le_finrank`) → inline literal `hmem` (the §38
    `hrow_mem` link-witness idiom, kept inline to keep the `ofNormals` carrier opaque) →
    `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` → `hasGenericFullRankRealization_of_
    rigidOn_ofNormals`. The W6f shear is NOT needed (§(4.86)). Took `hrank` AT `(ofNormals G ends q).toBodyHinge`
    as the hypothesis (S2 will produce it).
  - [x] **S4 — the arm assembly `case_III_arm_realization_aug_ofNormals`** (the `_ofNormals` sibling of
    `case_III_arm_realization_aug` `ForkedArm.lean:426`). LANDED 2026-06-28
    (`PanelHingeFramework.case_III_arm_realization_aug_ofNormals` `ForkedArm.lean:1309`, axiom-clean, gates
    green): built `Lrow`/`U` (via `exists_rowOp_of_strictInjection` +
    `prodColumnOpEquiv_transpose_toMatrix'_det_isUnit`), reshaped `fromBlocks A B C D → fromBlocks (A−L₀C) 0 C D`
    via `hB` (`rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`), called the LANDED S2 wrapper
    `case_III_rank_certification_aug_ofNormals` for `hrank`, fed the LANDED S3 tail
    `case_III_realization_of_rank_ofNormals`. Same structure as the override arm, only the cert + tail calls swap
    to their `_ofNormals` siblings (§(4.87.3)); the much-simpler S3 tail let the override arm's
    `Gv/v/a/b/e_a/e_b` chain-arm tail args drop, so the tail's `IsLink`-shaped `hne`/`hends` are derived in-body
    (`IsLink.edge_mem`/`exists_isLink_of_mem_edgeSet`, `V(G).Nonempty` from `hVcard`/`hVone`). Clean first pass.
  - [→] **S5 — the C.3 dispatch-body reshape — INTERFACE KERNEL-SETTLED (§(4.88), a CLEAN BUILD, NO fresh
    adjudication); the `_aug` block-data step started.** The S4 arm `case_III_arm_realization_aug_ofNormals`
    FIRES from the genuine candidate's conjuncts (PROBE 1); the seven non-block hypotheses are SOURCED: `hgp`
    from the discriminator's GP via the GRAPH-FREE `IsGeneralPosition` (PROBE 2 — `IsGeneralPosition` reads only
    `P.normal`, so the bottom-framework GP IS the candidate GP, verbatim), `hr` from the S1 leaf ← the LANDED
    chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` + `panelSupportExtensor_swap` (PROBE 3,
    end-to-end), the `obtain` chain (discriminator + `Q`-concretization off `hsplitGP`, `h622lb` from the LANDED
    general-`k` `case_III_nested_rank_lower_all_k`) (PROBE 4); `hva`/`hVone`/`hVcard`/`hends`/`hdef`
    trivial/benign. The `_aug` block data is the genuinely-peripheral 5c/5e assembly.
    - [x] **(5c) the augmented `hB`/`L₀` factoring `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂`** (the
      ONE genuinely-new matrix brick, §(4.79.5)) — **LANDED 2026-06-28** (`Concrete.lean`, axiom-clean, gates
      green), with its prerequisite augmented bottom read `submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom`.
      The augmented sibling of `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂` (`Concrete.lean:3119`): composes
      the LANDED `submatrix_columnOp_toBlocks₁₂_aug_eq` (`:2043`, the `χ₂` corner B-read) + the new aug bottom
      read (via the `hrebot` bottom-rows-map-`inl` defeq to `submatrix_columnOp_toBlocks₂₂_eq_mixedBottom`)
      through the LANDED engine `matrix_eq_mul_of_dual_row_comb`/`dual_comb_reindex_fiberwise` (`:2994`). Clean
      first pass, exactly the §(4.79.5) "COMPILER-CONFIRMED feasible" prediction.
    - [→] **(5e) the `re`/`hre`/`L₀` + bottom assembly** + **(5f) the dispatch body + C.3 `hIH` add + CHAIN-5**
      (§(4.79.5)/§(4.88.6)). **Next: the 5e/5f block-data assembly → dispatch body.** Map: §(4.88.1).
  - [→] **S6 — CHAIN-5 + router** (the 8-tuple → `cd : G.ChainData n` reshape + the `Fin cd.d` dispatch;
    reuses §(4.79.1)'s composition skeleton re-pointed at the S4 `_ofNormals` arm). **Folds into S5's step 2;
    ~1 commit if it splits.**
  - **Build order:** S2-faces (§(4.85)) ✓ + S3 (§(4.86)) ✓ + S2-shape (§(4.87)) ✓ kernel-confirmed → **S1
    LANDED** (the `±r` membership leaf) → **S3 LANDED** (the realization tail) → **S2 LANDED** (the cert wrapper)
    → **S4 LANDED** (the arm assembly, the kernel-de-risked clean assembly) → **S5 (NEXT, the dispatch seam —
    user adjudication)** → S6. **Gate:** full `lake build` green + `lake lint` clean + axiom-clean.

  A1–A5c (matrix model + column op + block-additivity backbones `Rank.lean:480/574/622`) + D1
  `interior_hsplitGP` ✓ LANDED and REUSED. **The `_aug` ladder reuse is RESOLVED for BOTH bottom and corner
  (§(4.87)): all bricks are framework-general / abstract-`F` and compose at `F = (ofNormals G ends q).toBodyHinge`
  (PROBES 1–5), NONE re-keyed** (the §(4.84.4) "UNCERTAIN for the corner" worry is dissolved — the corner `hr` is
  the LANDED S1 leaf, the corner `hA` reads `e_a`'s genuine panel). `_matrix`/`_rowOp`/chain dead arms stay
  landed-but-dead (αE6 retire DEFERRED to phase-close).

## Blockers / open questions

- **(D-substitution) AUTHORIZED (user, 2026-06-28) — staying in 23f; S2-faces (§(4.85)), S3 (§(4.86)),
  AND the S2 cert-WRAPPER shape (§(4.87)) ALL GO.** All six narrow routes are REFUTED (the SAME root: the `caseIIICandidate` override
  creates the false-for-generic-`q` short-circuit `hr` perp KT never has, downstream of candidate selection).
  The route is the foundational re-architecture (D-substitution) — faithful (KT's actual eq. 6.59/6.61; Q1 the
  union-dimension half LANDED general-`k` `case_III_claim612_gen` `Claim612.lean:1333`). **S2 = GO** (§(4.85)):
  both faces compose SORRY-FREE — bottom already LANDED (D-canonical), corner's genuine chain-edge `±r`
  membership reduces to the LANDED chain-edge perp. **S3 = GO** (§(4.86)): the realization tail COMPOSES for a
  genuine `ofNormals G ends q` cert and is SIMPLER — the W6f shear is NOT needed (it was an artifact of the
  override's fictional candidate line); PROBE G compiles `hrank` → motive end-to-end SORRY-FREE. The §(4.84)
  "S2 re-hits PROBE-2a" AND the §(4.84.3)/(4.85.5) "pure-`ofNormals` breaks the W6f `t`-family" were BOTH
  over-pessimistic flags, corrected at the kernel. **S5's dispatch-wiring interface is now KERNEL-SETTLED
  (§(4.88), spike `SpikeDSubstS5.lean`): a CLEAN BUILD under the standing authorizations, NO fresh adjudication —
  the S4 arm fires from the genuine candidate's conjuncts, each sourced (the 0-dof motive's GP conjunct supplies
  `hgp` GRAPH-FREELY).** Est. ~2–3 commits remaining (REVISED DOWN; S1/S2/S3/S4 LANDED, S5 interface confirmed).
  Full verdict: design §(4.88) (S5 dispatch-wiring); §(4.86) (S3-GO); §(4.85) (S2-GO); scoping §(4.84).
- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; lands with
  the C.3 dispatch reshape, S5). The interior arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`),
  derivable only from `hIH` via `splitOff_isMinimalKDof` — D1 `interior_hsplitGP` ✓ LANDED; the C.3
  consume-shape gets the `hIH` field added when the dispatch is wired (a one-bundle add touching the C.0
  producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change). Concrete ripple surface kernel-traced:
  §(4.88.4) (the 3-decl lockstep + the general-`k` `case_III_nested_rank_lower_all_k`/`interior_hsplitGP`
  consumers). Context: §(4.43) + §C.3 + §(4.79.4). **The (D-substitution) `Q`-threading (Q2/S5) is RESOLVED
  (§(4.88)) — no longer an escalation; the `hIH` add + the authorized re-architecture cover it.**
- **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) — orthogonal to the cert;
  tracked separately, lands with the dispatch.
- **Downstream (23g+):** ENTRY's `exists_chain_data_of_noRigid` reshape + floor lift + OD-1, then ASSEMBLY.
  The frozen contract (C.5/C.6) is invariant; none touches 23e's cert. ENTRY is parallel-safe (independent
  of the (D-substitution) decision — it owns the chain/cycle dichotomy + the `hD`-floor lift, not the cert).

## Hand-off / next phase

**S1 + S2 + S3 + S4 ARE ALL LANDED; S5's DISPATCH-WIRING INTERFACE IS KERNEL-SETTLED (§(4.88)) — A CLEAN BUILD,
NO FRESH ADJUDICATION; THE NEXT ACTION IS THE S5 BUILD.** (D-substitution) is USER-AUTHORIZED (2026-06-28: "do the
foundational re-architecture with any recons/spikes necessary") and the geometry arm stays in 23f (not a new
sub-phase). The four (D-substitution) bricks now landed, all axiom-clean: S1
`PanelHingeFramework.hingeRow_mem_ofNormals_rigidityRows_chainEdge` (`ForkedArm.lean:621`, the genuine-`±r`
membership); S2 `PanelHingeFramework.case_III_rank_certification_aug_ofNormals` (`Candidate.lean:2782`, the cert
wrapper, delivering `hrank`); S3 `PanelHingeFramework.case_III_realization_of_rank_ofNormals`
(`ForkedArm.lean:1238`, the `hrank`-consumer realization tail); **S4
`PanelHingeFramework.case_III_arm_realization_aug_ofNormals` (`ForkedArm.lean:1309`, the cert→tail arm assembly
— builds `Lrow`/`U`, reshapes via `hB`, fires the S2 cert for `hrank`, feeds the S3 tail; the override arm's
`Gv/v/a/b/e_a/e_b` chain-tail args drop because the S3 tail is much simpler)**. **S5 INTERFACE KERNEL-SETTLED
(§(4.88), spike `SpikeDSubstS5.lean`, 4 probes, interface map SORRY-FREE):** the S4 arm FIRES from the genuine
candidate's conjuncts (PROBE 1) and every non-block hypothesis is SOURCED — `hgp` from the discriminator's GP
via the GRAPH-FREE `IsGeneralPosition` (PROBE 2), `hr` from the S1 leaf ← the LANDED chain-edge perp (PROBE 3),
the `obtain` chain off `hsplitGP` (PROBE 4). The §(4.86.5) "open interface question" is answered YES; NO new
motive conjunct / IH-strength / contract-type change beyond the authorized route + the approved `hIH`. **(5c)
— the ONE genuinely-new matrix brick of the `_aug` block-data assembly — is now LANDED**
(`submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` + its prerequisite `_toBlocks₂₂_aug_eq_mixedBottom`,
`Concrete.lean`, axiom-clean, gates green; design §(4.79.5) item 1). **The smallest next commit:** (5e) the
`re`/`hre`/`L₀` + bottom assembly — build `reInr`/`re₂`/`hbot2`/`hbot1`/`hj`/`hsupp`/`hrank` from
`bottom_selection_of_crossFramework_span_Gab` (`Concrete.lean:2880`, fed `F₂ = R(Gab)`/`lift`/`hlift_*` off the
candidate `ends` + `hfr₂` from `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` `:822`); set `re :=
reAug ⟨e_a,_⟩ reInr`, `hre := reAug_injective …`; `hD := linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`;
`L₀` = the (5c) fiberwise weight (§(4.79.5) (5e); all feeders LANDED). Then (5f) = the `Fin cd.d` dispatch body
re-pointing the §(4.79.1) skeleton at the S4 `_ofNormals` arm + the C.3 `hIH` add + CHAIN-5. **~1–2 commits;
S6 folds into (5f).** Authoritative recon: design §(4.88) (the S5 dispatch-wiring + arm-hyp↔source map) + §(4.79.5)
(the 5c/5e/5f sub-commit list), on top of §(4.87) (S2 cert-wrapper shape) + §(4.86) (S3, LANDED) + §(4.85) (S2-faces-GO).

**LANDED-FEASIBLE + REUSED under (D-substitution) (none touches `hr`):** S1's genuine-`±r` membership leaf
`hingeRow_mem_ofNormals_rigidityRows_chainEdge` (`ForkedArm.lean:604`, LANDED 2026-06-28) consumes the
chain-edge perp below; **S3's realization tail `case_III_realization_of_rank_ofNormals` (`ForkedArm.lean:1238`,
LANDED 2026-06-28) consumes `hrank` AT the genuine `(ofNormals G ends q).toBodyHinge` and the framework-general
closers below**;
the Q1 union-count discriminator (`case_III_claim612_gen` `Claim612.lean:1333` + the moving-member pick
`exists_shared_redundancy_and_matched_candidate` `Realization.lean:1481`); the D-CAN bottom machinery
(`submatrix_columnOp_toBlocks₂₂_eq_Gab` `Concrete.lean:2387`, `bottom_selection_of_crossFramework_span_Gab`
`:2880`, `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` `:2715`); the LANDED chain-edge perp
`baseRedundancy_perp_interior_reproduced_panel` (`ForkedArm.lean:640`, the `hr`-discharger); the corner-`hA`
gate `corner_hA'_of_gate` (`Concrete.lean:810`, `e_r`-independent); D1 `interior_hsplitGP`
(`Realization.lean:758`, the `Q` source); the block-rank backbones (`Rank.lean:480/574/622`); the §(4.79.1)
dispatch composition skeleton (now to re-point at S4 in the S5 dispatch wiring); **the framework-general realization closers the
LANDED S3 tail consumes (§(4.86)): `exists_independent_panelRow_subfamily_of_le_finrank` (`GenericityDevice.
lean:718`), `panelRow_mem_rigidityRows`'s body inline (`Pinning.lean:116`, the §38 `hrow_mem` link-witness),
`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` (`CaseI.lean:1099`),
`hasGenericFullRankRealization_of_rigidOn_ofNormals` (`CaseI.lean:1478`).** The `_aug` ladder + 5c/5e reuse is RESOLVED for the corner too (§(4.85.4), cleaner
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

### (D-substitution) — the live route; S2-faces + S3 GO, S2 cert-wrapper shape SETTLED (design §(4.84) scoping + §(4.85)/(4.86)/(4.87) spikes)

- **AUTHORIZED + stay in 23f** (user, 2026-06-28): pursue the foundational re-architecture with any
  recons/spikes necessary; the geometry arm stays ONE sub-phase (23f closes ✓ when the arm lands — no new
  sub-phase, no renumber; ENTRY = 23g, ASSEMBLY = 23h unchanged). BOTH S2 §(4.85) and S3 §(4.86) are DONE, GO.
- **S1 LANDED** (2026-06-28, `PanelHingeFramework.hingeRow_mem_ofNormals_rigidityRows_chainEdge`
  `ForkedArm.lean:604`, axiom-clean, gates green): the genuine chain-edge `±r` row IS a rigidity row of the
  pure `ofNormals G ends q` framework (KT 6.59). Term-mode mirror of the override leaf
  `hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` — same `Submodule.subset_span ⟨e_a, v, a, hlink, ρ₀,
  hblock, rfl⟩`, but `hblock` reads the GENUINE `ofNormals` support (`ofNormals_supportExtensor_eq_panel_of_
  ends`), so `hperp` is the LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` — NO
  override panel, NO false short-circuit `hr` obligation. Confirms §(4.86.4) shape (a) (no new `def`).
- **S3 LANDED** (2026-06-28, `PanelHingeFramework.case_III_realization_of_rank_ofNormals` `ForkedArm.lean:1238`,
  axiom-clean, gates green): the (D-substitution) realization tail = PROBE G's composition verbatim. From
  `hrank` AT the genuine `(ofNormals G ends q).toBodyHinge`: W6e
  (`exists_independent_panelRow_subfamily_of_le_finrank`, framework-general) → inline literal `hmem` (the §38
  `hrow_mem` link-witness, NOT `panelRow_mem_rigidityRows` against the unfolded carrier) →
  `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` → `hasGenericFullRankRealization_of_
  rigidOn_ofNormals`. NO `caseIIICandidate`, NO shear, NO good-`t` (the W6f shear was an override artifact,
  §(4.86)). Built §38+§53-safe: `set F` keeps the carrier opaque, `hFG : F.graph.vertexSet = V(G)` bridges the
  rigidity conclusion (first draft `clear_value`-then-`hmem` `whnf`-timed-out → FRICTION). The override tail
  `case_III_realization_of_rank` (`Arms.lean:63`) is KEPT for `d=3`/`caseIIICandidate`. Next = S2 wiring.
- **S2 LANDED** (2026-06-28, `PanelHingeFramework.case_III_rank_certification_aug_ofNormals` `Candidate.lean:2782`,
  axiom-clean, gates green): the cert wrapper, exactly as §(4.87) PROBE 1 predicted, a clean first pass. The
  `caseIIICandidate … 0 → (ofNormals G ends q).toBodyHinge` mechanical substitution of
  `case_III_rank_certification_aug` (`Candidate.lean:2694`) — body byte-for-byte the override wrapper's (only
  `hends'` rewrites via `toBodyHinge_graph`/`ofNormals_graph` instead of `caseIIICandidate_graph`), calling the
  framework-general backbone `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂`
  (`Concrete.lean:1258`, abstract `F`) at `F = (ofNormals G ends q).toBodyHinge` + the `Nat.mul_succ` count.
  Delivers `hrank` AT `(ofNormals G ends q).toBodyHinge.rigidityRows` (the exact LANDED-S3-tail hypothesis);
  `hr`/`hA`/`hD`/`Lrow`/`U`/`hblock` enter as hypotheses (the S4 arm assembly supplies them). NOT new math (the
  §(4.87.2) AUGMENTED-required verdict holds: the `±r` row's `ρ₀` is a redundancy functional, not a
  `blockBasisOn` basis vector).
- **S4 LANDED** (2026-06-28, `PanelHingeFramework.case_III_arm_realization_aug_ofNormals` `ForkedArm.lean:1309`,
  axiom-clean, gates green): the cert→tail arm assembly, the `_ofNormals` sibling of
  `case_III_arm_realization_aug` — exactly the §(4.87.3) kernel-de-risked clean assembly, clean first pass.
  Builds `Lrow` (B1 `exists_rowOp_of_strictInjection`) + the (6.61) column-op `U`, reshapes
  `fromBlocks A B C D → fromBlocks (A−L₀C) 0 C D` via `hB` (B2
  `rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂`), fires the LANDED S2 cert
  `case_III_rank_certification_aug_ofNormals` for `hrank`, feeds the LANDED S3 tail
  `case_III_realization_of_rank_ofNormals`. Only the two seam calls swap vs the override arm; the much simpler S3
  tail let the override arm's `Gv/v/a/b/e_a/e_b` chain-tail args DROP — the tail's `IsLink`-shaped `hne`/`hends`
  are derived in-body (`IsLink.edge_mem` / `exists_isLink_of_mem_edgeSet`; `V(G).Nonempty` from `hVcard`/`hVone`
  via `Set.nonempty_of_ncard_ne_zero`), and the unused `[DecidableEq β]`/`hleG` dropped (`classical` in-body).
  Next = S5 dispatch seam.
- **S5-(5c) LANDED** (2026-06-28, `BodyHingeFramework.submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂`
  `Concrete.lean`, axiom-clean, gates green): the augmented `hB`/`L₀` corner-off-`v` factoring — the ONE
  genuinely-new matrix brick of the S5 `_aug` block-data assembly (§(4.79.5) item 1). Clean first pass, exactly
  the §(4.79.5) "COMPILER-CONFIRMED feasible" prediction. The augmented sibling of
  `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂`: composes the LANDED corner B-read
  `submatrix_columnOp_toBlocks₁₂_aug_eq` (`χ₂`) + the new prerequisite bottom read
  `submatrix_columnOp_toBlocks₂₂_aug_eq_mixedBottom` (also landed this commit — the bottom rows map through
  `Sum.inl (rebot i)` (`hrebot`), so the aug `toBlocks₂₂` is defeq to the un-augmented
  `_toBlocks₂₂_eq_mixedBottom`) through the LANDED functional engine `matrix_eq_mul_of_dual_row_comb`
  /`dual_comb_reindex_fiberwise`. Pure dual-functional arithmetic — NO `hcomb` hard math, separable from the
  arm's `re`/`m₂`. Next = S5-(5e) the `re`/`hre`/`L₀` + bottom assembly.
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
- **S2 cert-WRAPPER shape SETTLED — a CLEAN ASSEMBLY, not a discovery** (§(4.87), kernel-clean spike
  `SpikeDSubstS2.lean`, 5 probes SORRY-FREE + 5× `#print axioms`-clean). The wrapper
  `case_III_rank_certification_aug` (`Candidate.lean:2694`) IS `caseIIICandidate`-hard-wired (the coordinator's
  read CONFIRMED), but the framework-general object is one level down — the dot-method backbone
  `finrank_span_rigidityRows_ge_of_aug_submatrix_fromBlocks_zero₁₂` (`Concrete.lean:1258`, abstract `F`); the
  S2 wrapper `case_III_rank_certification_aug_ofNormals` is the `caseIIICandidate → ofNormals` mechanical
  substitution (PROBE 1, body verbatim), calling the same backbone. AUGMENTED framing is the natural one — the
  augmentation is NOT vestigial (the `±r` row carries a redundancy functional `ρ₀`, not a `blockBasisOn` basis
  vector; structurally required, INDEPENDENT of override↔genuine — unlike the S3 shear, which WAS an override
  artifact). ALL slot bricks reuse at the `ofNormals` level (backbone, S1-leaf `hr`, `corner_hA'_of_gate`, the
  bottom bridge), NONE re-keyed (PROBES 1–5). The §(4.85.4)/(4.86.4) "signature swap, not new math" is
  precision-CORRECTED (the wrapper is candidate-specific) but CONFIRMED substantively; NO hidden new leaf.
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
