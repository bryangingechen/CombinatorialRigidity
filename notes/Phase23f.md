# Phase 23f — Case III general `d`: the geometry arm (work log)

**Status:** in progress — **§(4.90) RECON VERDICT = GO via the LANDED OVERRIDE route (2026-06-28).** KT's `+1`
IS the full-rank `D × D` corner `Mᵢ = [r(Lᵢ); ±r]` (eqs. (6.61)/(6.64)/(6.65)) — exactly the project's
`corner_hA'_of_gate` shape — with the panel block on the chain edge `vᵢvᵢ₊₁` whose panel `Lᵢ ⊂ Πᵢ` is a FREE
`(d−2)`-affine subspace (eq. (6.58)) and the redundant `±r` row on the SEPARATE chain edge `vᵢ₋₁vᵢ` (eq.
(6.59)). The LANDED `caseIIICandidate` override (`Candidate.lean:940`) implements this faithfully — `e_c`-panel
= the free `Lᵢ` (gate `ρ₀(C(e_c)) ≠ 0` from the discriminator's transversal `n'`), `e_r`-`±r` perp at the
relabelled-seed reproduced panel — and the discriminator `exists_shared_redundancy_and_matched_candidate`
(`Realization.lean:2134`) co-chooses `(q, ρ₀, n')` so the gate + the redundancy-perp hold SIMULTANEOUSLY. **The
kernel off-by-one is real ONLY for the (D-substitution) `ofNormals` candidate** (it collapsed both corner
conditions onto one chain edge at its genuine seed). **Route to CHAIN close = FINISH the never-built override
`chainData_dispatch` router on top of `chainData_arm_realization_aug_zero₁₂` (`:1625`); DISCARD the
(D-substitution) `_ofNormals` siblings; ~2–4 commits, no new leaf.** This REVERSES the 2026-06-28
(D-substitution) authorization (flagged for user). No motive/contract/foundational change — the override is
below the C.0–C.6 contract + 0-dof motive, faithful (KT eqs. (6.56)/(6.59)/(6.61)/(6.66)). `d=3` stays fully
green (hard constraint). See *Current state* / *Hand-off* + design §(4.90); program map
`notes/MolecularConjecture.md`.

The fifth CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e + 23f). 23e landed the KT-faithful A3-transposed
rank certificate + LA scaffolding axiom-clean (`notes/Phase23e.md`); 23f built the geometry arm's cert
infrastructure (the interior-corner cert, the D-CAN bottom, the `_aug` ladder), then ran the route
refutations that found the dispositive blocker is the candidate-construction device itself. On (D-substitution)
landing (if authorized) the CHAIN layer closes and ENTRY (**23g**) opens; ASSEMBLY is **23h**.

## Current state

**§(4.90) RECON VERDICT (2026-06-28) = GO via the LANDED OVERRIDE route — the (D-substitution) detour was the
wrong turn; the geometry arm has a route, and it is the override dispatch the project already built.** KT's `+1`
IS a full-rank `D × D` corner `Mᵢ = [r(Lᵢ); ±r]` (KT eqs. (6.61)/(6.64)/(6.65)) — exactly the project's
`corner_hA'_of_gate` shape — BUT KT's panel block `r(Lᵢ)` sits on the chain edge `vᵢvᵢ₊₁` whose panel `Lᵢ ⊂ Πᵢ`
is a **FREE `(d−2)`-affine subspace** (eq. (6.58), chosen at the witness join via Lemma 2.1), while the redundant
`±r` row sits on the **OTHER** chain edge `vᵢ₋₁vᵢ` (the substitution `pᵢ(vᵢ₋₁vᵢ) = q₁(vᵢvᵢ₊₁)`, eq. (6.59)). The
two corner rows are on **TWO DISTINCT EDGES / TWO DISTINCT PANELS**; KT's eq.-(6.56) isomorphism `ρᵢ`
de-coincides them. **The LANDED `caseIIICandidate` override (`Candidate.lean:940`) already implements this
faithfully:** `e_c`-slot panel `panelSupportExtensor (q a) n'` = the FREE `Lᵢ` (gate `ρ₀(C(e_c)) ≠ 0` from the
discriminator's transversal); `e_r`-slot `±r` perp at the relabelled-seed reproduced panel (the IH redundancy).
The discriminator `exists_shared_redundancy_and_matched_candidate` (`Realization.lean:2134`) CO-CHOOSES
`(q, ρ₀, n')` so `ρ₀(C(ab)) = 0` (eq.-(6.23)/(6.52) IH redundancy, LANDED `:2164`) AND `ρ₀(C(a, n')) ≠ 0` (free
transversal gate, `:2188`) hold SIMULTANEOUSLY (satisfiable since `n' ∉ span{q a, q b}`). **The kernel-confirmed
off-by-one is REAL only for the COLLAPSED (D-substitution) `ofNormals` candidate** — it pinned ONE chain edge
`e_a` to its genuine seed panel `(q v)(q a)` and sourced BOTH the gate (`ρ₀(C(e_a)) ≠ 0`, `:810`) and the `hr`
perp (`ρ₀(C(e_a)) = 0`, S1 leaf `ForkedArm.lean:621`) from it, destroying the free-panel degree of freedom that
makes `Mᵢ` rank `D`. The §(4.82) "override `hr` is false for generic `q`" finding examined an ARBITRARY free `q`;
the discriminator co-chooses the seed so `ρ₀` IS the `(ab)`-redundancy (`chainData_split_w6b_gates:919` proves
it). **So the route is NOT a new cert shape: it is to FINISH the never-built override router `chainData_dispatch`
on top of `chainData_arm_realization_aug_zero₁₂`, and DISCARD the (D-substitution) `_ofNormals` siblings.** This
REVERSES the 2026-06-28 (D-substitution) authorization; flagged for the user. Full verdict + reuse map + build
plan: design §(4.90).

---

*(Superseded context — the pre-BLOCKED GO narrative, kept one cycle for the adjudication.)*
**THE ROUTE IS (D-substitution), USER-AUTHORIZED (2026-06-28); BOTH S2 (§(4.85)) AND S3 (§(4.86)) MAKE-OR-BREAK
= GO; S1 + S2 + S3 + S4 (the geometry-arm CORE: block-data → motive) ALL LANDED, + the S5 feeder bricks
(5c/5e/bottom-block assembly). A RESUME-DRIVE of the full S5 dispatch (2026-06-28) returned a VERIFIED BLOCKED
that surfaced a PHASE-BOUNDARY gap: the `Fin cd.d` router + CHAIN-5 (the C.0-trio reshape) consume `cd :
G.ChainData n`, but the `cd` producer is DESIGN-PINNED to ENTRY/23g (returns only the `d=3` 4-tuple today). So
CHAIN-5 can't complete in 23f; the remaining 23f work is Gap B (the `_ofNormals` SPINE + `chainData_dispatch`
as `cd`-TAKING lemmas). PHASE-BOUNDARY DECIDED (user, 2026-06-28): OPTION A — 23f closes at the `cd`-taking
dispatch. **THE `L₀`/`hφ` MAKE-OR-BREAK IS SETTLED = GO, AND THE `hφ`/`L₀` COLLAPSE IS NOT NEEDED for the
genuine `ofNormals` candidate (§(4.89), spike `SpikeDSubstHphi.lean`, 3 probes SORRY-FREE + WARNING-CLEAN).**
The corner block's `hA` slot LANDED (`chainData_arm_corner_hA_ofNormals_of_gate`, un-operated `A.row` form) +
the augmented `C ≠ 0` operated-corner `hAeq` LANDED (`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_
coordEquiv` `Concrete.lean:2055`). **But the genuine arm DOESN'T use the `C ≠ 0` `hAeq` / the `hφ` collapse**:
the §(4.84.4)(iii) "the `v`-incident `±r` row forces a `C ≠ 0` literal-`R(G,pᵢ)` bottom" CONFLATED the `±r`
ROW's `v`-incidence with the BOTTOM block's content. The AUGMENTED framing carries the `v`-incident `±r` row in
the CORNER `m₁` (the `inr ()` slot via `reAug`), NOT the bottom `m₂`; the bottom is the pure-`R(Gab)` pin-zero
block (`exists_aug_bottom_blockData_of_Gab` selects both endpoints `≠ v`), so **`C = toBlocks₂₁ = 0`**,
`A − L₀·C = A` regardless of `L₀`, and the operated `±r` row reads `−ρ₀` DIRECTLY. The corner `hA :
LinearIndependent ℝ (A − L₀·C).row` closes via the LANDED route-(D) leaf `corner_hA_aug_zero₁₂_of_gate`
(`Concrete.lean:2185`) with `L₀` a FREE UNUSED argument (the `±r → ρ₀` collapse is `rigidityMatrixEdgeAug_mul_
columnOp_corner_hrow` `:2249`; the `C=0` is `rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`
`:1942`; the `−ρ₀/ρ₀` sign is `map_neg`). **THE GAP-B `_ofNormals` SPINE IS NOW LANDED** (2026-06-28,
`PanelHingeFramework.chainData_arm_realization_ofNormals` `Realization.lean:1769`, axiom-clean, gates green):
the `cd`-taking `_ofNormals` analog of `chainData_arm_realization_aug_zero₁₂` — threads the `ChainData` split
geometry (`v`/`a`/`Gv`/`hva`/`hVone`/`hVcard`) and fires the S4 arm `case_III_arm_realization_aug_ofNormals`
with the augmented block data carried as hypotheses; much thinner than the override spine (the simpler S3 tail
drops the chain-arm geometry). **NEXT = `chainData_dispatch` (the `Fin cd.d` router constructing the spine's
block data per `i`: `hr` via S1, `hA` via §(4.89.5)'s `corner_hA_aug_zero₁₂_of_gate` composition, `hB`/`L₀`
via (5c), bottom via (5e), `hM'eq` trivial — off the discriminator) — pure ASSEMBLY, no genuinely-new leaf.
— see *Hand-off*.** The `hφ`-consumer
`:3741` + the `C≠0` `hAeq` `:2055` stay landed-but-unused (phase-close cleanup alongside the dead route arms).
The augmented `hD` producer `BodyHingeFramework.linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq`
(`Concrete.lean`, LANDED 2026-06-28, axiom-clean, gates green) is the AUGMENTED sibling of
`linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` — the arm's `hD` is on the AUGMENTED `toBlocks₂₂`, so this
sibling (not the un-aug one §(4.79.5) (5e) named) is the genuine `hD` slot the S4 arm consumes; it reduces to the
LANDED un-aug producer because both blocks read the SAME `Matrix.of` of the `a`-shifted edge reads.
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
    - [x] **(5e) the `re`/`hre`/`hD` bottom-block producer** — **LANDED 2026-06-28**
      (`BodyHingeFramework.exists_aug_bottom_blockData_of_Gab` `Concrete.lean`, axiom-clean, gates green): the
      reusable packaging of the (5e) bottom-block wire-up — given the candidate `F`, the IH `F₂ = R(Gab)`, the
      corner edge `ea`, and the bottom inputs (`hfr₂`/`lift`/`hlift_inj`/`hlift_ends`/`hlift_supp`/`hlift_disj`),
      produces the `re`/`hre`/`hD` triple the S4 arm `case_III_arm_realization_aug_ofNormals` consumes. Composes
      the three LANDED feeders: `bottom_selection_of_crossFramework_span_Gab` (→ `reInr`/`re₂` + injectivity +
      per-row facts) + `reAug`/`reAug_injective` (`re := reAug ea reInr`; the `Sum.inr` half is `Sum.inl ∘ reInr`
      defeq, so `rebot := reInr`, `hrebot` `rfl`) + the LANDED augmented `hD` producer
      `linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq`. Required surfacing both
      `bottom_selection_of_crossFramework_span{,_Gab}`'s selector injectivity (free from the discarded
      `exists_finCard_linearIndependent_selection` `sel`-inj) + `_Gab`'s `reInr = (lift _, _)` construction
      equation (FRICTION [idiom] ∃-bound selector). Earlier this session: the augmented `hD` producer
      `linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq` (LANDED prior commit).
    - [x] **(5f.hA) the `cd`-taking genuine corner-`hA` leaf** — **LANDED 2026-06-28**
      (`PanelHingeFramework.chainData_arm_corner_hA_ofNormals_of_gate` `Realization.lean:1840`, axiom-clean,
      gates green): the `_ofNormals` sibling of the override `chainData_arm_corner_hA_of_discriminator_gate`
      (`Realization.lean:1761`). Threads the chain-edge-panel gate `ρ₀ (panelSupportExtensor (q(v,·)) (q(a,·)))
      ≠ 0` (GENUINE panel, `v = vtx i.castSucc`, `a = vtx i.succ`) into the operated corner `hA` via the genuine
      support read `ofNormals_supportExtensor_eq_panel_of_ends` (`e_a ↦ (v,a)` recording) +
      `corner_hA_zero₁₂_of_gate`. The §(4.73.2) seam the override hit is GONE — the gate is at the SAME chain-edge
      panel the S1 `hr` membership reads (no false short-circuit panel). Clean first pass (`hi` dropped: the gate
      threading needs no `0 < i`). Supplies the corner block's `hA` slot.
    - [x] **(5f.hAeq) the augmented OPERATED-corner entry identity** — **LANDED 2026-06-28**
      (`BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_coordEquiv` `Concrete.lean`,
      axiom-clean, gates green): the augmented sibling of `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_
      coordEquiv` (`:3549`), and the `C ≠ 0` (literal-`R(G,pᵢ)`-bottom) sibling of route-(D)'s
      `corner_hA_aug_zero₁₂_of_gate` (which assumed pin-zero `C = 0`). Reads `toBlocks₁₁ − L₀·toBlocks₂₁`
      (operated corner) of the AUGMENTED matrix as `coordEquiv ∘ φ`, taking the corner reads (`χ₁`/`hrow`), the
      bottom pin reads (`χbot`/`hbotrow`), and `L₀`/`φ`/`hφ` (`φ i = χ₁ i − ∑ L₀ i i' • χbot i'`) as hypotheses.
      Entrywise `Matrix.sub_apply`/`mul_apply` + the augmented-`inl`-agrees-by-defeq pattern; clean first pass.
      This is the `hAeq` precondition the genuine corner-`hA` leaf (5f.hA) consumes. Does NOT construct `L₀`/`hφ`.
    - [x] **(5f) the `L₀`/`hφ` make-or-break — SETTLED = GO, the `hφ`/`L₀` collapse NOT NEEDED** (§(4.89),
      spike `SpikeDSubstHphi.lean`, 3 probes SORRY-FREE + WARNING-CLEAN, deleted). The §(4.73.4)(3b)/§(4.74)
      `hφ`/`L₀` collapse (`hφ : φ i = χ₁ i − ∑ L₀ i i' • χbot i'`, the un-aug consumer `:3741` ZERO callers, the
      `C≠0` `hAeq` `:2055`) was the OVERRIDE/`mixedBottom` (`C ≠ 0`) path — §(4.74) found it UNSATISFIABLE there
      (the `±r` slot read opaque `blockBasisOn(e_b,j₀)`, `=ρ₀` false). **The genuine `ofNormals` arm is the `C =
      0` pin-zero route** (the `v`-incident `±r` row is in the AUGMENTED corner `m₁`, not the bottom `m₂`; the
      bottom is pure-`R(Gab)`, both endpoints `≠ v`, so `C = 0`). The corner `hA : (A − L₀·C).row` (the S4 arm's
      obligation, `ForkedArm.lean:1345`) closes via the LANDED `corner_hA_aug_zero₁₂_of_gate` (`Concrete.lean:
      2185`) with `L₀` a FREE UNUSED arg — fed `hrow` (the `±r → −ρ₀` collapse, `rigidityMatrixEdgeAug_mul_
      columnOp_corner_hrow` `:2249`) + `hC` (`C=0`, `rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_
      zero` `:1942`); the `−ρ₀/ρ₀` sign reconciles by `map_neg` (`:2231`). **No `cGv→L₀` construction, no
      fiberwise `hφ`, no genuinely-new leaf.** Producer skeleton: §(4.89.5).
    - [x] **(5f.spine) the `cd`-taking `_ofNormals` geometry SPINE** — **LANDED 2026-06-28**
      (`PanelHingeFramework.chainData_arm_realization_ofNormals` `Realization.lean:1769`, axiom-clean, gates
      green). The `_ofNormals` analog of `chainData_arm_realization_aug_zero₁₂` (`:1625`): a `cd : G.ChainData
      n`-taking lemma that threads the split body `v := vtx i.castSucc` / successor `a := vtx i.succ` /
      deleted-vertex graph `Gv := G − v` / `hva := castSucc_ne_succ` / `hVone`/`hVcard` (off the `removeVertex`
      ncard facts) and fires the S4 arm `case_III_arm_realization_aug_ofNormals` with the augmented block data
      (`re`/`hre`/`L₀`/`rRow`/`hr`/`hM'eq`/`hB`/`hA`/`hD` + `hm₁`/`hm₂`) + framework facts (`hgp`/`hends`)
      carried as hypotheses. Much thinner than the override spine (the S4 arm's simpler S3 tail drops the
      override's `Gv/v/a/b/e_a/e_b` chain-arm geometry); `hVone`/`hVcard` derived from `a ∈ V(Gv)` /
      `v ∈ V(G)` nonemptiness (no `hV3`/interiority needed). Clean first pass (one minor `omega`-context fix:
      thread `1 ≤ V(G).ncard` into the `hVcard` cast). This IS Gap B's spine — pure assembly of LANDED bricks,
      no genuinely-new leaf, as §(4.89) confirmed.
  - [→] **S6 — `chainData_dispatch` + CHAIN-5** (the `Fin cd.d` router constructing the spine's block data
    per `i` — `rRow`/`hr` (S1 leaf), corner `hA` (§(4.89.5) `corner_hA_aug_zero₁₂_of_gate` composition),
    `hB`/`L₀` (5c), bottom (5e), `hM'eq` (`fromBlocks_toBlocks _).symm`) — off the discriminator
    `exists_shared_redundancy_and_matched_candidate`; reuses §(4.79.1)'s composition skeleton re-pointed at the
    spine `chainData_arm_realization_ofNormals`. **NEXT COMMIT. ~1–2 commits.** (CHAIN-5 / the `cd` producer →
    23g/ENTRY per option A.)
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

**NEXT = the OVERRIDE `chainData_dispatch` router (§(4.90) GO) — pending user confirmation of the route reversal.**
The §(4.90) recon settled the geometry arm: KT's `+1` is the full-rank `D × D` corner `Mᵢ` (eqs. (6.61)/(6.64)),
and the LANDED `caseIIICandidate` override implements it faithfully (free panel `Lᵢ` on `e_c`, redundant `±r` on
the separate `e_r`, the discriminator co-choosing the seed so the gate + perp hold together). The route to CHAIN
close is to BUILD the never-built **`chainData_dispatch`** — the `Fin cd.d` router on top of the LANDED override
spine `chainData_arm_realization_aug_zero₁₂` (`Realization.lean:1625`): fire the discriminator
`exists_shared_redundancy_and_matched_candidate` ONCE at the base `v₁`-split → the shared `ρ₀`, matched `i`,
transversal `n'`; per `i` construct the override block data — `rRow := hingeRow b v ρ₀` + `hr` (override leaf
`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced` ← `interior_hρe₀_of_widening`, the relabelled-seed perp),
corner `hA` (`chainData_arm_corner_hA_of_discriminator_gate`, gate at the FREE panel `(q a, n')`), `hB`/`L₀`/bottom
(5c/5e, LANDED), `hM'eq` (`fromBlocks_toBlocks .symm`) — case-split on `(i : ℕ)` (base/floor via
`chainData_split_realization`, interior via the override arm); the C.3 `hIH` add lands with it. **~2–4 commits**;
no genuinely-new leaf (the override corner/perp/bottom are all LANDED + satisfiable). Then CHAIN-5 + the `cd`
producer → 23g/ENTRY per option A. **DISCARD the (D-substitution) `_ofNormals` siblings** (S1
`hingeRow_mem_ofNormals_rigidityRows_chainEdge`, S2 `case_III_rank_certification_aug_ofNormals`, S3
`case_III_realization_of_rank_ofNormals`, S4 `case_III_arm_realization_aug_ofNormals`, the spine
`chainData_arm_realization_ofNormals`, the corner-`hA` `chainData_arm_corner_hA_ofNormals_of_gate`) — correct
*conditional* lemmas whose `hA` is unsatisfiable for the collapsed candidate; landed-but-dead, phase-close cleanup
alongside the route-(α)/(D) dead arms. **FLAG: this reverses the 2026-06-28 (D-substitution) authorization** — the
detour (sessions #52–#56) was an over-correction; the override is below the C.0–C.6 contract + 0-dof motive,
faithful (KT eqs. (6.56)/(6.59)/(6.61)/(6.66)), and its corner is satisfiable. No motive/contract/foundational
change. Full reuse map + build plan: design §(4.90).

*(Superseded GO narrative below, kept one cycle — the (D-substitution) bricks, now landed-but-dead.)* The four
(D-substitution) bricks landed, all axiom-clean: S1
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
— the ONE genuinely-new matrix brick of the `_aug` block-data assembly — is LANDED**
(`submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` + its prerequisite `_toBlocks₂₂_aug_eq_mixedBottom`,
`Concrete.lean`, axiom-clean, gates green; design §(4.79.5) item 1). **The full (5e) BOTTOM-BLOCK assembly is
now LANDED** (2026-06-28, axiom-clean, gates green): both the augmented `hD` producer
`linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq` (the arm's `hD` is on the AUGMENTED `toBlocks₂₂`,
reduces to the LANDED un-aug producer over `F₂ = R(Gab)` at `reUn := Sum.elim Empty.elim rebot`) **AND its
packaging `exists_aug_bottom_blockData_of_Gab`** (`Concrete.lean`) — given `F`/`F₂ = R(Gab)`/the corner edge
`ea`/the bottom inputs (`hfr₂`/`lift`/`hlift_inj`/`hlift_ends`/`hlift_supp`/`hlift_disj`), it produces the
`re`/`hre`/`hD` triple the S4 arm consumes, composing `bottom_selection_of_crossFramework_span_Gab` (now
returning selector injectivity + the `reInr = (lift _, _)` construction eq) + `reAug`/`reAug_injective`
(`re := reAug ea reInr`, `rebot := reInr`, `hrebot` `rfl`) + the augmented `hD` producer. **The corner block's
`hA` slot is now LANDED** (2026-06-28, `PanelHingeFramework.chainData_arm_corner_hA_ofNormals_of_gate`
`Realization.lean:1840`, axiom-clean, gates green): the `cd`-taking genuine corner-`hA` leaf — the `_ofNormals`
sibling of the override `chainData_arm_corner_hA_of_discriminator_gate` (`:1761`), threading the chain-edge-panel
gate `ρ₀ (panelSupportExtensor (q(v,·)) (q(a,·))) ≠ 0` (GENUINE panel) into the operated corner `hA` via the
genuine support read `ofNormals_supportExtensor_eq_panel_of_ends` + `corner_hA_zero₁₂_of_gate`; the §(4.73.2)
seam is GONE (the gate panel = the S1 `hr` panel). **The augmented operated-corner entry identity is also now
LANDED** (`submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_coordEquiv` `Concrete.lean`, axiom-clean —
the `C ≠ 0` literal-bottom `hAeq` read, takes `L₀`/`φ`/`hφ` as hypotheses — STAYS LANDED-BUT-UNUSED). **THE
`L₀`/`hφ` MAKE-OR-BREAK IS NOW SETTLED = GO, AND THE `hφ`/`L₀` COLLAPSE IS NOT NEEDED** (§(4.89), spike
`SpikeDSubstHphi.lean`, 3 probes SORRY-FREE + WARNING-CLEAN, deleted): the §(4.73.4)(3b)/§(4.74) `hφ` collapse
was the OVERRIDE/`mixedBottom` (`C ≠ 0`) path; the genuine `ofNormals` arm is the `C = 0` pin-zero route (the
`v`-incident `±r` row is in the AUGMENTED corner `m₁`, not the bottom; the bottom is pure-`R(Gab)`, both
endpoints `≠ v`, so `C = toBlocks₂₁ = 0`). So `A − L₀·C = A` and the corner `hA` closes via the LANDED
`corner_hA_aug_zero₁₂_of_gate` (`Concrete.lean:2185`) with `L₀` a FREE UNUSED arg — fed `hrow` (the `±r → −ρ₀`
collapse `rigidityMatrixEdgeAug_mul_columnOp_corner_hrow` `:2249`) + `hC` (`C=0`
`rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero` `:1942`); the `−ρ₀/ρ₀` sign reconciles by
`map_neg`. **The smallest next commit — `chainData_dispatch` (the `Fin cd.d` router), pure ASSEMBLY (no `hφ`,
no genuinely-new leaf):** for each `i`, obtain the discriminator data
(`exists_shared_redundancy_and_matched_candidate`), then construct the SPINE
`chainData_arm_realization_ofNormals`'s block data: `hr` via the S1 leaf
`hingeRow_mem_ofNormals_rigidityRows_chainEdge` (+ `panelSupportExtensor_swap` alignment); `hA` via §(4.89.5)'s
`corner_hA_aug_zero₁₂_of_gate` composition (`C = 0` pin-zero, fed `hrow`
=`rigidityMatrixEdgeAug_mul_columnOp_corner_hrow` + `hC`
=`rigidityMatrixEdgeAug_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`); `hB`/`L₀` via the (5c) factoring
`submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂` (`L₀` zeroes the corner's off-`v` block, NOT `hA`); bottom
via `exists_aug_bottom_blockData_of_Gab` (fed `F₂ = R(Gab)`/`lift`/`hlift_*` off the candidate `ends`, `hfr₂`
from `exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP` `:822`); `hM'eq` = `(fromBlocks_toBlocks
M').symm`. **THIS IS GAP B's tail — buildable in 23f as `cd : G.ChainData n`-TAKING lemmas; the make-or-break is
closed (§(4.89)), the spine is landed, no new geometry/LA leaf remains.**

**PHASE-BOUNDARY DECISION — DECIDED (user, 2026-06-28): OPTION A — 23f closes at the `cd`-taking dispatch.**
23f lands **Gap B** (the `_ofNormals` interior-arm spine + `chainData_dispatch` as `cd : G.ChainData n`-taking
lemmas — the geometry arm complete as a `cd`-consuming dispatch), then 23f ✓. **CHAIN-5 + the `cd` producer +
the C.0-trio wiring move to 23g/ENTRY** (where `cd` is produced). The `cd`-taking dispatch lemmas are the
designed ENTRY interface (23g wires them; not pathologically orphaned). **NEXT CONCRETE COMMIT:
`chainData_dispatch`** (the `Fin cd.d` router; the spine `chainData_arm_realization_ofNormals` it fires per `i`
is LANDED). Context for the decision (resume-drive BLOCKED 2026-06-28, rescue §6 built-in safety):
the resume-drive of the FULL S5 dispatch assembly returned a verified BLOCKED:
the `Fin cd.d` router + CHAIN-5 (the C.0 producer/consumer/ENTRY trio reshape) consume `cd : G.ChainData n`,
but the `cd` PRODUCER (`exists_chain_data_of_noRigid` `Induction/ForestSurgery/Reduction.lean:383` → a full
`ChainData`, KT Lemma 4.6 iterated) is DESIGN-PINNED to ENTRY/23g — it returns only the `d=3` 4-tuple today
(*Blockers* "Downstream (23g+)" + design §C.2/§C.5 + §(4.79.5); coord source-verified Reduction.lean:383 +
the 23g pin). So CHAIN-5 / the C.0-trio reshape CANNOT complete in 23f. Two gaps:
- **Gap B (buildable in 23f, ~1–2 commits, `cd`-taking; the make-or-break CLOSED, §(4.89)):** the genuine
  `_ofNormals` interior-arm SPINE — the `cd`-threaded analog of the override `chainData_arm_realization_aug_
  zero₁₂` (`Realization.lean:1625`) — is **LANDED** (`chainData_arm_realization_ofNormals` `:1769`). It fires
  the S4 arm `case_III_arm_realization_aug_ofNormals` from carried block data (`hM'eq`/`hB`/`L₀`/`hA`/`hD`/`re`/
  `hre`/`hr` + counts). The remaining Gap B tail is `chainData_dispatch` (the `Fin cd.d` router) constructing
  that block data per `i` off the discriminator: `hA` via §(4.89.5)'s `corner_hA_aug_zero₁₂_of_gate`
  composition (`C = 0`, NO `hφ`), `hB`/`L₀` from the (5c) brick, bottom via `exists_aug_bottom_blockData_of_Gab`,
  `hr` via the S1 leaf, `hM'eq` = `(fromBlocks_toBlocks _).symm`. Pure ASSEMBLY of LANDED bricks — no
  genuinely-new geometry/LA leaf remains (§(4.89) confirmed the corner `hA` builds SORRY-FREE).
- **Gap A (ENTRY/23g):** the `cd` producer reshape + the C.0-trio wiring (CHAIN-5) — design-pinned to 23g.

**RESOLVED: option A (user, 2026-06-28)** — 23f closes by landing Gap B as `cd`-taking lemmas; CHAIN-5 + the
`cd` producer → 23g. (Options B "pull 23g ENTRY in" and C "close at the S1–S4 arm core" were declined.)
Authoritative recon: design §(4.88)/(4.79.5).

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
the dead arms (`_matrix`/`_rowOp`/the dual-space chain arm + the route-(a)/route-α correct-but-unused leaves
**+ the `C≠0` orphan 5f.hAeq `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_coordEquiv`** — built on
the §(4.84.5)(iii) `C≠0` premise the §(4.89) spike corrected to `C=0`; correct-but-unused, 0 refs) is DEFERRED
to phase-close.

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
- **S5-(5e) augmented `hD` producer LANDED** (2026-06-28,
  `BodyHingeFramework.linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq` `Concrete.lean`, axiom-clean,
  gates green): the arm's `hD : LinearIndependent ℝ D.row` is on the AUGMENTED `toBlocks₂₂` (`hM'eq` reshapes
  `rigidityMatrixEdgeAug`), so the augmented sibling of `linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq` —
  not the un-aug one §(4.79.5) (5e)'s wording named — is the genuine `hD` slot. Both blocks rewrite to the SAME
  `Matrix.of` of the `a`-shifted edge reads (via the (5c) `_aug` `_eq_mixedBottom` + the un-aug `_eq_mixedBottom`,
  keyed `rebot i` resp. `reUn (Sum.inr i)`, defeq), so it reduces to the LANDED un-aug D-CAN-3a producer over
  `F₂ = R(Gab)` at the placeholder selector `reUn := Sum.elim Empty.elim rebot` (`m₁ := Empty` dodges a
  corner-placeholder). The `rebot`-vs-`reUn` defeq needed an explicit `Matrix.of`-typed `show`-rw (→ FRICTION).
- **S5-(5e) bottom-block packaging LANDED** (2026-06-28,
  `BodyHingeFramework.exists_aug_bottom_blockData_of_Gab` `Concrete.lean`, axiom-clean, gates green): the
  reusable (5e) producer of the arm's `re`/`hre`/`hD` triple — composes `bottom_selection_of_crossFramework_
  span_Gab` (→ `reInr`/`re₂`/per-row facts) + `reAug ea reInr` (the `Sum.inr` half `= Sum.inl (reInr ·)` defeq,
  so `rebot := reInr`, `hrebot` `rfl`) + the augmented `hD` producer. `hre = reAug_injective`, which forced
  surfacing both selectors' injectivity (`_hre_inj`/`_hreInr_inj`, free from the discarded
  `exists_finCard_linearIndependent_selection` `sel`-inj) + `_Gab`'s `reInr = (lift _, _)` construction eq
  (`_hreInr_eq`, for the corner-disjointness `(reInr i).1 ≠ ea` via `hlift_disj`). FRICTION [idiom] ∃-bound
  selector. Next = (5f) the dispatch body (the CORNER block data + the `Fin cd.d` router + the C.3 `hIH` add).
- **(5f.hA) the `cd`-taking genuine corner-`hA` leaf LANDED** (2026-06-28,
  `PanelHingeFramework.chainData_arm_corner_hA_ofNormals_of_gate` `Realization.lean:1840`, axiom-clean, gates
  green): the `_ofNormals` sibling of the override `chainData_arm_corner_hA_of_discriminator_gate` (`:1761`),
  clean first pass. Threads the chain-edge-panel gate `ρ₀ (panelSupportExtensor (q(v,·)) (q(a,·))) ≠ 0`
  (GENUINE panel `(v,a) = (vtx i.castSucc, vtx i.succ)`) into the operated corner `hA`
  (`LinearIndependent ℝ A.row`) via the genuine support read `ofNormals_supportExtensor_eq_panel_of_ends`
  (`ends e_a = (v,a)`) + `corner_hA_zero₁₂_of_gate` (with `hAeq`/`em₁`/`coordEquiv` carried). The §(4.73.2)
  override seam is GONE: the gate is at the SAME chain-edge panel the S1 `hr` membership reads, not the false
  short-circuit `(vtx i+1, vtx i−1)`. `hi : 0 < i` dropped (gate threading needs no interiority). This is the
  corner block's `hA` slot for the spine (§(4.88.1) map); the remaining `hM'eq`/`hB`/`L₀` (the `hAeq` read +
  `hcomb` widening) + spine + router are the rest of 5f. Next = the rest of the corner block data + the spine.
- **(5f.hAeq) the augmented operated-corner entry identity LANDED** (2026-06-28,
  `BodyHingeFramework.submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_aug_eq_coordEquiv` `Concrete.lean`,
  axiom-clean, gates green): the `C ≠ 0` (literal-`R(G,pᵢ)`-bottom) + AUGMENTED sibling of
  `submatrix_columnOp_toBlocks₁₁_sub_mul_toBlocks₂₁_eq_coordEquiv` (`:3549`). Reads the operated corner
  `toBlocks₁₁ − L₀·toBlocks₂₁` = `coordEquiv ∘ φ`, taking corner reads `χ₁`/`hrow`, bottom pin reads
  `χbot`/`hbotrow`, and `L₀`/`φ`/`hφ` as hypotheses — does NOT construct `L₀`/`hφ`. Entrywise via the
  augmented-`inl`-agrees-by-defeq pattern. STAYS LANDED-BUT-UNUSED: §(4.89) found the genuine arm is the `C = 0`
  pin-zero route (the `hφ`/`L₀` collapse is the `C ≠ 0` override path, NOT NEEDED), so this `C ≠ 0` `hAeq` and
  the `hφ`-consumer `:3644` have zero callers (phase-close cleanup with the dead route arms).
- **(5f.spine) the `cd`-taking `_ofNormals` geometry SPINE LANDED** (2026-06-28,
  `PanelHingeFramework.chainData_arm_realization_ofNormals` `Realization.lean:1769`, axiom-clean, gates green):
  the `_ofNormals` analog of `chainData_arm_realization_aug_zero₁₂` (`:1625`). A `cd : G.ChainData n`-taking
  lemma threading the split geometry (`v := vtx i.castSucc`, `a := vtx i.succ`, `Gv := G − v`, `hva`,
  `hVone`/`hVcard` off the `removeVertex` ncard facts), firing the S4 arm
  `case_III_arm_realization_aug_ofNormals` with the augmented block data (`re`/`hre`/`L₀`/`rRow`/`hr`/`hM'eq`/
  `hB`/`hA`/`hD` + `hm₁`/`hm₂`) + framework facts (`hgp`/`hends`) carried as hypotheses. Much thinner than the
  override spine — the S4 arm's simpler S3 tail drops the override's `Gv/v/a/b/e_a/e_b` chain-arm geometry;
  `hVone`/`hVcard` derived from `a ∈ V(Gv)` / `v ∈ V(G)` nonemptiness (no `hV3`/interiority). Clean first pass.
  Next = `chainData_dispatch` (the `Fin cd.d` router building the block data per `i`).
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
- **Two defeq-but-not-syntactic `Matrix.of` lambdas (keyed `rebot i` vs `reUn (Sum.inr i)`): `rw [← h]`
  fails; use `rw [show <Matrix.of …> = <RHS> from h.symm]` with the explicit `Matrix.of` type ascription**
  (S5-(5e) `linearIndependent_toBlocks₂₂_row_Gab_aug_of_finrank_eq`) → FRICTION (the route-(D) `_aug`
  defeq-bridge family, *[idiom] for "row of `M * (toMatrix' g)ᵀ`" …* "Also seen" siblings).
