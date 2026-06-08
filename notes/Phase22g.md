# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**Just landed: the eq.-(6.27) row-operation core** — `BodyHingeFramework.linearIndependent_sumElim_candidateRow_swap`
(RigidityMatrix.lean, next to `linearIndependent_sum_pinned_block_augment`). The abstract
rank-invariance-under-row-operations fact the candidate completion needs: if
`Sum.elim (Sum.elim rn (Unit→ w)) ro` is independent and `w' − w ∈ span (range (Sum.elim rn ro))`
(the candidate row differs from a target row by a combination of the *other* block rows), then
`Sum.elim (Sum.elim rn (Unit→ w')) ro` is independent. Reassociate `(ιn ⊕ Unit) ⊕ ιo → (ιn ⊕ ιo) ⊕ Unit`
(`linearIndependent_equiv`) so the candidate summand is last, then `linearIndependent_sumElim_unit_iff`
reads independence as `w ∉ span (range base)`, transferred to `w'` by `hdiff`. Graph-/carrier-free
(no §38). Green, sorry-free (`propext`/`Classical.choice`/`Quot.sound`), warning-clean, lint clean.
This is the linear-algebra content of KT eq.-(6.27)'s collapse `hingeRow v b ρ − wGv = hingeRow v a ρ`
(`wGv = hingeRow a b ρ` an old-block element).

**SHARPENED FINDING (the live route's remaining gap, refining last commit's KEY FINDING):** the device
feed (`hasFullRankRealization_of_independent_panelRow_index`) requires the independent family to be
**literally** `fun i => panelRow ends (j i)` — every member a *single* `panelRow`. Two facts now block
a one-shot single-candidate brick: **(g1)** the producer's candidate row `hingeRow v b r̂` (selector
`r̂(C(e_b)) ≠ 0`) is not a panelRow at `e_b` (panelRows annihilate their edge's extensor; `r̂` does
not); **(g2)** even the `exists_candidate_row_eq612` collapse row `hingeRow v b ρ` (`ρ ∈ (span C(e_b))^⊥`,
a genuine `rigidityRows` member) is a *combination* of `e_b`-panelRows (since `ρ` is a span of `annihRow`s
via `span_annihRow_eq_dualAnnihilator`), **not a single** panelRow. So the producer's `r̂`-family
independence does not directly yield a panelRow *family*. The swap lemma (this commit) handles the
row-operation half; the unresolved design question is **how to feed the device a family that is
panelRows-plus-one-rigidity-row** — either (A) relax the device feed to accept an independent family in
`span rigidityRows` (not literal panelRows), or (B) connect the producer's `r̂`-independence to a genuine
single-panelRow family via the collapse. This is a real design fork, not mechanical packaging.

**Next concrete step (smallest forward commit): resolve the (g1)/(g2) device-feed fork.** Recommended
route (A): build a `hasFullRankRealization_of_independent_rigidityRow` variant of
`hasFullRankRealization_of_independent_panelRow[_index]` consuming an independent family `s ⊆ span rigidityRows`
(the device closure `exists_relative_full_count_ofParam` needs only that the family's *span* sits inside
`span rigidityRows` for the coannihilator `hcoord` — check whether the panelRow shape is load-bearing
beyond `hcoord`/`hindep`, GenericityDevice.lean:234–252). If route (A) lands, the single-candidate brick
is then: producer (`linearIndependent_sum_p2_candidateRow`, abstract `F` per §38) for the `r̂`-family
independence, then the family's span ⊆ `span rigidityRows` (`rn`/`ro` panelRows + `hingeRow v b r̂` a
rigidity row at link `e_b` — its block membership is `r̂ ∈ r(p(e_b))`? NO, `r̂(C(e_b)) ≠ 0`, so it is
**not** a rigidity row at `e_b` either: re-examine — KT's actual placed row after eq.-(6.27) is
`hingeRow v a ρ`, the swap output, which IS in `span rigidityRows` via the collapse). The swap lemma
(this commit) is the bridge that replaces the producer's `r̂`-row by the collapse's `hingeRow v a ρ`
once `hingeRow v b r̂ − hingeRow v a ρ ∈ span base` is established — that membership is the genuine
geometry still to thread (it is KT's eq.-(6.24)/(6.27) decomposition, `exists_candidate_row_eq612` +
`exists_redundant_panelRow_ab_decomposition`). Stated over abstract `F` (the `ofNormals` carrier §38-times-out
the producer; confirmed prior commits).

(L0 spine, landed earlier this phase: `PanelHingeFramework.case_III_hsplit_producer` carries the
candidate-selection data + each candidate's `panelRow`-packaging as explicit `h…` and composes
`case_III_eq629_conditional` → `…_index` per disjunct.)

After the producer lands: instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed that into
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound is already green, discharged in-proof);
do the Thm 5.5→5.6 multigraph push (`lem:motions-mono-of-graph-le`). Milestone: the molecular
conjecture proved at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is
**Phase 23** (reuse map: §1.33 (C)).

**Leaves L0–L5 + the columnOp bridge + the row-swap core green; L-wire remains (genuinely multi-commit,
not mechanical).** The §1.34 (F1)/L3/L5-pack framing (`ρ = annihRow(C(e_a))`, candidate row at `e_a`
via L3) is **off the live route** — it fires only for an `annihRow`-shaped `ρ`, which the selected
candidate's row is not. L5-pack/L3 still hold as lemmas. The phase-open red-node + supersession +
label-resolution gates ran clean at open.

## Red-node consistency gate — recon verdict (2026-06-07, opening commit)

Read the target producer nodes `lem:case-II-realization` / `lem:case-III`
(`algebraic-induction/case-iii.tex`) end-to-end (statement AND proof), traced
`minimal_kdof_reduction` + the `theorem_55`/`theorem_55_generic` dispatch
(`Induction/ForestSurgery.lean`, `AlgebraicInduction/PanelHinge.lean`), and ran the supersession +
label-resolution gates over `algebraic-induction/*.tex`. **Gate clean; both open items resolved.**

- **(B.1) — CONFIRMED: the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization`
  (KT Lemma 5.4).** `theorem_55` and `theorem_55_generic` are *literally*
  `Graph.minimal_kdof_reduction` applied to three branch hypotheses — `hbase` (`V(G).ncard = 2`),
  `hsplit` (a reducible degree-2 vertex, split off), `hcontract` (a proper rigid subgraph,
  contracted). The reduction's induction (`Nat.strong_induction_on` on `V(G).ncard`) has **no
  cycle branch**: the *only* base case is `V = 2`, reached purely by descent through `hsplit`/
  `hcontract`. Short cycles dissolve into repeated splits — there is no separate short-cycle
  realization input on the Lean path. So `lem:case-III`'s `\uses{lem:cycle-realization}` is a
  **blueprint↔Lean structural divergence**: a KT-*narrative* dependency (KT's Lemma 6.13 opens by
  Lemma 4.6 with $G$ a short cycle, by Lemma 5.4, *or* carrying a length-`d` chain — Lemma 6.10/6.13
  proper is the chain case), **not** a Lean-load-bearing one for the `d=3` assembly.
  - *Reconciled in this commit, not dropped.* `lem:cycle-realization` stays genuinely RED (no
    `\leanok`; its residual gap is the cited Crapo–Whiteley projective input, not the device) and
    stays a real general-`d` input for **Phase 23's** cycle base — and it is *already* load-bearing
    for the `k > 0` `lem:case-II` (green, `\uses`'s it). So the `\uses` edge on `lem:case-III` is
    kept, with a new prose note in the node clarifying the `d=3` Lean path does not consume it.
  - *Stale `case-i.tex:149–151` text fixed.* The `lem:cycle-realization` node said the only
    cited-not-formalized step is "the genericity device, Claim 6.4/6.9, shared with Cases I and II."
    Stale post-22b — `lem:claim-6-4` went green (`\leanok`). Rewritten: the residual cited step is
    the **Crapo–Whiteley** "cycle rigid iff hinge lines independent" projective input
    (`crapoWhiteley1982` Prop 3.4 / `whiteley1999` Prop 3), with an explicit aside that Claim 6.4/6.9
    is now green and is not the gap.
- **(B.2) — DECIDED: add a small `d=3`-instance `theorem_55` node.** A blueprint node is
  green-or-red, and the *general* `thm:theorem-55` (free `n k`) must stay red until Phase 23 supplies
  `hsplit` at all `k`. So the molecule-app chapter (Cor 5.7) consumes a small green `d=3`-instance
  node = `theorem_55 (n:=2) (k:=2)` applied to the three green args (`hbase`/`hsplit`/`hcontract`),
  **not** a standalone `theorem_55_dim3` restating the statement. Rationale: avoids duplicating the
  statement (it's an instantiation, not a re-proof) and keeps the general node honestly
  red-pending-Phase-23 with a note. Mint the node name when the producer lands.
- **Supersession + resolution gates clean.** Superseded labels =
  {`-disjoint-line-meet`, `-e0-recovery`, `-motion-side-assembly`, `-pin-vertex`} (the four 22c
  motion-side dead-ends); no live node's `\uses` reaches any of them. `\uses` ⊆ `\label` (no
  dangling references). `lem:case-II-realization` / `lem:case-III` route through the same argument
  their statements claim (the `d=3` contrapositive is green; the realization assembly is the genuine
  remaining content), no live-route `\uses` reaches a superseded node.

**Verdict: the build is safe to scope.** The one real gap is the `d=3` `hsplit` producer (now cracked
into L0–L5, §1.34); the `lem:cycle-realization` dependency is not Lean-load-bearing for it (B.1), and
the architecture call is settled (B.2). No deferred Lemma-5.4 sub-phase is a prerequisite for `d=3`
(it re-enters at the Phase-23 cycle base).

## Lemma checklist

- [x] **`lem:case-III-eq629-conditional` candidate-selection capstone** — `case_III_eq629_conditional`
  (`RigidityMatrix.lean`), the graph-free selection routing `case_III_claim612`'s disjunction through
  the three per-candidate full-family implications. Node flipped GREEN. (2026-06-07)
- [x] **Abstractly-indexed device-closure feed** — `hasFullRankRealization_of_independent_panelRow_index`
  (`GenericityDevice.lean`), the `Set`-free repackaging of the device closure consuming a finite
  `ι` + injective `j` (the shape of the candidate-completion's `Sum`-indexed output). The producer's
  packaging-out end-brick. Fully green, no defeq trap; internal infra (no blueprint node). (2026-06-07)
- **`d=3` `hsplit` producer — cracked into L0–L5** (§1.34; each a smallest-buildable commit):
  - [x] **L0 — `hsplit` skeleton green-modulo** (`PanelHingeFramework.case_III_hsplit_producer`,
    CaseI.lean). The spine: the producer carries the candidate families + `hselᵢ` + `hp`/`hduality`/`hr`
    + per-candidate `panelRow`-packaging (`q₀ᵢ`/`ιᵢ`/`jᵢ`/`hfamᵢ`/`hcardᵢ`) as explicit hypotheses; body
    `rcases`'s the Claim-6.12 disjunction (`BodyHingeFramework.case_III_eq629_conditional`) and feeds the
    winner to `…_index` per branch. Green-modulo, sorry-free. (2026-06-07)
  - [x] **L1 — IH → old/new block extraction** (`PanelHingeFramework.case_III_old_new_blocks`,
    CaseI.lean). The front of `case_II_placement_eq612` exposing the OLD block `so`
    (`holdindep`/`hold`/count/`so`-avoids-`e_b`) and NEW block `sn` (`hsn_e`/`hsn_indep`/`hnewpin`)
    separately + `hane`/`hnewne`. Graph-free over `ofNormals`. Green, sorry-free. (2026-06-07)
  - [x] **L2 — pinned-block span bridge** (`BodyHingeFramework.span_panelRow_comp_single_of_edge`,
    Pinning.lean). `rn`-pinned spans `F.hingeRowBlock e` ⟹ the `hspan` the candidate producers need:
    each pinned row IS `annihRow (C(e)) t₁ t₂ ∈ r(p(e))`, `=` by equal `finrank D−1`
    (`linearIndependent_panelRow_comp_single_of_edge` + `finrank_hingeRowBlock`). Small
    `eq_of_le_of_finrank_eq` leaf, mirrors `exists_redundant_panelRow_of_edge_of_finrank_lt`'s `hrspan`.
    Green, sorry-free. (2026-06-07)
  - [x] **L3 — the candidate-row-IS-a-panelRow leaf** (`BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends`,
    Pinning.lean). The `+1` `Unit`-summand candidate row `hingeRow u w ρ` = `panelRow ends (e,t₁,t₂)`
    (where `ρ = annihRow (C(p(e))) t₁ t₂`, `ends e = (u,w)`), so it lands at an `(edge,⋀ᵏ-pair)` index
    of L5's `j`. Proof = `rw [panelRow, hends]`. **§38 trap did NOT bite** — graph-free (`panelRow` reads
    only `ends`/`supportExtensor`), so the general `BodyHingeFramework`-level form is the answer; the
    design's `ofNormals` round-trip helper was not needed. Green, sorry-free. (2026-06-07)
  - [x] **L4 — candidate-row membership** (`BodyHingeFramework.panelRow_mem_rigidityRows_of_link`,
    Pinning.lean). `e_a` links `v a` *directly* in `G` (`hlink`/`hG_ea`) ⟹ `panelRow_mem_rigidityRows`
    (after `rw [hends]`) for the `+1` summand — the direct-link analog of `case_II_placement_eq612`'s
    `hGv`-routed membership step. Closes the F2 gap. One-liner, graph-free (no §38). Green, sorry-free.
    (2026-06-07)
  - [x] **L5-inj — the candidate-completion index-map injectivity**
    (`PanelHingeFramework.candidateCompletion_index_injective`, CaseI.lean). `j` over `(sn ⊕ Unit) ⊕ so`
    placing `sn→e_b`, `Unit→e_a`, `so→Gᵥ`-edges is injective — the candidate analog of
    `case_II_placement_eq612`'s inline `hjinj`, abstract (3 disjointness facts in), graph-free (no §38).
    Green, sorry-free. (2026-06-07)
  - [x] **L5-pack — the `panelRow ∘ j` family identity + count**
    (`PanelHingeFramework.candidateCompletion_panelRow_packaging`, CaseI.lean). Ties the candidate
    producer's abstract `Sum.elim` family to `fun i => panelRow ends (j i)`: `rn`/`ro` are `panelRow`s
    of `sn`/`so`-vals, the `Unit`-summand `hingeRow u w ρ = panelRow ends (e_a,ta,tb)` via L3 once
    `ρ = annihRow (C(e_a)) ta tb` ((F1) resolved as stated — no device-feed restatement). Count
    `D(|V|−1) = ((D−1)+1)+D(m−2)`, `m ≥ 1`. `funext`/`rcases`/`rfl` identity (graph-free, no §38) +
    the `case_II_placement_eq612` count arithmetic. Green, sorry-free. (2026-06-07)
- [x] **L-wire columnOp bridge** — `columnOp_apply_single` + `comp_columnOp_comp_single`
  (RigidityMatrix.lean): `columnOp hvb` is the identity on body `v`'s screw column, converting the
  producers' operated `hrnpin`/`hspan` to the bare L1/L2 forms. Green, sorry-free. (2026-06-07)
- [x] **L-wire eq.-(6.27) row-swap core** — `BodyHingeFramework.linearIndependent_sumElim_candidateRow_swap`
  (RigidityMatrix.lean). The rank-invariance-under-row-operations fact: swap the candidate summand
  `w → w'` when `w' − w ∈ span (range (Sum.elim rn ro))`, independence preserved. Reassoc +
  `linearIndependent_sumElim_unit_iff`. Graph-/carrier-free (no §38). Green, sorry-free. (2026-06-07)
- [ ] **Device-feed fork (g1)/(g2) — the next smallest commit.** The producer's `r̂`-row and even the
  collapse's `hingeRow v b ρ` are not *single* panelRows, but the device feed needs literal panelRows.
  Recommended route (A): a `…_of_independent_rigidityRow` variant of
  `hasFullRankRealization_of_independent_panelRow[_index]` consuming an independent family with span
  ⊆ `span rigidityRows` (check the panelRow shape isn't load-bearing beyond `hcoord`/`hindep`,
  GenericityDevice.lean:234–252). See *Current state* SHARPENED FINDING.
- [ ] **L-wire single-candidate brick** — over **abstract `F`** (§38). Producer for `r̂`-independence,
  the swap core (this commit) to replace the `r̂`-row by the collapse `hingeRow v a ρ` once
  `hingeRow v b r̂ − hingeRow v a ρ ∈ span base` is threaded (KT eq.-(6.24)/(6.27),
  `exists_candidate_row_eq612` + `exists_redundant_panelRow_ab_decomposition`), then route (A)'s feed.
  Wire three bricks into the L0 spine + supply Claim-6.12 data from `exists_candidate_row_eq612` + N3b.
- [ ] **`d=3`-instance `theorem_55` node** (B.2) — instantiate `theorem_55 (n:=2) (k:=2)` on the
  three green branch args; add the small green blueprint node the molecule-app chapter consumes.
- [ ] **`lem:case-II-realization` / `lem:case-III` flip green** — once the producer + instance land.
- [ ] **Thm 5.5→5.6 push + feed `rigidityMatrix_prop11`'s `hgen`** — unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **The (g1)/(g2) device-feed shape mismatch is the live blocker** (see *Current state* SHARPENED
  FINDING). The device feed wants *single* panelRows; neither the producer's `hingeRow v b r̂` (g1) nor
  the collapse's `hingeRow v b ρ` (g2, a span of `e_b`-panelRows) is one. Needs a design call (route (A)
  relax the feed to span-⊆-`rigidityRows`; or (B) realize a single-panelRow family). Not a math blocker
  on the *result* — the `d=3` contrapositive (Claim 6.12) is green; this is feed-shape plumbing + the
  one genuine geometry step (the `hingeRow v b r̂ − hingeRow v a ρ ∈ span base` membership).
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38; carried from 22a–e) **bites the
  candidate producer call** when `F := (ofNormals …).toBodyHinge`. Mitigation: state the single-candidate
  brick over an **abstract `F : BodyHingeFramework`** (instantiate `F` only at the very end).
- **The §1.34 (F1)/L3/L5-pack `annihRow(C(e_a))` route is off the live route** — it fires only for an
  `annihRow`-shaped `ρ`, which the selected candidate's row is not. L5-pack/L3 hold as lemmas.

## Hand-off / next phase

**Smallest next commit: resolve the (g1)/(g2) device-feed fork** (the *Current state* SHARPENED
FINDING). Recommended route (A): a `hasFullRankRealization_of_independent_rigidityRow[_index]` variant
of the existing panelRow feed (GenericityDevice.lean) that consumes an independent family whose *span*
sits in `span rigidityRows` — verify first that the panelRow shape is not load-bearing beyond the
coannihilator `hcoord` + the witnessed `hindep`/`hcard` (GenericityDevice.lean:234–252; the `hsub` span
containment is the only place the panelRow form is used, and it only needs `⊆ rigidityRows`). With route
(A) the single-candidate brick is: producer (`linearIndependent_sum_p2_candidateRow`, abstract `F`) for
the `r̂`-family independence; the row-swap core (this commit,
`linearIndependent_sumElim_candidateRow_swap`) to replace `hingeRow v b r̂` by the collapse
`hingeRow v a ρ` once the difference is shown in `span base` (the one genuine geometry step, KT
eq.-(6.24)/(6.27), `exists_candidate_row_eq612` + `exists_redundant_panelRow_ab_decomposition`); then
route (A)'s feed on the resulting span-⊆-`rigidityRows` family. Wire three bricks into the L0 spine
(`case_III_hsplit_producer`) + supply Claim-6.12 data `hr`/`hp`/`hduality` from
`exists_candidate_row_eq612` + N3b. Then the `theorem_55` instantiation (B.2 node), the
`lem:case-II-realization` / `lem:case-III` flips, and the Thm 5.5→5.6 push. Leaf shapes:
`notes/Phase22-realization-design.md` §1.34 (read alongside this note — §1.34's F1/L5-pack `annihRow`
framing is off the live route).

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d`
(KT Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1 verbatim;
generalize the candidate chain on the graph-free assembly; build the `⋀^{d−1}` duality via the
top-power route per §1.33 (D), reusing 22f's already-landed `map`-range infra; reuse the existing
alg-independence machinery for the points). Open Phase 23 with its own recon (read eqs. 6.46–6.67
against the `d=3` Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **eq.-(6.27) row-swap core landed + the (g1)/(g2) device-feed fork found (2026-06-07).**
  `BodyHingeFramework.linearIndependent_sumElim_candidateRow_swap` (RigidityMatrix.lean): swap the
  candidate summand `w → w'` when `w' − w ∈ span (range (Sum.elim rn ro))`, independence preserved
  (reassoc + `linearIndependent_sumElim_unit_iff`); graph-/carrier-free, no §38. This is the
  linear-algebra core of KT eq.-(6.27)'s collapse `hingeRow v b ρ − wGv = hingeRow v a ρ`. Building it
  sharpened the candidate-placement gap: the device feed
  (`hasFullRankRealization_of_independent_panelRow_index`) needs *single* panelRows, but **(g1)** the
  producer's `hingeRow v b r̂` (`r̂(C(e_b)) ≠ 0`) is not a panelRow, and **(g2)** even the collapse's
  `hingeRow v b ρ` (`ρ ∈ (span C(e_b))^⊥`) is a *span* of `e_b`-panelRows, not one. So the producer's
  `r̂`-independence does not directly yield a panelRow family — a real design fork (route (A): relax the
  feed to a span-⊆-`rigidityRows` family; route (B): single-panelRow realization). See *Current state*.
- **Earlier this phase: columnOp bridge + L5-pack/L3 are off the live route (2026-06-07; one-line
  record).** `columnOp_apply_single`/`comp_columnOp_comp_single` (RigidityMatrix.lean, the "comp `Φ`
  identity at the pin" bridge) and `candidateCompletion_panelRow_packaging`/
  `panelRow_eq_hingeRow_annihRow_of_ends` (the `annihRow`-shaped-`ρ` family identity) are green lemmas
  but **not** how the selected candidate's row is placed (its `ρ` is not `annihRow`-shaped — the
  selector forces `ρ(C(e_b)) ≠ 0`). They stand as reusable lemmas; the live route is the swap core +
  `exists_candidate_row_eq612` collapse.
- **Leaves L0–L5-inj landed earlier this phase (2026-06-07; one-line record, full detail in the Lean
  source + git):**
  - L0 `case_III_hsplit_producer` (CaseI.lean) — the green-modulo spine carrying `hselᵢ`/`hfamᵢ`/`hjᵢ`/
    `hcardᵢ`, composing `case_III_eq629_conditional` → `…_index` per disjunct;
    `case_III_eq629_conditional` generalized to three index types (FRICTION `[resolved]`).
  - L1 `case_III_old_new_blocks` (CaseI.lean) — the front of `case_II_placement_eq612` re-exposed to
    output the OLD `so` / NEW `sn` blocks separately (verbatim proof; re-exposed since the packaged set
    hides the two-block split the `+1` augment needs).
  - L2 `span_panelRow_comp_single_of_edge` (Pinning.lean) — the candidate producers' `hspan` (pinned
    `D−1` rows span `hingeRowBlock e`), `eq_of_le_of_finrank_eq`; the `comp Φ` is identity at the pin.
  - L3 `panelRow_eq_hingeRow_annihRow_of_ends` (Pinning.lean) — F1, the candidate row IS a `panelRow`;
    `rw [panelRow, hends]`, graph-free so the §38 trap is off the `d=3` path entirely.
  - L4 `panelRow_mem_rigidityRows_of_link` (Pinning.lean) — the `+1` summand's `rigidityRows`
    membership at `e_a` via its *direct* `G`-link (closes F2); graph-free.
  - L5-inj `candidateCompletion_index_injective` (CaseI.lean) — `j` over `(sn ⊕ Unit) ⊕ so` injective,
    abstract over the three disjointness facts (incl. the new `hso_ne_ea` L1 doesn't emit); graph-free.
- **`hsplit` producer core cracked: green-modulo-skeleton-first, defeq trap isolated to one leaf
  (2026-06-07).** Decided the green-modulo-skeleton route (state the producer carrying the residual
  graph-data obligations as explicit `h…`, flip the spine first, discharge each as a leaf) over
  all-at-once — it converts the "multi-session blob" into L0–L5 and confines the §38 trap to L3.
  Three structural facts found in the Lean de-risk the leaves: F1 the candidate row IS a `panelRow`
  (placeable at an edge for `j`), F2 `case_II_placement_eq612` only needs `Gv ≤ G` for ONE membership
  step (transport graph-free, reused verbatim), F3 candidate producers need the full hinge-row-block
  span (L2, green bricks). Full cut + `j` bridge + leaf shapes: `notes/Phase22-realization-design.md` §1.34.
- **Device-closure feed lifted to an abstract index, decoupling the producer's packaging from
  `case_II_placement_eq612` (2026-06-07).** `hasFullRankRealization_of_independent_panelRow_index`
  repackages the `Set`-indexed device closure to consume a finite `ι` + injective `j` — the shape of
  the candidate-completion's `Sum`-indexed output. Built green by reindexing across
  `Equiv.ofInjective j` + `Nat.card_range_of_injective`, lifting the inline packaging out of
  `case_II_placement_eq612` (CaseI.lean:2757–2818) so the candidate path reuses it. No defeq trap (it
  is the already-green closure under an index bijection). Internal infra — no blueprint node (a
  `Set`-free restatement of an already-blueprinted lemma; churn-prone glue, below the selection bar).
- **Selection capstone built graph-free as the first producer brick (2026-06-07).**
  `case_III_eq629_conditional` discharges `lem:case-III-eq629-conditional` by composing
  `case_III_claim612`'s disjunction with three abstract per-candidate implications
  (`r̂(Cᵢ)≠0 ⟹ LinearIndependent famᵢ`). Stated over abstract families (no `ofNormals`) so the heavy
  concrete-carrier `whnf` (§38) cannot bite — the selection logic is pure `Or`-mapping. The defeq
  trap is thereby confined to the *one* remaining step (the real-graph instantiation), keeping it
  isolatable per the §38 extract-a-helper mitigation. 1-line term proof.
- **(B.1) the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization`
  (2026-06-07, open).** `theorem_55`/`theorem_55_generic` = `minimal_kdof_reduction` with three
  branches, no cycle branch, base case `V=2` only. Short cycles dissolve into repeated splits.
  `lem:case-III`'s `\uses{lem:cycle-realization}` is a KT-narrative (not Lean-load-bearing)
  dependency — kept with a clarifying prose note; the cited step it bottoms on is Crapo–Whiteley,
  not Claim 6.4/6.9 (which is green). Fixed the stale `case-i.tex:149–151` text. Detail above.
- **(B.2) add a small `d=3`-instance `theorem_55` node, not a standalone `theorem_55_dim3`
  (2026-06-07, open).** It's `theorem_55 (n:=2) (k:=2)` on three green args; the general
  `thm:theorem-55` stays honestly red-pending-Phase-23. Avoids duplicating the statement.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *The `ofNormals`/`withGraph` defeq-timeout trap + its extract-a-generic-helper mitigation*
  → TACTICS-QUIRKS § 38 (carried from 22a–e).
