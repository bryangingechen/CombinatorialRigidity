# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**The live route — the corrected L-wire decomposition** (recon-of-the-core,
`notes/Phase22-realization-design.md` §1.35). The (g1)/(g2) device-feed fork is **resolved**: the
candidate-row placement geometry and the device feed are pinned down, verified against KT §6.4.1
eqs. (6.24)–(6.44) and the green Lean. The placed `+1` row is `hingeRow v b r̂` (`r̂(C(e_b)) ≠ 0`),
in `span rigidityRows` (a combination of `e_b`-panelRows), fed at the *fixed* placement
(`exists_good_realization_const`). **C1 + C2 + C3 have landed** (the fixed-framework device feed,
the single-candidate brick `hasFullRankRealization_of_candidateSelector`, the re-wired L0 spine
`case_III_hsplit_producer`). **C5a + C5b have landed** (this commit): `case_III_claim612`'s
`hduality` is restated to the honest KT eq. (6.45) per-panel-line model, and its body dispatches the
per-line N3b brick over the six joins. The C3 spine carries the Claim-6.12 data
(`r`/`hr`/`hp`/`hduality`/`Cᵢ`/`hselᵢ`) + per-candidate `hmemᵢ`/`hcardᵢ` as explicit hypotheses; all
three `hselᵢ`, the `+1` `r̂`-row `hmemᵢ`, and the `r̂` candidate-vector data (`hr`) are in hand.

**Next concrete step (smallest forward commit): C5c — discharge `case_III_hsplit_producer`'s
remaining carried data at real `ofNormals` graph data (§38 defeq trap).** This now includes
*producing* the per-panel-line `hduality` witnesses: for each of the six joins `q`, supply the two
panel normals through the complementary line + the four `⬝ᵥ`-orthogonalities + the
`omitTwoExtensor … q = extensor ![pi, pj]` identity + `r ⊥ C(those normals)` — keyed off the N3a
incidence (`exists_affineIndependent_panel_incidence`, the panel tabulation in §1.36) and the
failed-block contrapositive (KT eqs. (6.42)–(6.44)). Plus the OLD/NEW-block `hmemᵢ` at the real
`ofNormals` carrier (§38). If graph-side progress is preferred, an OLD/NEW-block `hmemᵢ` leaf is
independent of the `hduality`-witness assembly. **The C4↔C5 ordering stands:** a *green*
`d=3`-instance `theorem_55` node (C4, B.2) cannot land before the C3 spine's carried data is
discharged (C5c).

After the producer lands: instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed that into
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound is already green, discharged in-proof);
do the Thm 5.5→5.6 multigraph push (`lem:motions-mono-of-graph-le`). Milestone: the molecular
conjecture proved at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is
**Phase 23** (reuse map: §1.33 (C)).

The L0–L5 row-block bricks (eq.-(6.12) `so`/`sn` blocks, L2 span bridge, L4 membership) + the columnOp
bridge + the row-swap core are green and survive as the infra C2 consumes; only the device feed and
the L0 `hfamᵢ` contract change (§1.35). The phase-open red-node + supersession + label-resolution gates
ran clean at open.

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
- **`d=3` `hsplit` producer — row-block bricks L0–L5** (§1.34's cut; the device feed they fed is
  superseded by §1.35, but the bricks below survive as the infra C1–C5 consume):
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
    `ρ = annihRow (C(e_a)) ta tb`. Count `D(|V|−1) = ((D−1)+1)+D(m−2)`, `m ≥ 1`. `funext`/`rcases`/`rfl`
    identity (graph-free, no §38) + the `case_II_placement_eq612` count arithmetic. Green, sorry-free.
    Off the live route (§1.35: the placed row's `ρ` is not `annihRow`-shaped); reusable lemma. (2026-06-07)
- [x] **L-wire columnOp bridge** — `columnOp_apply_single` + `comp_columnOp_comp_single`
  (RigidityMatrix.lean): `columnOp hvb` is the identity on body `v`'s screw column, converting the
  producers' operated `hrnpin`/`hspan` to the bare L1/L2 forms. Green, sorry-free. (2026-06-07)
- [x] **L-wire eq.-(6.27) row-swap core** — `BodyHingeFramework.linearIndependent_sumElim_candidateRow_swap`
  (RigidityMatrix.lean). The rank-invariance-under-row-operations fact: swap the candidate summand
  `w → w'` when `w' − w ∈ span (range (Sum.elim rn ro))`, independence preserved. Reassoc +
  `linearIndependent_sumElim_unit_iff`. Graph-/carrier-free (no §38). Green, sorry-free. (2026-06-07)
- [x] **C1 — the fixed-framework device-feed variant**
  (`PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow`, **CaseI.lean** — *not*
  GenericityDevice: `exists_good_realization_const` lives in CaseI and the import goes CaseI →
  GenericityDevice, so C1 cannot sit upstream). Fixed `F₀ = ofNormals G ends q₀`, an independent
  `f : ι → Module.Dual` with `span (range f) ≤ span F₀.rigidityRows` + `D(|V(G)|−1) ≤ |ι|` ⟹
  `HasFullRankRealization k G`. Weakened `exists_good_realization_const`'s `hspanrows` `=`→`≤`
  (its `hcoord` leg is now `dualCoannihilator_anti hspanrows`; the one caller `hglue_of_realization`
  takes `.le`). The rigidity-on-`V(G)` step turned out to already exist as
  `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` — refactored its body into a
  span-containment core `BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`
  (takes `hsub : span (range a) ≤ span rigidityRows` instead of pointwise `hmem`), kept the pointwise
  form as a thin wrapper; C1 wraps the core into the `HasFullRankRealization` existential at the fixed
  `ofNormals` placement. Abstract `F₀`, graph-free except the final `ofNormals` carrier. Green,
  sorry-free, build + lint clean. (2026-06-07)
- [x] **C2 — the single-candidate brick**
  (`PanelHingeFramework.hasFullRankRealization_of_candidateSelector`, CaseI.lean). Turns a
  per-candidate selector `hsel : r̂(Cᵢ) ≠ 0 → LinearIndependent fam` + per-row membership
  `hmem : ∀ i, fam i ∈ span rigidityRows` + count `D(|V|−1) ≤ |κ|` into
  `r̂(Cᵢ) ≠ 0 → HasFullRankRealization k G` (assemble span containment from `hmem`, feed C1 at the
  fixed `ofNormals G ends q₀`). Generic over `fam`/`κ`; consumes the producers' selector-shaped
  output rather than calling them, so the §38 trap is confined to C1's carrier. Build + lint clean,
  sorry-free. (2026-06-07)
- [x] **C3 — re-wire L0 to the corrected route** (`PanelHingeFramework.case_III_hsplit_producer`,
  CaseI.lean). Restated the per-candidate hypotheses from the superseded panelRow contract
  (`jᵢ`/`hjᵢ`/`hfamᵢ`) to the C2 inputs (seed `q₀ᵢ` + `hmemᵢ` + `hcardᵢ` + `hselᵢ`); body =
  `case_III_claim612`'s disjunction mapped through three `hasFullRankRealization_of_candidateSelector`
  (C2) calls — no device call in the spine. Green-modulo (the candidate-selection data stays carried
  as explicit hypotheses). Build + lint clean, sorry-free. (2026-06-07) §1.35.
- [x] **C5-leaf — the `+1` `r̂`-row membership** (`BodyHingeFramework.hingeRow_mem_rigidityRows`,
  Pinning.lean). General block-row form of `panelRow_mem_rigidityRows`: `r ∈ hingeRowBlock e` +
  `IsLink e u v` ⟹ `hingeRow u v r ∈ rigidityRows` (`⟨e,u,v,hlink,r,hr,rfl⟩`). Discharges the
  candidate `+1` row's `hmemᵢ` ingredient (§1.35 finding (1)). Graph-free, axiom-clean. (2026-06-07)
- [x] **C5-leaf — the `hsel₂`/`hsel₃` selector recasts** (`linearIndependent_sum_p2_candidateRow_selector`
  + `linearIndependent_sum_p3_candidateRow_selector`, RigidityMatrix.lean). Package the `p₂`/`p₃`
  producers into the `hselᵢ : r(C(e)) ≠ 0 → LinearIndependent famᵢ` shape (`ρ := r`,
  `C := F.supportExtensor e`); one-line `fun hr => producer … hr` term proofs, graph-free (no §38).
  (2026-06-07)
- [x] **C5-leaf — the `hsel₁` (`M₁`) selector recast**
  (`BodyHingeFramework.linearIndependent_sum_augment_candidateRow_selector`, RigidityMatrix.lean). The
  last of the three; `M₁` (`p₁` along `va`) has no separate producer, so this one builds the operated
  top-left block `hnewpinaug` inline (`hingeRow_comp_columnOp_comp_single` then the row-space criterion
  `linearIndependent_sumElim_candidateRow_iff`) rather than delegating like `hsel₂`/`hsel₃`. ~4-line
  term wrapper; graph-free (no §38), axiom-clean. All three `hselᵢ` now in hand. (2026-06-07)
- [x] **C5-leaf — the `r̂` candidate-vector data (eqs. (6.24)/(6.25))**
  (`BodyHingeFramework.exists_redundant_panelRow_ab_lam`, CaseI.lean; the mirror-eligible LA leaf
  `exists_smul_combination_eq_sub_of_mem_span_image_compl`, `Mathlib/LinearAlgebra/.../Basic.lean`).
  Reads off the explicit unit-normalized `λ` (KT eq. (6.25), `λ_{i^*} = 1`) from the redundant-row
  decomposition's `r i = wGv + wOther`, so `r̂ := ∑_j λ_j r_j = wGv` (a `G_v`-row) and `r̂ ≠ 0`
  (`hr`). Graph-free (no §38), axiom-clean. (2026-06-08)
- [x] **C5-leaf — the N3b per-line annihilation transfer, `⬝ᵥ`-incidence form**
  (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, Meet.lean; the mirror bridge
  `Pi.basisFun_toDual_apply`, `Mathlib/LinearAlgebra/Dual/Basis.lean`). Restates the green N3b core
  with incidence phrased as `pi ⬝ᵥ n_u = 0` (N3a's `exists_affineIndependent_panel_incidence` shape)
  rather than the core's `(Pi.basisFun ℝ (Fin 4)).toDual pi n_u = 0`; conversion via the mirrored
  self-pairing identity `(Pi.basisFun ℝ (Fin 4)).toDual x y = ∑ i, x i * y i`. The per-line brick the
  `hduality` dispatch consumes over the six joins. Graph-free (no §38), axiom-clean. (2026-06-08)
- [x] **C5a — restate `case_III_claim612`'s `hduality` to the per-panel-line model + C5b — the
  six-join dispatch** (route (a), RigidityMatrix.lean; landed together — the signature restate breaks
  the old body, so they are one green unit). (2026-06-09)
  - The unsound three-fixed-`Cᵢ` premise `r C₁=0 → r C₂=0 → r C₃=0 → ∀ q, r(omitTwoExtensor q)=0` is
    replaced by the honest *per-join-witness* form: `… → ∀ q : pair, ∃ (n_u n' pi pj : Fin 4 → ℝ),
    LinearIndependent ![n_u,n'] ∧ (the 4 ⬝ᵥ-orthogonalities of pi,pj to n_u,n') ∧
    omitTwoExtensor (homogenize∘p) q = extensor ![pi,pj] ∧ r(complementIso ⟨extensor ![n_u,n'],_⟩)=0`.
    Conclusion unchanged (`r C₁≠0 ∨ r C₂≠0 ∨ r C₃≠0`).
  - Body (C5b in-`case_III_claim612`): the contrapositive feeds
    `eq_zero_of_annihilates_span_top (span_omitTwoExtensor_eq_top hp)`; per `q`, the witness's
    `extensor`-equality rewrites the goal join, then the per-line brick
    `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` fires. Needed
    `public import …Molecular.Meet` (the brick + `complementIso` live there; no cycle — Meet imports
    only Extensor).
  - Both consumers (`case_III_eq629_conditional`, `case_III_hsplit_producer`) forward `hduality`
    verbatim — pure signature ripple, no proof-body change. Honesty gate **improved**: the carried
    `hduality` now *is* the conclusion of `lem:case-III-claim612-line-in-panel-union` (the `\uses`'d
    per-line node), so the node's `\leanok` is honest green-modulo case (b). Axiom-clean (no `sorryAx`),
    build + lint clean.
  - **The N3a-keyed six-join *witnessing* moved to C5c** — producing each `q`'s panel normals +
    orthogonalities + `omitTwoExtensor=extensor` identity is now part of discharging `hduality` at
    real data (the failed-block contrapositive supplies `r ⊥ C(L)`; the N3a tabulation supplies the
    pairs, §1.36).
- [ ] **C5c — discharge `case_III_hsplit_producer`'s remaining carried data** at real `ofNormals`
  graph data (§38 defeq trap): (i) *produce* the per-join `hduality` witnesses (the N3a panel
  tabulation + the eqs. (6.42)–(6.44) failed-block contrapositive — see *Current state*); (ii) the
  OLD/NEW-block `hmemᵢ` (the `+1`-row `hmemᵢ` is in hand) + `Cᵢ`/`hp` (green). Wires
  `case_III_claim612` ⊕ the producers. Takes the C3 spine fully green.
- [ ] **C4 — `d=3`-instance `theorem_55` node** (B.2) — once C5 lands: instantiate
  `theorem_55 (n:=2) (k:=2)` on the three green branch args; mint the small green blueprint node.
- [ ] **C-flip — `lem:case-II-realization` / `lem:case-III` flip green** — once the producer + instance land.
- [ ] **Thm 5.5→5.6 push + feed `rigidityMatrix_prop11`'s `hgen`** — unblocks Cor 5.7 at `d=3`.
## Blockers / open questions

- **No live blocker.** The `hduality` six-join modeling subtlety is **resolved and landed** (C5a/C5b,
  this commit): `case_III_claim612`'s `hduality` now carries KT eq. (6.45)'s per-panel-line model and
  the body dispatches the per-line brick. Verdict (kept terse; full account in *Decisions made* +
  §1.36): the fixed-`C₁C₂C₃` form was mathematically undischargeable (three `2`-extensors span
  ≤ `3 < 6 = finrank ⋀²ℝ⁴`); KT sweeps every line in the panel union (6.45), reaching the six joins
  via Lemma 2.1. The remaining work is C5c — *producing* the per-join witnesses at real `ofNormals`
  data (now part of discharging `hduality`).
- **No live blocker on the device feed.** The (g1)/(g2) fork is **resolved** (§1.35 / *Current
  state*): the corrected feed is the fixed-framework, genericity-free `exists_good_realization_const`
  route (C1), not the panelRow-shaped `_index` feed. The `d=3` contrapositive (Claim 6.12) is green
  modulo the `hduality` shape question above; the remaining work is the C1–C5 composition.
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38; carried from 22a–e). The
  `r̂`-producers are graph-free over abstract `F`; C1 instantiates `F` to the concrete
  `ofNormals … q₀ᵢ` carrier only at the final device-feed call, and C2 states everything over abstract
  `F`, instantiating only when it composes with C1. C3's spine carries the per-candidate `hmemᵢ` at the
  concrete `ofNormals G ends q₀ᵢ` carrier, but only as a hypothesis (no `whnf` of the carrier in the
  spine); the §38 trap re-enters only when the leaves that discharge `hmemᵢ` instantiate it.
## Hand-off / next phase

**Smallest next commit: C5c — discharge `case_III_hsplit_producer`'s carried data at real `ofNormals`
graph data** (§38 defeq trap). Two independent strands, either a smallest commit:
- **(i) Produce the per-join `hduality` witnesses.** `case_III_claim612`'s restated `hduality` (C5a,
  landed) now needs, per join `q`, the two panel normals through the complementary line + the four
  `⬝ᵥ`-orthogonalities + the `omitTwoExtensor (homogenize∘p) q = extensor ![pi,pj]` identity +
  `r ⊥ C(those normals)`. Source: the N3a incidence (`exists_affineIndependent_panel_incidence`, the
  six-join panel tabulation in §1.36) for the normals/orthogonalities, and the failed-block
  contrapositive (KT eqs. (6.42)–(6.44)) for `r ⊥ C(L)`. The `omitTwoExtensor`-↔-complementary-pair
  identity is a `fin_cases q` + `orderEmbOfFin` computation (Extensor.lean shapes). Graph-free until
  the `r`/`Cᵢ` data is instantiated.
- **(ii) The OLD/NEW-block `hmemᵢ`** at the real `ofNormals` carrier (the `+1`-row `hmemᵢ` is in hand
  via `hingeRow_mem_rigidityRows`); via L2 span bridge / L4 membership on the L1 blocks. Independent
  of (i).

**C4 (a green `theorem_55` `d=3`-instance) is blocked on C5.** The C5c `hmemᵢ` (at real `ofNormals`
data, §38 defeq trap): the OLD/NEW `so`/`sn` blocks via L2 span bridge
(`span_panelRow_comp_single_of_edge`) / L4 membership (`panelRow_mem_rigidityRows_of_link`) on the L1
blocks, and the `+1` `r̂`-row via the landed `hingeRow_mem_rigidityRows` (the placed `hingeRow v b r̂`
with `r̂ ∈ hingeRowBlock e_b`). After C5: C4 (mint the green `theorem_55 (n:=2) (k:=2)` instance node,
**not** a standalone `theorem_55_dim3`), the `lem:case-II-realization` / `lem:case-III` flips, the
Thm 5.5→5.6 push. Full verified leaf sequence + the KT/Lean verification:
`notes/Phase22-realization-design.md` §1.35 (L-wire) + §1.36 (the `hduality` restate verdict).

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d`
(KT Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1 verbatim;
generalize the candidate chain on the graph-free assembly; build the `⋀^{d−1}` duality via the
top-power route per §1.33 (D), reusing 22f's already-landed `map`-range infra; reuse the existing
alg-independence machinery for the points). Open Phase 23 with its own recon (read eqs. 6.46–6.67
against the `d=3` Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **C5a/C5b landed: `case_III_claim612`'s `hduality` restated to the per-panel-line model + the
  six-join dispatch in-body (2026-06-09; verdict home `notes/Phase22-realization-design.md` §1.36).**
  The fixed-`C₁C₂C₃` `hduality` was mathematically undischargeable (three `2`-extensors span
  ≤ `3 < 6 = finrank ⋀²ℝ⁴`); KT sweeps *every* line in the panel union (6.45), reaching the six joins
  via Lemma 2.1. New `hduality` (per-join witness form): `r C₁=0 → r C₂=0 → r C₃=0 → ∀ q : pair,
  ∃ n_u n' pi pj, indep ∧ (4 ⬝ᵥ-orths) ∧ omitTwoExtensor (homogenize∘p) q = extensor ![pi,pj] ∧
  r(complementIso ⟨extensor ![n_u,n'],_⟩)=0`. Body: contrapositive → `span_omitTwoExtensor_eq_top`,
  per `q` rewrite the join by the witness's `extensor`-equality, fire the per-line brick. Needed
  `public import …Molecular.Meet` (brick + `complementIso`; no cycle). Both consumers forward
  `hduality` verbatim — pure signature ripple. **Honesty gate improved**: `hduality` now *is* the
  conclusion of the `\uses`'d `lem:case-III-claim612-line-in-panel-union` (legit green-modulo case
  (b)). Updated that node's blueprint parenthetical to the landed past tense (no `\lean{}`/`\uses`
  change → no checkdecls). Axiom-clean, build + lint clean.
- **The N3b per-line transfer landed as a `⬝ᵥ`-incidence restatement of the green core (2026-06-08).**
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` (Meet.lean) restates the green N3b core
  with incidence as `pi ⬝ᵥ n_u = 0` (N3a's shape) instead of `toDual pi n_u = 0`, via the mirrored
  self-pairing identity `Pi.basisFun_toDual_apply` (`toDual x y = ∑ i, x i * y i`). The per-line brick
  the restated `hduality` dispatch (C5b) consumes. Building it forced the KT eq. (6.45) re-read that
  surfaced the modeling subtlety resolved in the entry above. Graph-free (no §38), axiom-clean.
- **The `r̂` candidate vector landed via a mirror-eligible coefficient-extraction leaf, not
  inline (2026-06-08).** `exists_redundant_panelRow_ab_lam` (CaseI.lean) reads the explicit
  unit-normalized `λ` (KT eq. (6.25), `λ_{i^*} = 1`) off the redundant-row decomposition's
  `r i = wGv + wOther`, so `r̂ := ∑_j λ_j r_j = wGv` (a `G_v`-row) and `r̂ ≠ 0`. The actual
  coefficient extraction is pure LA (negate `Fintype.mem_span_image_iff_exists_fun`, extend by `1`
  at `i`; nonzero via `linearIndependent_sum_smul_ne_zero`), so it was mirrored as
  `exists_smul_combination_eq_sub_of_mem_span_image_compl` (`Mathlib/LinearAlgebra/.../Basic.lean`,
  alongside its sibling) over a nontrivial `Ring` rather than buried in the rigidity proof. Two
  minor build cycles (FRICTION [mirrored]). Graph-free (no §38), axiom-clean.
- **The `hsel₁` (`M₁`) selector builds `hnewpinaug` inline; the `hsel₂`/`hsel₃` ones delegate to the
  `p₂`/`p₃` producers (2026-06-07).** All three are `BodyHingeFramework`-level selector recasts
  packaging a candidate producer into the `hselᵢ : r(C(e)) ≠ 0 → LinearIndependent famᵢ` shape
  `case_III_eq629_conditional` / `case_III_hsplit_producer` consume (`ρ := r`,
  `C := F.supportExtensor e`). `hsel₂`/`hsel₃` (`linearIndependent_sum_p{2,3}_candidateRow_selector`)
  are one-line `fun hr => producer … hr` wrappers — the `p₂`/`p₃` producers do the `hnewpinaug` work.
  `M₁` (`p₁` along the original `va`) has no separate producer (it *is* the candidate-completion
  assembly `linearIndependent_sum_augment_candidateRow`), so its selector
  (`linearIndependent_sum_augment_candidateRow_selector`) builds the operated block inline:
  `rw [hingeRow_comp_columnOp_comp_single hva r]` then the row-space criterion
  `linearIndependent_sumElim_candidateRow_iff` — a ~4-line term wrapper, still graph-free (no §38),
  axiom-clean. No friction. Built as selectors (not folded into producers) so the producers keep the
  cleaner `ρ(C(e)) ≠ 0` statement and the selectors match the consumer's `r C ≠ 0` shape verbatim.
- **The `+1` `r̂`-row membership landed as the general block-row form, not the sum decomposition
  (2026-06-07).** `hingeRow_mem_rigidityRows` (Pinning.lean): `r ∈ hingeRowBlock e` + `IsLink e u v`
  ⟹ `hingeRow u v r ∈ rigidityRows`, a one-line `⟨e,u,v,hlink,r,hr,rfl⟩` straight off `rigidityRows`'s
  definition. The candidate `+1` row is `hingeRow v b r̂` with `r̂ = ∑_j λ_{(ab)j} r_j`, each
  `r_j ∈ r(p(e_b)) = hingeRowBlock e_b` (a `Submodule`), so `r̂ ∈ hingeRowBlock e_b` and the row is
  *directly* a rigidity row — no `= ∑ λ_j hingeRow v b r_j` decomposition / `span_annihRow_eq_…`
  needed (the §1.35 hand-off's route was heavier than the fact). Generalizes
  `panelRow_mem_rigidityRows` (drops the `r = annihRow C` forcing — `r̂(C(e_b)) ≠ 0`, off the panelRow
  coset). Graph-free (no §38), axiom-clean. No friction.
- **C4↔C5 ordering corrected (2026-06-07).** A green `d=3`-instance `theorem_55` node (C4) is blocked
  on the producer discharge (C5) — confirmed against §1.35 + B.2 ("mint the node name when the
  producer lands"); the prior *Current state* "C4 next" predated that. C5 (discharge
  `case_III_hsplit_producer`'s carried `hr`/`hp`/`hduality`/`Cᵢ`/`hselᵢ`/`hmemᵢ` at real `ofNormals`
  data) is the live work; the `+1`-row `hmemᵢ` ingredient is now in hand.
- **C3 re-wired the L0 spine to the corrected route — a clean signature edit + 6-line body
  (2026-06-07).** `case_III_hsplit_producer`'s per-candidate hypotheses dropped the superseded
  panelRow packaging (`jᵢ`/`hjᵢ`/`hfamᵢ`) for the C2 inputs (`q₀ᵢ`/`hmemᵢ`/`hcardᵢ`/`hselᵢ`); body now
  `rcases`'s `case_III_claim612`'s `r Cᵢ ≠ 0` disjunction and applies
  `hasFullRankRealization_of_candidateSelector` (C2) to each disjunct — no device call in the spine.
  No downstream callers, so the signature change was self-contained (green-modulo skeleton, carried
  selection data unchanged). Used `BodyHingeFramework.case_III_claim612` directly (the disjunction
  source) rather than `case_III_eq629_conditional` (which maps it through the selectors) — C2 wants the
  `r Cᵢ ≠ 0` disjunct, not the `LinearIndependent famᵢ` it would already discharge into. No friction.
- **C2 stated generic over the assembled family, consuming the producers' selector output rather
  than calling them (2026-06-07).** `hasFullRankRealization_of_candidateSelector` takes the
  selector-shaped `hsel : r̂(Cᵢ) ≠ 0 → LinearIndependent fam` (the exact `hselᵢ` shape of
  `case_III_eq629_conditional`) + pointwise membership `hmem` + count, and feeds C1 — a 4-line
  composition (`span_le`/`range_subset_iff` to lift `hmem` to the span containment). Keeping it
  generic over `fam`/`κ` (not calling `linearIndependent_sum_{p2,p3,augment}_candidateRow` inside)
  leaves the producer machinery in the green abstract lemmas and confines the §38 carrier trap to C1.
  C1's implicit `q₀` needed `(q₀ := q₀)` passed explicitly (pinned only by the later `hsub` arg);
  routine elaboration-order, no FRICTION.
- **C1 landed by factoring the existing rigidity-on-`V(G)` closure, not duplicating it (2026-06-07).**
  The rigidity-on-`V(G)` step C1 needs already existed as
  `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows`, which used its pointwise `hmem`
  hypothesis only to build the span containment `hsub`. Factored the body into a span-containment core
  `BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` (takes `hsub`
  directly), kept the pointwise form as a one-line wrapper, and built C1
  (`hasFullRankRealization_of_independent_rigidityRow`) by wrapping the core into the
  `HasFullRankRealization` existential at the fixed `ofNormals` placement. Also weakened
  `exists_good_realization_const`'s `hspanrows` `=`→`≤` (its `hcoord` leg is `dualCoannihilator_anti`,
  anti-monotone — only the one caller `hglue_of_realization` needed `.le`). **C1 lives in CaseI.lean,
  not GenericityDevice as §1.35 said** — `exists_good_realization_const` is in CaseI and the import
  runs CaseI → GenericityDevice, so C1 can't sit upstream; the rank-nullity closure it actually turns
  on is the CaseI core anyway, so this is the natural home.
- **L-wire corrected: device feed is the fixed-framework `_const` route, not the panelRow-shaped feed
  (2026-06-07; the recon-of-the-core, `notes/Phase22-realization-design.md` §1.35).** Verified against
  KT §6.4.1 eqs. (6.24)–(6.44): the placed `+1` row is `hingeRow v b r̂` (`r̂(C(e_b)) ≠ 0`) — provably
  not a single `panelRow`, but in `span rigidityRows` (a combination of `e_b`-panelRows). The
  `_ofParam`/`hasFullRankRealization_of_independent_panelRow[_index]` feed needs the literal panelRow
  shape (its `hg` is the `annihRowPoly` coordinatization), so route (A)-as-stated and route (B) both
  fail; the corrected feed is the genericity-free, fixed-framework `exists_good_realization_const`
  (constant family, `hg = eval_C`, span-⊆-rigidityRows) + `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`.
  Corrected leaf sequence C1–C5 in §1.35. (Supersedes §1.34's panelRow-feed framing + the prior "swap
  the `r̂`-row by the collapse" Hand-off, which conflated the producer's `r̂` with
  `exists_candidate_row_eq612`'s block `ρ`.)
- **The swap core + columnOp bridge + L5-pack/L3 are green lemmas but off the live route (2026-06-07;
  one-line record).** `linearIndependent_sumElim_candidateRow_swap` (the eq.-(6.27) row-op invariance),
  `columnOp_apply_single`/`comp_columnOp_comp_single`, and `candidateCompletion_panelRow_packaging`/
  `panelRow_eq_hingeRow_annihRow_of_ends` (the `annihRow`-shaped-`ρ` identity) all hold, but none is on
  the corrected route: the placed candidate row is not `annihRow`-shaped and cannot be swapped for a
  single panelRow (different cosets, §1.35 finding 1). Reusable; not consumed by C1–C5.
- **Leaves L0–L5-inj landed earlier this phase (2026-06-07; one-line record, full detail in the Lean
  source + git):**
  - L0 `case_III_hsplit_producer` (CaseI.lean) — the green-modulo spine carrying `hselᵢ`/`hfamᵢ`/`hjᵢ`/
    `hcardᵢ`, composing `case_III_eq629_conditional` → `…_index` per disjunct;
    `case_III_eq629_conditional` generalized to three index types (FRICTION `[resolved]`). **Its
    `hfamᵢ = panelRow ∘ jᵢ` contract is superseded by §1.35; C3 restates it to the C2 conclusion.**
  - L1 `case_III_old_new_blocks` (CaseI.lean) — the front of `case_II_placement_eq612` re-exposed to
    output the OLD `so` / NEW `sn` blocks separately (verbatim proof; re-exposed since the packaged set
    hides the two-block split the `+1` augment needs).
  - L2 `span_panelRow_comp_single_of_edge` (Pinning.lean) — the candidate producers' `hspan` (pinned
    `D−1` rows span `hingeRowBlock e`), `eq_of_le_of_finrank_eq`; the `comp Φ` is identity at the pin.
  - L3 `panelRow_eq_hingeRow_annihRow_of_ends` (Pinning.lean) — the `annihRow`-shaped-`ρ` candidate-row
    identity; `rw [panelRow, hends]`, graph-free. Off the live route (§1.35 finding 1: the placed row
    is not `annihRow`-shaped); reusable lemma.
  - L4 `panelRow_mem_rigidityRows_of_link` (Pinning.lean) — the `+1` summand's `rigidityRows`
    membership at `e_a` via its *direct* `G`-link (closes F2); graph-free.
  - L5-inj `candidateCompletion_index_injective` (CaseI.lean) — `j` over `(sn ⊕ Unit) ⊕ so` injective,
    abstract over the three disjointness facts (incl. the new `hso_ne_ea` L1 doesn't emit); graph-free.
- **`hsplit` producer core cracked: green-modulo-skeleton-first, defeq trap isolated to one leaf
  (2026-06-07).** Decided the green-modulo-skeleton route (state the producer carrying the residual
  graph-data obligations as explicit `h…`, flip the spine first, discharge each as a leaf) over
  all-at-once — it converts the "multi-session blob" into named leaves. (The §1.34 cut routed the
  finished family through a panelRow-shaped device feed; §1.35 corrects that — the L0–L5 row-block
  bricks survive as infra, the feed and the L0 `hfamᵢ` contract change. F2 holds: `case_II_placement_eq612`
  needs `Gv ≤ G` for one membership step only, transport graph-free, reused verbatim.) Full corrected
  cut + leaf shapes: `notes/Phase22-realization-design.md` §1.35.
- **Device-closure feed lifted to an abstract index, decoupling the producer's packaging from
  `case_II_placement_eq612` (2026-06-07).** `hasFullRankRealization_of_independent_panelRow_index`
  repackages the `Set`-indexed device closure to consume a finite `ι` + injective `j` — the shape of
  the candidate-completion's `Sum`-indexed output. Built green by reindexing across
  `Equiv.ofInjective j` + `Nat.card_range_of_injective`, lifting the inline packaging out of
  `case_II_placement_eq612` (CaseI.lean:2757–2818). No defeq trap (it is the already-green closure
  under an index bijection). Internal infra — no blueprint node (a `Set`-free restatement of an
  already-blueprinted lemma; churn-prone glue, below the selection bar). **NB (§1.35): the candidate
  path does NOT reuse this `_index` feed — its `+1` row is not a panelRow, so it routes through the
  fixed-framework `exists_good_realization_const` (C1) instead. `_index` stays the eq.-(6.12) brick's
  own feed.**
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
- *The unit-normalized combination from a span-of-the-others membership*
  (`exists_smul_combination_eq_sub_of_mem_span_image_compl`) → FRICTION [mirrored].
- *The standard-basis `Basis.toDual` self-pairing is the dot product* (`Pi.basisFun_toDual_apply`)
  → FRICTION [mirrored].
- *`rw [eq]` of a function-valued term over-rewrites its partial applications — narrow with
  `conv_lhs`/`nth_rewrite`* → TACTICS-QUIRKS § 41.
