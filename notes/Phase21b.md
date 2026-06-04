# Phase 21b — Genericity device + realization-layer re-plan (work log)

**Status:** in progress (opened 2026-06-03; realization layer re-planned 2026-06-04;
node-decomposition re-plan 2026-06-06, cold-start-ready hand-off below).

Sub-phase scoped out of Phase 21 on 2026-06-03 (user decision, risk #4/#7),
the **analytic sibling** of the Phase-21a meet sub-phase. Two things live here
now: (1) the genuinely-new analytic crux of Katoh–Tanigawa's algebraic
induction — Claim 6.4/6.9, the **genericity device** (rigidity-matrix entries
are polynomials in the panel coordinates, so a single good realization lifts to
a generic one) — which is **GREEN**; and (2) the **realization layer** of
Theorem 5.5 (the producers exhibiting a rigid panel framework for each
inductive case), which a 2026-06-04 spike found was built on a **mis-defined
motive** and is being **re-planned** around the corrected one.

Program-level plan, reuse map, citations: `notes/MolecularConjecture.md`
*Phase 21b*. Scope-out rationale + node-by-node consumer split: `DESIGN.md`
*Genericity device …* + *Forward-mode reduction chains* + *Realization motive
must be V(G)-relative …*. Forward-mode dep-graph:
`blueprint/src/chapter/algebraic-induction.tex`
(`sec:molecular-algebraic-induction`). Lean is in
`CombinatorialRigidity/Molecular/AlgebraicInduction.lean` + mirror bricks under
`CombinatorialRigidity/Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`.

## Current state

**RE-PLAN LANDED (2026-06-06, planning commit): the realization layer is decomposed into an explicit
cold-start-ready node list; two prior mis-assessments corrected.** A spike + two recons (device
internals; the graph-contraction infra; the `apnelson1/Matroid` dependency) firmed up the remaining
work; the Hand-off below is now an ordered node list a fresh `coordinate-phase 21b` agent can run
top-to-bottom. Key outcomes:
1. The device's output is an **absolute** codimension bound `#s + dim Z(G,p) ≤ D·card α` over the
   ambient body type, so the producers need a **`V(G)`-relative count bridge** (new red nodes
   `lem:relative-screw-split` / `lem:relative-device-count` / `lem:isInfRigidOn-of-relative-count`,
   N1–N3) — **build-shaped, the next concrete commit**; the shape was MCP-validated as a `sorry`-stub.
2. The rigid-subgraph contraction is **mostly built, NOT fully.** `rigidContract` (`Induction.lean:1854`),
   its vertex-drop (`:1869`), and the matroid-side `contraction_isMinimalKDof` (`:1998`) are green, but
   the graph↔matroid minimality bridge `(rigidContract).IsMinimalKDof` (new red node
   `lem:rigidContract-isMinimalKDof`, N4) is a **deliberate Phase-20 carry-forward gating Case I**
   (comment `Induction.lean:2956–2961`). An earlier spike mis-read this as "no graph-level contraction
   exists" (wrong) and a recon over-corrected to "contraction done" (also wrong); the truth is N4.
3. **`thm:theorem-55` does NOT flip in Phase 21b.** Its recursion needs all three case-producers, and
   Case III (`lem:case-III`) is deferred to Phases 22–23, where `theorem_55` flips. **Phase 21b closes
   when the two producers `lem:case-I-realization` (N6) + `lem:case-II-realization` (N7) are green.**
4. `apnelson1/Matroid` offers **no** reusable leverage; the remaining work is analytic/geometric
   *known-construction* formalization (KT 2011), not open math. The one genuinely hard node is the
   Case-I splice placement `lem:case-I-splice-placement` (N5) — research-shaped geometry that
   **warrants its own decomposition pass** before a build commit.

See the Hand-off section for the ordered list, shape tags, and the recon findings (so a cold agent
need not re-investigate).

**Item 4 LANDED (2026-06-06): Case-I splice GREEN/RED split — the glue half is green, the placement
half is the new red node.** `lem:case-I-splice-seed` was the genuine geometric heart and is now
restated as the block-triangular **glue**: `BodyHingeFramework.isInfinitesimallyRigidOn_of_splice`
(`AlgebraicInduction.lean`) — given a *single* parent framework `F` on `G` realizing both legs
(`(F.withGraph H)` rigid on `V(H)`, `(F.withGraph G/E(H))` rigid on `V(G/E(H))`), sharing a body
`c ∈ sH ∩ sc` and covering `V(G) ⊆ sH ∪ sc`, `F` is `IsInfinitesimallyRigidOn V(G)`. Two new
bricks: `isInfinitesimallyRigidOn_union_of_inter` (`RigidityMatrix.lean` — two overlapping
relatively-rigid pieces glue along a shared body) and `isInfinitesimallyRigidOn_of_withGraph_of_le`
(`AlgebraicInduction.lean` — relative rigidity transports subgraph→parent via
`infinitesimalMotions_le_withGraph_of_le`). The hypotheses are the *satisfiable* inductive facts
(relative rigidity of each piece on a common `F`), NOT the parent rank they conclude — honest per
the producer-scrutiny gate. The **placement-construction half** — exhibiting one `F` realizing both
legs at a generic point (the witness-transfer / intersection of two Zariski-open rigid loci) —
remains the genuine red obligation, split out as the new node `lem:case-I-splice-placement` (matching
the gate's documented `lem:case-I-splice-placement` precedent). Blueprint: `lem:case-I-splice-seed`
restated + flipped GREEN, `lem:case-I-splice-placement` added red, `lem:case-I-realization`'s `\uses`
+ prose updated to compose glue + placement + B0 + device; chapter intro + device-section summary
synced (B0 + glue green, placement + producers red). Build + lint clean, axiom-clean {propext,
Classical.choice, Quot.sound}. **Next: item 5 (`lem:case-I-realization`) — compose the placement +
B0 + device into `HasFullRankRealization`; the splice glue is now available.**

**Item 3 LANDED (2026-06-06): B0 sub-commit 4 — the device closure; `lem:rows-polynomial-in-normals`
GREEN.** `PanelHingeFramework.exists_good_realization_ofParam` in `AlgebraicInduction.lean` assembles
the device input shape on the **varying** panel family `q ↦ (ofNormals G ends q).toBodyHinge`
(`ofNormals` = the free-normal panel framework, `normal a i = q (a,i)`; the moment-curve seed is its
special case, `ofParam_eq_ofNormals_momentCurve`) and invokes the device, producing a generic normal
assignment at the witnessed corank. Three supporting bricks landed alongside:
- **`exists_good_realization_reindex`** — the basis-flexible device wrapper: takes `φ : Dual ≃ₗ
  (ν → ℝ)` against an arbitrary finite basis index `ν` (+ `e : Fin (finrank dual) ≃ ν`) instead of
  the canonical `Fin (finrank …)`, reducing to `exists_good_realization` via
  `LinearEquiv.funCongrLeft ℝ ℝ e` + pulling `c` back along `e`. Lets the closure coordinatize
  against the *concrete* standard basis `Pi.basis (screwBasis k)`, indexed by `Σ _ : α, ⋀^k`-indices.
- **`BodyHingeFramework.panelRow` + `span_panelRow_eq_rigidityRows`** — the explicit
  edge×basis-pair-indexed row family (`hingeRow (ends e).1 (ends e).2 (annihRow C t₁ t₂)`) and the
  proof its span equals `rigidityRows` (given `hends` + transversal `hne`); the orientation
  case-split (`IsLink.eq_and_eq_or_eq_and_eq`) handles `(u,v) = ends e` vs reversed via
  `hingeRow u v r = hingeRow v u (-r)`.
- The device's `hcoord` was **generalized from equality to a `≤`-containment** (`infinitesimalMotions
  ≤ (span (range g)).dualCoannihilator`). This is the keystone fix: at degenerate normals some
  `C(p(e)) = 0`, so the panel-row family `panelRow` *under*-spans `rigidityRows` (annihRow 0 = 0
  there) and equality fails — but the device only needs the bound, and the `⊆` half of
  `span_panelRow` (no transversality) holds at every `q`, including the generic output point. The
  equality consumer (`exists_good_realization_const`) passes `le_of_eq`.

`hg` (the eval identity): `φ (g q i) ⟨a,t⟩ = (g q i) (Pi.single a (sb t))` (`dualBasis_equivFun`) `=
([u=a]−[v=a]) · annihRow C t₁ t₂ (sb t)` (`Pi.single_apply` + `annihRow` linearity) `= eval q (c i
⟨a,t⟩)` with `c i ⟨a,t⟩ = ([u=a]−[v=a]) • annihRowPoly u v t₁ t₂ t` (`annihRowPoly_eval`). Build +
lint clean, axiom-clean {propext, Classical.choice, Quot.sound}. **Next: item 4
(`lem:case-I-splice-seed`) — the genuine geometric Case-I seed.**

Sub-commits 1–3 (the polynomial bricks) landed 2026-06-04…06: `normalsJoin_basis_repr` +
`normalsJoinPoly{,_eval,_totalDegree_le}` (the `⋀²` minor); `panelSupportPoly{,_eval,_totalDegree_le}`
(the `⋀^k` coordinate through `complementIso`); `screwBasis`, `annihRow`
(+`_apply`/`_apply_self`), `span_annihRow_eq_dualAnnihilator`, `annihRowPoly{,_eval,_totalDegree_le}`
(the per-edge annihilator family, panel-coordinatized degree-2).

**Item 2 LANDED (2026-06-05): the Case-I / Case-II accounting is re-stated rank-side.**
Two genericity-free, `α`-independent rigidity bridges in `AlgebraicInduction.lean` give the
relative-motive restatement of the accounting iffs (decision: **re-state rank-side as a new bridge,
keep the nullity iffs**). Case I:
`BodyHingeFramework.isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` — given every motion is
constant on the rigid block `s` (`hblock`, from the rigidly-placed `H`), the framework is rigid on
`t = V(G)` (`s ⊆ t`) iff `pinnedMotionsOn s ≤ pinnedMotionsOn t` (equiv., since `s ⊆ t` gives the
reverse, `pinnedMotionsOn s = pinnedMotionsOn t`). Case II:
`BodyHingeFramework.isInfinitesimallyRigidOn_insert_iff` — rigid on `insert v t` iff rigid on `t`
AND every motion pins `v`'s screw to `t` (`S v = S w ∀ w ∈ t`), the rank-side `+(D−1)` 1-extension
read off the relative motive; the `S v = S w` condition is Claim 6.9's general position the device
supplies. Both reference only `s,t ⊆ V(G)`, so they compose through the vertex-reducing induction
(the absolute nullity bridges concluded `IsInfinitesimallyRigid` from `pinnedMotionsOn s = ⊥`,
unsatisfiable for non-spanning subgraphs). The nullity iffs (`rankHypothesis_iff_finrank_*`) are
**kept** as the `α`-dependent siblings feeding the deficiency / Prop 1.1 path. Blueprint
`lem:case-I` / `lem:case-II` flipped GREEN-modulo-21b (relative bridge `\leanok`'d; device leg is
the `\uses`'d green-modulo node, entering only in the producers). Build + lint clean, axiom-clean
{propext, Classical.choice, Quot.sound}. **Next: item 3 (B0 keystone, `lem:rows-polynomial-in-normals`).**

**Item 1 LANDED (2026-06-05): the motive is relativized + base case green.**
`BodyHingeFramework.IsInfinitesimallyRigidOn (s : Set α)` ("motions constant on `s`") is in
`RigidityMatrix.lean` (with `.mono`, `isInfinitesimallyRigidOn_univ_iff`,
`isInfinitesimallyRigidOn_of_isInfinitesimallyRigid`); `HasFullRankRealization k G` is re-pinned to
`∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`; `theorem_55_base` now concludes
`IsInfinitesimallyRigidOn {u, v}` unconditionally (**`hcover` dropped**, `[Nonempty]`/`[Finite]`
dropped) and `toBodyHinge_rankHypothesis_zero` follows; `theorem_55`'s recursion is unchanged
(motive-agnostic `exact minimal_kdof_reduction …`) and compiles against the new motive. The four
absolute-motive Case-I producers (`hasFullRankRealization_ofParam_of_{pinnedMotionsOn,
isInfinitesimallyRigid,contraction}`, `hasFullRankRealization_of_pinnedMotionsOn`) and the orphaned
vacuous block-internal chain (`isInfinitesimallyRigid_of_le_withGraph`,
`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph`,
`isInfinitesimallyRigid_of_rigid_subgraph_of_{pinnedMotionsOn_eq_bot,block_internal}`,
`pinnedMotionsOn_eq_bot_of_block_internal_rigid`) are **retired** (deleted, retirement note at end
of `AlgebraicInduction.lean`). Blueprint: `def:rank-hypothesis` + `lem:theorem-55-base` flipped
GREEN; `thm:theorem-55` stays red (producers red). The nullity `RankHypothesis` chain + accounting
iffs are retained. Build + lint clean, axiom-clean {propext, Classical.choice, Quot.sound}.
**Next: item 2 (accounting iffs) or item 3 (B0 keystone).**

**The device is GREEN; the realization producers are RED (re-planned 2026-06-04).**
Two spike findings (both verified in Lean) reshaped the plan:

1. **The realization motive was unsatisfiable for the inductive graphs.**
   `HasFullRankRealization k G` unfolds to `RankHypothesis 0`, the *absolute*
   null-space equality `dim Z(G,p) = D` over **all** of `α → ScrewSpace`. That
   equals infinitesimal rigidity only when `G` **spans** `α` — a body in
   `α ∖ V(G)` carries no hinge constraint, hence is a free non-trivial motion
   (verified: a 1-line lemma, an isolated body gives a non-trivial motion). But
   `minimal_kdof_reduction` (the recursion `theorem_55` runs on) reduces to
   graphs with **strictly fewer vertices on the same fixed `α`**, which do not
   span it. So `theorem_55`'s premises `hbase`/`hsplit`/`hcontract` are
   unsatisfiable for `card α ≥ 3` (concrete counterexample: the double edge on
   `{u,v}` inside a 3-body `α` is minimal-0-dof with `|V| = 2` but has no rigid
   realization). `theorem_55` is green only as a conditional over unsatisfiable
   hypotheses. `theorem_55_base`'s `hcover : ∀ w, w = u ∨ w = v` ("`α = {u,v}`")
   is the exposed symptom.

   **Fix (user decision, rank-form):** carry the realization motive in the
   **`V(G)`-relative rank form** `rank R(G,p) = D(|V(G)|−1)` — equivalently
   `finrank (span rigidityRows) = D·(V(G).ncard − 1)`, equivalently "every
   infinitesimal motion is constant on `V(G)`". This is **`α`-independent**
   (isolated bodies contribute no rigidity rows / `rank = D·card α − dim Z`),
   composes through the induction, and **resurrects the block-constancy
   machinery** (which was vacuous only because of the global-`α` rigidity).

2. **The Case-I closure carrier targeted unsatisfiable hypotheses.** The retired
   `hasFullRankRealization_ofParam_of_contraction` /
   `isInfinitesimallyRigid_of_rigid_subgraph_of_block_internal` took as
   hypotheses that two subgraphs `G_H, G_c ≤ G` are *each* infinitesimally rigid
   **over the whole `α`** — false for a proper `H` (same isolated-body argument).
   Under the relativized motive the legs ("`H` realizes its rank", "`G/E(H)`
   realizes its rank") are the **satisfiable** inductive hypotheses, and the
   producer is a **device-direct** composition (B0 + splice-seed + device), not a
   closure over unsatisfiable rigidity inputs.

The device itself (`exists_good_realization` + `exists_good_realization_const`,
on the route-(a) `exists_…_polynomial` engine) is unchanged and green; it is
*motive-independent* (a generic-rank statement). The **B0 keystone** —
coordinatizing the `ofParam`/panel-normal rows as `MvPolynomial` so the device
can be *applied* to a varying realization — was spiked and is feasible/clean:
mathlib's `exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti` +
`Matrix.det_fin_two` give a `⋀²` coordinate of `normalsJoin n₁ n₂` as the
bilinear minor `n₁ᵢn₂ⱼ − n₁ⱼn₂ᵢ` (verified to compile); `complementIso` is a
fixed `LinearEquiv` (stays degree-2); the annihilator spanning family
`{Cᵢeⱼ* − Cⱼeᵢ*}` is linear in `C`.

## Architectural choices made up front

- **Forward-mode, nodes beside the consumers** (unchanged). The realization
  spine + device live in `algebraic-induction.tex`'s
  `sec:molecular-algebraic-induction`.
- **The motive is `V(G)`-relative (rank form).** `def:rank-hypothesis` carries
  `rank R(G,p) = D(|V(G)|−1) − k'`. Recommended Lean carrier: an
  `IsInfinitesimallyRigidOn (s : Set α)` predicate ("motions constant on `s`")
  with `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.toBodyHinge.
  IsInfinitesimallyRigidOn V(G)`; the rank-equality form is the bridge. This
  reuses the block-constancy bricks (resurrected) and `theorem_55_base`'s `key`.
- **Realization is device-direct on the full parent**, not via the (vacuous)
  `withGraph`-subgraph-rigid carrier. The device proves the *full parent* rigid
  (it spans `α`); the per-leg work is the genericity-free splice seed.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`. Tracked
here for hand-off. All `[x]` Lean bricks are axiom-clean {propext,
Classical.choice, Quot.sound}.

**GREEN and motive-independent (retained verbatim):**
- [x] `lem:genericity-device` — `exists_good_realization{,_const}` on the
  multivariate engine `exists_finrank_dualCoannihilator_polynomial` (route (a),
  four mirror bricks: `MvPolynomial.exists_eval_ne_zero`,
  `Matrix.exists_linearIndependent_rows_specialize`,
  `exists_le_finrank_span_polynomial`,
  `exists_finrank_dualCoannihilator_polynomial`).
- [x] Panel layer `def:panel-support-extensor`, `def:panel-hinge-framework`
  (+ `IsGeneralPosition`, moment-curve `withMomentNormals`/`ofParam`).
- [x] All four Lean pieces of `lem:cycle-realization` (base, dim-bound,
  panel-independence reduction, existence) + `lem:cycle-realization-rigid`.
- [x] `R(G,p)` coordinatization: `infinitesimalMotions_eq_dualCoannihilator`,
  `rigidityRows`/`hingeRow`/`screwDiff`, `exists_independent_rigidityRows_of_forest`,
  `exists_finite_spanning_rigidityRows`, `finrank_screwAssignment`.
- [x] `def:framework-with-graph`, `lem:motions-mono-of-graph-le`,
  `def:pinned-motions-on`, `lem:pinned-motions-on-mono`,
  `lem:pinned-motions-on-rank-bound` (the genericity-free block-pin lower bound
  + `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`, the
  block-triangular glue — genuine, reusable under the relativized motive).
- [x] `Graph.endsOf`, `pinnedMotionsOn_withGraph_eq_of_block_internal` (genuine,
  no rigidity hypothesis), the Case-II `withNormal`/`hnew`/edge-substitution
  graph bricks (`lem:case-II-rank-lift`, `lem:splitoff-edge-substitution`).

**GREEN — relativized motive + base (item 1, landed 2026-06-05):**
- [x] `def:rank-hypothesis` — re-pinned to `IsInfinitesimallyRigidOn` +
  `HasFullRankRealization` (the `V(G)`-relative rank form); the nullity
  `RankHypothesis` retained as the accounting-iff carrier.
- [x] `lem:theorem-55-base` — `theorem_55_base` concludes `IsInfinitesimallyRigidOn {u,v}`,
  `hcover` (and `[Nonempty]`/`[Finite]`) dropped; `toBodyHinge_rankHypothesis_zero` follows.

**GREEN-modulo-21b — accounting re-stated rank-side (item 2, landed 2026-06-05):**
- [x] `lem:case-I` — `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` (the genericity-free
  `α`-independent rigidity bridge; rigid on `t` iff `pinnedMotionsOn s ≤ pinnedMotionsOn t` given
  `hblock`-constancy on the rigid block `s`). Nullity iffs kept as `α`-dependent siblings.
- [x] `lem:case-II` — `isInfinitesimallyRigidOn_insert_iff` (rigid on `insert v t` iff rigid on `t`
  + every motion pins `v`'s screw to `t`). Device leg enters only in the producers.

**RED — `V(G)`-relative count bridge (N1–N3, the next build; build-shaped):**
- [ ] `lem:relative-screw-split` (N1) — `dim Z = D(card α − V(G).ncard) + dim Z_{V(G)}` (`finrank_pi`
  product split; the ambient bodies are a free direct summand).
- [ ] `lem:relative-device-count` (N2) — device re-wrapped with N1: a generic point attains
  `#s + dim Z_{V(G)} ≤ D(V(G).ncard − 1)`.
- [ ] `lem:isInfRigidOn-of-relative-count` (N3) — relative full count ⇒ `IsInfinitesimallyRigidOn V(G)`
  (via green `screwDim_add_finrank_pinnedMotionsOn_le` + `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`).

**GREEN — B0 keystone (item 3, landed 2026-06-06):**
- [x] `lem:rows-polynomial-in-normals` (**B0, keystone**) —
  `PanelHingeFramework.exists_good_realization_ofParam`: the device closure on the varying panel
  family `ofNormals G ends q`. Bricks: `ofNormals` (+ `ofParam_eq_ofNormals_momentCurve`),
  `exists_good_realization_reindex` (basis-flexible device), `BodyHingeFramework.panelRow` +
  `span_panelRow_eq_rigidityRows`, and the device's `hcoord` generalized to a `≤`-containment.
  Sub-commits 1–3 (the polynomial bricks `normalsJoin{Poly}`, `panelSupportPoly`, `annihRow{Poly}` +
  `span_annihRow_eq_dualAnnihilator`) landed 2026-06-04…06.

**GREEN — Case-I splice glue (item 4, landed 2026-06-06):**
- [x] `lem:case-I-splice-seed` — `isInfinitesimallyRigidOn_of_splice` (the block-triangular glue:
  two legs realized on a common `F` ⇒ rigid on `V(G)`). Bricks: `isInfinitesimallyRigidOn_union_of_inter`,
  `isInfinitesimallyRigidOn_of_withGraph_of_le`.

**RED — realization producers + the contraction bridge (the genuine build):**
- [ ] `lem:case-II-realization` (N7, after the bridge) — 1-extension producer; needs only N3 + device,
  NOT N4/N5. General-position panel normal (`exists_independent_panelSupportExtensor`), `+(D−1)` rows
  (KT 6.12); `isInfinitesimallyRigidOn_insert_iff` (green) + bridge ⇒ `HasFullRankRealization`.
  Discharges `hsplit`. **The cheapest full producer.**
- [ ] `lem:rigidContract-isMinimalKDof` (N4) — graph↔matroid contraction-minimality bridge:
  `(G.rigidContract H r).IsMinimalKDof n 0` from green matroid-side `contraction_isMinimalKDof`
  + a `matroidMG`-of-`(map ∘ deleteEdges)` correspondence. *Build-shaped but nontrivial*; Phase-20
  carry-forward 1; gates Case I. Independent of N1–N3.
- [ ] `lem:case-I-splice-placement` (N5) — exhibit one `F` realizing both legs at a generic point
  (witness-transfer; KT 6.2/6.6). **The genuinely hard node — dispatch a decomposition pass first.**
- [ ] `lem:case-I-realization` (N6) — compose N4 + N5 + glue + B0 + N3/device ⇒
  `HasFullRankRealization` (device-direct, NOT the retired closure). Discharges `hcontract`.
- [ ] `lem:case-III` — deferred to Phases 22–23.

**RED — capstone (carries beyond Phase 21b; NOT a 21b close-condition):**
- [ ] `thm:theorem-55` — recursion compiles motive-agnostically (`theorem_55` green as a conditional);
  flips in **Phase 23** (needs all three case-producers incl. Case III).
- [ ] `prop:rigidity-matrix-prop11` — depends on `theorem_55` + brick `hub` (Phase-19 partition count);
  independent, may be done any time.

**RETIRED (item 1, deleted — retirement note at end of `AlgebraicInduction.lean`):**
`hasFullRankRealization_ofParam_of_{contraction,isInfinitesimallyRigid,pinnedMotionsOn}`,
`hasFullRankRealization_of_pinnedMotionsOn` (absolute-motive producers);
`isInfinitesimallyRigid_of_le_withGraph`,
`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph`,
`isInfinitesimallyRigid_of_rigid_subgraph_of_{pinnedMotionsOn_eq_bot,block_internal}`,
`pinnedMotionsOn_eq_bot_of_block_internal_rigid` (orphaned vacuous block-internal chain).
The genuine block-pin bricks `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`,
`pinnedMotionsOn_withGraph_eq_of_block_internal`, `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid`,
`finrank_pinnedMotionsOn_eq_zero_of_isInfinitesimallyRigid` are **retained** (reusable, blueprint
`lem:pinned-motions-on-rank-bound`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The Case-I splice splits into a green `glue` + a red `placement`.** The original
  `lem:case-I-splice-seed` promised to *produce a placement* `p₀` with `D(|V(G)|−1)` independent
  rows — a producer, so flipping it green while the Lean *assumes* the two legs' rigidity would
  launder the deliverable (producer-scrutiny gate). Resolution: the Lean `isInfinitesimallyRigidOn_
  of_splice` is the honest **glue** (two legs realized on a common `F` ⇒ rigid on `V(G)`, hypotheses
  satisfiable IH facts), green; the **placement** (one `F` realizing both legs at a generic point —
  the witness-transfer) is the new red node `lem:case-I-splice-placement`. Matches the gate's
  documented `lem:case-I-splice-placement` precedent. → blueprint honesty gate / producer scrutiny.
- **The device's `hcoord` is a `≤`-containment, not equality.** At degenerate panel
  normals some `C(p(e)) = 0`, so the polynomial row family `panelRow` (annihRow 0 = 0)
  *under*-spans `rigidityRows` and the equality `Z = (span (range g))^∘` fails — but the
  device's generic output point is unknown, so it must work at degenerate `q` too. The fix:
  the device only needs `Z ⊆ (span (range g))^∘` (the `⊆`-half of `span_panelRow`, which holds
  at *every* `q`, no transversality); `finrank Z ≤ finrank (…)^∘` then chains into the bound.
  Equality consumers pass `le_of_eq`. → blueprint honesty gate (the family may under-span).
- **B0 coordinatizes against the concrete `Pi.basis (screwBasis k)`, not `Module.finBasis`.**
  `B.dualBasis.equivFun (g i) ⟨a,t⟩ = (g i) (Pi.single a (sb t))` is computable (degree-2 panel
  poly); `Module.finBasis` is opaque. The price is a reindex: `B.dualBasis.equivFun : Dual ≃ₗ
  (ν → ℝ)` with `ν = Σ _ : α, ⋀^k`-indices, bridged to the device's `Fin (finrank dual)` via
  `exists_good_realization_reindex` (`LinearEquiv.funCongrLeft`).
- **The realization motive must be `V(G)`-relative.** The absolute null-space
  form `dim Z = D` is α-dependent and unsatisfiable for non-spanning inductive
  subgraphs. Carry the rank form `rank R = D(|V(G)|−1)`. → `DESIGN.md`
  *Realization motive must be V(G)-relative*.
- **Producer hypotheses must be satisfiable, not just type-correct.** The
  retired Case-I carrier and the absolute base case smuggled unsatisfiable
  rigidity/coverage hypotheses; they typecheck and even prove (vacuously) but
  can never be discharged. → blueprint honesty gate (producer scrutiny).
- **B0 coordinate bilinearity is mathlib-supported** (no new hard mirror):
  `exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti` +
  `Matrix.det_fin_two`. The device parameter is the panel **normals**
  (`σ = α × Fin(k+2)` or moment-param `α`), entries degree-2.
- **The Case-I splice seed is genericity-free.** Block-triangular row
  independence (KT 6.3 + pin-a-body Lemma 5.1 column split) from the two IH
  legs; genericity (the device) only lifts `p₀` to a generic point afterward.
- **Coordinatize `R(G,p)` as a functional family** (carried forward): rows are
  `hingeRow u v r`; `Z = (span rigidityRows).dualCoannihilator`. QUIRKS §30/§32/§33.

### Promoted
- *Forward-mode + linear reduction chain → single-use wrapper sprawl; build the
  keystone first.* → `DESIGN.md` *Forward-mode reduction chains*.
- *A `\leanok`/producer node may not carry a load-bearing hypothesis no node
  discharges — and the hypothesis must be **satisfiable**, not merely
  type-correct.* → `blueprint/CLAUDE.md` *the honesty gate* + *producer scrutiny*.
- *An absolute (ambient-type) rigidity/rank motive over a fixed body type is
  unsatisfiable for non-spanning subgraphs; realization motives in a
  vertex-reducing induction must be carried relative to `V(G)`.* → `DESIGN.md`
  *Realization motive must be V(G)-relative*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive.* →
  TACTICS-QUIRKS § 33.
- *`map_sum` won't push `Basis.repr` (a `LinearEquiv` to `Finsupp`) through a `∑`
  — route the coordinate through `Finsupp.lapply t ∘ₗ repr.toLinearMap`.* →
  TACTICS-QUIRKS § 34.

## Blockers / open questions

- **The `V(G)`-relative count bridge (N1–N3) is the next build** — the producer-side leaf item 1
  flagged. The device's absolute count `#s + dim Z ≤ D·card α` must be adapted to
  `IsInfinitesimallyRigidOn V(G)`. Build-shaped (mathlib `finrank_pi` + the green block-pin bricks);
  shape MCP-validated as a `sorry`-stub. See Hand-off.
- **The graph↔matroid contraction-minimality bridge (N4) is a real, deliberately-deferred obligation
  gating Case I.** `(rigidContract).IsMinimalKDof` is NOT built (Phase-20 carry-forward 1,
  `Induction.lean:2956–2961`); only the matroid side `contraction_isMinimalKDof` is green.
  Build-shaped but nontrivial (the matroid-of-a-mapped-graph identification is the content).
- **The Case-I splice placement (N5) is the one genuinely hard node** — research-shaped geometry
  (KT 6.2/6.6, the witness-transfer); dispatch a decomposition pass before building.
- **`thm:theorem-55` stays red through Phase 21b.** Its recursion needs all three case-producers;
  Case III (`lem:case-III`) is Phases 22–23, where `theorem_55` flips. Phase 21b closes on the two
  producers N6 + N7.
- **`prop:rigidity-matrix-prop11`'s `hub`** (genericity-free upper bound, the Phase-19-partition
  count `D + def ≤ dim Z`) is still an untracked obligation carried as a hypothesis; independent,
  not a 21b close-condition.
- **Case III** (`lem:case-III`) deferred to Phases 22–23.

## Hand-off / next phase

**For the `coordinate-phase` orchestrator (ready for a cold start).** The nodes
below are an ordered list (re-planned 2026-06-06; see the *Current state* top
entry). Do them top to bottom, re-reading this section after each commit (the
building subagent updates it). Each commit lands Lean + flips its blueprint
node's `\leanok` (or adds green infra) + updates this file. **Mind the shape
tags — this is NOT uniformly build work.** Most of the frontier is build-shaped,
but two Case-I nodes are not: `N4` (graph↔matroid contraction bridge) is
build-shaped-but-nontrivial, and `N5` (splice placement) is genuinely hard
geometry that **warrants its own decomposition pass** (dispatch a planning/recon
subagent to break it into sub-nodes) before a single-commit build. **Do not**
re-introduce the retired vacuous lemmas, and **do not** assume the contraction
is fully built (matroid side green; the graph-level `(rigidContract).IsMinimalKDof`
bridge is `N4`, a deliberate Phase-20 carry-forward).

**Next concrete commit: N1–N3, the `V(G)`-relative count bridge** (likely one
commit; the builder may split N1 from N2+N3). The device
(`exists_good_realization_ofParam`, green) produces a generic point with an
*absolute* codimension bound `#s + dim Z(G,p) ≤ D·card α` over the whole ambient
body type; the producers need the relative motive `IsInfinitesimallyRigidOn V(G)`.
Build the adapter (blueprint subsection `sec:molecular-algebraic-induction-relative`):
- **N1 `lem:relative-screw-split`** — `dim Z(G,p) = D(card α − V(G).ncard) +
  dim Z_{V(G)}`, the `Pi`-product split (`finrank_pi`) removing the ambient free
  bodies. The one piece with content; *build-shaped* (a clean free direct
  summand, NOT a relative-rank argument over a non-spanning block).
- **N2 `lem:relative-device-count`** — re-wrap `exists_good_realization` (resp.
  `_ofParam`) with N1 substituted for `finrank_screwAssignment`: a generic point
  attains `#s + dim Z_{V(G)} ≤ D(V(G).ncard − 1)`. Mechanical.
- **N3 `lem:isInfRigidOn-of-relative-count`** — from the relative full count
  (`k'=0`) conclude `IsInfinitesimallyRigidOn V(G)`, via the green
  `screwDim_add_finrank_pinnedMotionsOn_le` (`lem:pinned-motions-on-rank-bound`)
  + `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` (`lem:case-I`). Mechanical;
  shape MCP-validated as a `sorry`-stub during the 2026-06-06 spike.

Then, in order:
1. **N7 `lem:case-II-realization`** — the cheapest full producer: needs only the
   bridge (N3) + device, NOT N4/N5. Re-insert the degree-2 body `v` with a
   general-position panel normal (`exists_independent_panelSupportExtensor`),
   `+(D−1)` rows (KT 6.12); `isInfinitesimallyRigidOn_insert_iff` (green) + the
   bridge ⇒ `HasFullRankRealization`. Discharges `theorem_55`'s `hsplit`.
2. **N4 `lem:rigidContract-isMinimalKDof`** — the graph↔matroid contraction
   bridge (independent of N1–N3; may land any time after them): `(G.rigidContract
   H r).IsMinimalKDof n 0` from the green matroid-side `contraction_isMinimalKDof`
   (`Induction.lean:1998`) + a `matroidMG`-of-`(map ∘ deleteEdges)` correspondence.
   *Build-shaped but nontrivial* (the matroid-of-a-mapped-graph identification is
   the content). Gates the Case-I IH application. Phase-20 carry-forward 1
   (`Induction.lean:2956–2961`).
3. **N5 `lem:case-I-splice-placement`** — the genuinely hard node. **Dispatch a
   planning/recon pass first** to decompose KT eqs. (6.2)/(6.6) (the
   boundary-panel intersection + combined block-triangular independence) into
   build-shaped sub-nodes, then build. Exhibit one parent `F` realizing both legs
   at a generic point; the glue `isInfinitesimallyRigidOn_of_splice` (green) + the
   device lift then conclude. The independent subfamily `hindep` the device needs
   comes from `exists_independent_panelSupportExtensor` through the hinge-row block
   (the `panelRow` family's `s`).
4. **N6 `lem:case-I-realization`** — compose N4 + N5 + glue + B0 + N3/device ⇒
   `HasFullRankRealization k G`. Discharges `theorem_55`'s `hcontract`.

**Phase 21b closes when N6 + N7 are green.** It does NOT flip `thm:theorem-55`:
the recursion needs all three case-producers, and Case III (`lem:case-III`, the
no-rigid-subgraph branch) is deferred to **Phases 22–23**, where `theorem_55`
flips. `prop:rigidity-matrix-prop11` (re-close against `theorem_55`; brick `hub`,
the Phase-19 partition count) likewise carries to a later phase — independent,
not a 21b close-condition.

**Recon findings backing this plan (2026-06-06; a cold agent need not
re-investigate):**
- `apnelson1/Matroid` holds **no** reusable infrastructure for the remaining
  work — no `Pi`-finrank / relative-rank utilities (N1–N3 build from mathlib
  `finrank_pi`), no generic-realization machinery; its contraction/minor API is
  clean but the project operates at the graph layer. The remaining work is
  analytic/geometric *known-construction* formalization (KT 2011), not open math.
- The contraction is **mostly built, not fully** (see N4): an earlier spike
  mis-read it as "no graph-level contraction exists" (wrong — `rigidContract`
  exists) and a recon over-corrected to "contraction done" (wrong — N4 is the
  residual graph↔matroid bridge). Lesson: cross-check the actual statement
  (matroid-side vs graph-side), not the name.

**Completed items (chronological; per-item detail in the *Current state* entries above):**
- **Item 1 (2026-06-05):** motive relativized to `IsInfinitesimallyRigidOn`, base case green,
  absolute-motive producers retired (`def:rank-hypothesis` + `lem:theorem-55-base` green).
- **Item 2 (2026-06-05):** Case-I/II accounting re-stated rank-side
  (`isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` / `isInfinitesimallyRigidOn_insert_iff`;
  `lem:case-I` / `lem:case-II` green-modulo-21b); nullity iffs kept.
- **Item 3 (2026-06-04…06):** B0 keystone `lem:rows-polynomial-in-normals` green
  (`exists_good_realization_ofParam`, the device closure on the varying panel family).
- **Item 4 (2026-06-06):** Case-I splice **glue** `lem:case-I-splice-seed` green
  (`isInfinitesimallyRigidOn_of_splice`); the placement half split out as N5 above.

**Process lessons (don't repeat).** (a) Build the keystone / validate the
target shape *before* growing a reduction chain (`DESIGN.md` *Forward-mode
reduction chains*). (b) A producer hypothesis must be **satisfiable**, not just
type-correct — check it against a concrete small instance (the retired Case-I
carrier and the absolute base case both failed this). (c) For a vertex-reducing
induction, the realization motive must be carried relative to `V(G)`, not
absolute over the ambient body type. (d) When assessing whether existing work
covers a need, a single name-search misleads in *both* directions — a spike
called the rigid-subgraph contraction "missing" (wrong) and a recon called it
"done" (also wrong); the truth (the matroid side is green, the graph-level
`(rigidContract).IsMinimalKDof` bridge `N4` is not) only surfaced by reading the
actual statement (matroid-side vs graph-side) and the deliberate-deferral comment
at `Induction.lean:2956–2961`. Cross-check statements, not names.

**Session note.** `origin/master` was inadvertently pushed once an earlier
session; commits since are local. Match author `bryangingechen@gmail.com`; do
**not** push without asking.
