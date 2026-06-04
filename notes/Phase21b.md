# Phase 21b — Genericity device + realization-layer re-plan (work log)

**Status:** in progress (opened 2026-06-03; realization layer re-planned 2026-06-04).

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

**RED — realization spine, re-stated against the relativized motive:**
- [ ] `thm:theorem-55` — recursion compiles motive-agnostically (`theorem_55` green as a
  conditional); node stays red until its producers land.
- [ ] `prop:rigidity-matrix-prop11` — depends on the re-stated `theorem_55`.

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

**RED — realization producers (no `\lean` yet; the genuine build):**
- [ ] `lem:case-I-splice-placement` — exhibit one parent `F` realizing both legs at a generic point
  (the witness-transfer; intersection of two Zariski-open rigid loci). The placement-construction half
  the glue does not supply. **Item 4b (genuine geometric content).**
- [ ] `lem:case-I-realization` — compose placement + B0 + device ⇒
  `HasFullRankRealization` (the device-direct producer, NOT the retired closure). **Item 5.**
- [ ] `lem:case-II-realization` — the shallower 1-extension producer (one
  re-inserted body, `+(D−1)` rows, KT 6.12). **Item 6.**
- [ ] `lem:case-III` — deferred to Phases 22–23.

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

- **Motive relativization (gating commit) DONE (item 1, 2026-06-05).** The
  realization motive is now `V(G)`-relative (`IsInfinitesimallyRigidOn V(G)`); the
  rank-equality bridge `IsInfinitesimallyRigidOn V(G) ↔ finrank (span rigidityRows)
  = D·(V(G).ncard−1)` was **not** built this commit (the base case proves constancy
  directly, not via the rank bridge) — it is a leaf the producers (items 4–6) need,
  build on contact.
- ~~**Accounting iffs (`lem:case-I`/`lem:case-II`) are nullity-side, α-dependent.**~~
  **DONE (item 2, 2026-06-05).** Decision: re-state rank-side as two new genericity-free,
  α-independent rigidity bridges (`isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` for Case I,
  `isInfinitesimallyRigidOn_insert_iff` for Case II); **keep** the nullity iffs as the α-dependent
  siblings for the deficiency / Prop 1.1 path. These are the rank-side legs the producers (items
  4–6) consume to convert their seeds/realizations into `IsInfinitesimallyRigidOn V(G)`.
- **`prop:rigidity-matrix-prop11`'s `hub`** (genericity-free upper bound, the
  Phase-19-partition count `D + def ≤ dim Z`) is still an untracked obligation
  carried as a hypothesis. Independent of the motive fix.
- **Case III** (`lem:case-III`) deferred to Phases 22–23.

## Hand-off / next phase

**For the `coordinate-phase` orchestrator:** the items below are an ordered
single-commit sequence; do them top to bottom, re-reading this section after
each commit (the building subagent updates it). Each commit lands Lean + flips
its blueprint node's `\leanok` (or adds green infra) + updates this file. The
device is green and `B0`'s coordinate core is validated, so this is build work,
not research. **Do not** re-introduce the retired vacuous lemmas.

**Next concrete commit: item 4b — `lem:case-I-splice-placement`** (items 1–4 landed: 1–2 on
2026-06-05; item 3, the B0 keystone `lem:rows-polynomial-in-normals` GREEN, on 2026-06-06; item 4,
the Case-I splice **glue** `lem:case-I-splice-seed` GREEN, on 2026-06-06 —
`isInfinitesimallyRigidOn_of_splice`, see *Current state*). The remaining genuine geometric content
is the **placement** `lem:case-I-splice-placement`: exhibit one parent framework `F` on `G`
realizing *both* legs simultaneously — `(F.withGraph H)` rigid on `V(H)` AND `(F.withGraph G/E(H))`
rigid on `V(G/E(H))` — by transporting the IH realizations of `H` and `G/E(H)` onto a *common*
placement (the witness-transfer / intersection of two Zariski-open rigid loci, lifted by the device
`exists_good_realization_ofParam`). The glue `isInfinitesimallyRigidOn_of_splice` then turns the two
legs into `IsInfinitesimallyRigidOn V(G)`, and item 5 (`lem:case-I-realization`) wraps it as
`HasFullRankRealization`. The witnessed independent subfamily `hindep` the device needs is supplied
by `exists_independent_panelSupportExtensor` through the hinge-row block (the `panelRow` family's
`s`). This is the step the 5-brick decomposition (commit `eb7dda7`) flagged as the crux: the
witness-transfer gap (two legs on one `ofParam` family) and the unexercised non-constant multivariate
path through `exists_good_realization` (consumers used `…_const` only — but B0's
`exists_good_realization_ofParam` now exercises the varying family).

1. ~~**Relativize the realization motive + base case**~~ **DONE (2026-06-05).**
   `IsInfinitesimallyRigidOn` + its API in `RigidityMatrix.lean`;
   `HasFullRankRealization` re-pinned; `theorem_55_base` relative (`hcover` dropped);
   `theorem_55` recursion unchanged; four absolute-motive producers + the orphaned
   vacuous block-internal chain retired; `def:rank-hypothesis` + `lem:theorem-55-base`
   GREEN, `thm:theorem-55` red (producers red). Nullity `RankHypothesis` + accounting
   iffs retained. *The rank-equality bridge `IsInfinitesimallyRigidOn V(G) ↔ finrank
   (span rigidityRows) = D·(V(G).ncard−1)` was NOT built — it is a producer-side leaf
   (items 4–6 need it; build on contact).*

2. ~~**Re-state the Case-I / Case-II accounting**~~ **DONE (2026-06-05).** Two genericity-free,
   α-independent rigidity bridges in `AlgebraicInduction.lean`:
   `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` (Case I) +
   `isInfinitesimallyRigidOn_insert_iff` (Case II). Nullity iffs **kept** as α-dependent siblings.
   `lem:case-I` / `lem:case-II` flipped GREEN-modulo-21b (relative bridge `\leanok`'d; device leg is
   the `\uses`'d green-modulo node). *These are the rank-side legs items 4–6 consume to convert
   their seeds into `IsInfinitesimallyRigidOn V(G)`.*

3. ~~**B0 — `lem:rows-polynomial-in-normals`** (the keystone)~~ **DONE (2026-06-06, GREEN).**
   `PanelHingeFramework.exists_good_realization_ofParam` — the device closure on the varying panel
   family `ofNormals G ends q`. Sub-commits 1–3 (the polynomial bricks `normalsJoin{Poly}`,
   `panelSupportPoly`, `annihRow{Poly}` + `span_annihRow_eq_dualAnnihilator`) landed 2026-06-04…06;
   sub-commit 4 (the closure) on 2026-06-06 with three new bricks: `ofNormals` (free-normal panel
   framework), `exists_good_realization_reindex` (basis-flexible device wrapper), `panelRow` +
   `span_panelRow_eq_rigidityRows`; the device's `hcoord` was generalized to a `≤`-containment (it
   must hold at degenerate output normals, where the family under-spans). See *Current state* +
   *Decisions made*.

4. ~~**`lem:case-I-splice-seed`** (the glue half)~~ **DONE (2026-06-06, GREEN).**
   `BodyHingeFramework.isInfinitesimallyRigidOn_of_splice` — the block-triangular glue: from two
   legs realized on a common `F` (`(F.withGraph H)` rigid on `V(H)`, `(F.withGraph G/E(H))` rigid on
   `V(G/E(H))`, sharing a body, covering `V(G)`), `F` is `IsInfinitesimallyRigidOn V(G)`. Bricks:
   `isInfinitesimallyRigidOn_union_of_inter`, `isInfinitesimallyRigidOn_of_withGraph_of_le`. The
   placement-construction half split out as `lem:case-I-splice-placement` (item 4b).

4b. **`lem:case-I-splice-placement`** — exhibit one parent `F` realizing *both* legs at a generic
   point: transport the IH realizations of `H` and `G/E(H)` onto a *common* placement (witness-
   transfer / intersection of two Zariski-open rigid loci, lifted by `exists_good_realization_ofParam`).
   The glue `isInfinitesimallyRigidOn_of_splice` then concludes. The genuine geometric content of
   Case I; certify block-triangular row independence via pin-a-body Lemma 5.1's column split.

5. **`lem:case-I-realization`** — compose splice-placement + glue + B0 + device ⇒
   `HasFullRankRealization k G`. Discharges `theorem_55`'s `hcontract`.

6. **`lem:case-II-realization`** — the shallower 1-extension producer: re-insert
   the degree-2 body `v` with a general-position panel normal (KT 6.12), `+(D−1)`
   rows; discharges `hsplit`. Parallel to 4–5 but single-body.

7. **`prop:rigidity-matrix-prop11`** — re-close against the re-stated
   `theorem_55`; brick `hub` (Phase-19 partition count) — independent, may be
   done any time.

**Process lessons (don't repeat).** (a) Build the keystone / validate the
target shape *before* growing a reduction chain (`DESIGN.md` *Forward-mode
reduction chains*). (b) A producer hypothesis must be **satisfiable**, not just
type-correct — check it against a concrete small instance (the retired Case-I
carrier and the absolute base case both failed this). (c) For a vertex-reducing
induction, the realization motive must be carried relative to `V(G)`, not
absolute over the ambient body type.

**Session note.** `origin/master` was inadvertently pushed once an earlier
session; commits since are local. Match author `bryangingechen@gmail.com`; do
**not** push without asking.
