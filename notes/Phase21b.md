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

**Item 3 IN PROGRESS (2026-06-05): B0 sub-commit 2 — the panel-support-extensor coordinate is
landed as a degree-2 `MvPolynomial`.** `panelSupportPoly u v t = ∑ s, m(t,s)·normalsJoinPoly u v s`
(in `AlgebraicInduction.lean`): a `⋀^k`-coordinate (in the standard exterior-power basis of
`ScrewSpace k = ⋀^k ℝ^(k+2)`, indexed by `k`-element subsets `t`) of the panel support extensor
`panelSupportExtensor (q(u,·)) (q(v,·)) = complementIso (normalsJoin …)`. The complement iso is a
*fixed* `LinearEquiv`, so each `⋀^k`-coordinate is the fixed linear combination
`m(t,s) = repr_k (complementIso (b₂ s)) t` of the sub-commit-1 `⋀²`-minors `normalsJoinPoly u v s`,
hence stays degree-2: `panelSupportPoly_eval` (eval at panel coords = the `⋀^k`-coordinate) +
`panelSupportPoly_totalDegree_le` (`totalDegree ≤ 2`). The eval proof routes the coordinate through
the `ℝ`-valued composite `Finsupp.lapply t ∘ₗ repr_k.toLinearMap ∘ₗ complementIso.toLinearMap` so
`map_sum` can push it through the two sums (the `Finsupp`-codomain `map_sum` snag — TACTICS-QUIRKS
§34). Sub-commit 1 (`normalsJoin_basis_repr` + `normalsJoinPoly{,_eval,_totalDegree_le}`, the `⋀²`
minor) landed 2026-06-04. The B0 node `lem:rows-polynomial-in-normals` stays **RED** (the full
device-input assembly — the per-edge `{Cᵢeⱼ*−Cⱼeᵢ*}` annihilator family, then `g`/`c`/`φ`/`hg` and
invoking `exists_good_realization` — is the remaining keystone build). Build + lint clean,
axiom-clean {propext, Classical.choice, Quot.sound}. **Next B0 sub-commits:** the per-edge
annihilator family `{Cᵢeⱼ*−Cⱼeᵢ*}` (linear in `C`), then assemble `c`/`g`/`hg` and invoke the
device.

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

**RED — realization producers (no `\lean` yet; the genuine build):**
- [ ] `lem:rows-polynomial-in-normals` (**B0, keystone**) — coordinatize the
  panel-normal rows as degree-2 `MvPolynomial`, packaging the device's
  `g`/`c`/`φ`/`hg` (`hcoord` = green `infinitesimalMotions_eq_dualCoannihilator`). **Item 3.**
  Sub-commit 1 (2026-06-04) LANDED the `⋀²`-minor core: `normalsJoin_basis_repr`
  (`⋀²`-coordinate = `2×2` minor), `normalsJoinPoly` + `normalsJoinPoly_eval` +
  `normalsJoinPoly_totalDegree_le` (the degree-2 `MvPolynomial` lift). Sub-commit 2
  (2026-06-05) LANDED the `⋀^k` panel-support-extensor coordinate through `complementIso`:
  `panelSupportPoly` + `panelSupportPoly_eval` + `panelSupportPoly_totalDegree_le` (degree
  stays 2 under the fixed linear iso). Node stays RED (per-edge annihilator family + device
  assembly remain).
- [ ] `lem:case-I-splice-seed` — one placement `p₀` with `D(|V(G)|−1)`
  independent parent rows, block-triangular from the two IH legs
  (genericity-free). **Item 4.**
- [ ] `lem:case-I-realization` — compose B0 + splice-seed + device ⇒
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

**Next concrete commit: item 3, B0 sub-commit 3** (items 1–2 landed 2026-06-05;
item 3 sub-commit 1 — the `⋀²` minor `normalsJoin_basis_repr` +
`normalsJoinPoly{,_eval,_totalDegree_le}` — landed 2026-06-04; item 3 sub-commit 2 — the `⋀^k`
panel-support-extensor coordinate `panelSupportPoly{,_eval,_totalDegree_le}` through `complementIso`
— landed 2026-06-05; node still RED).
Next: the per-edge annihilator family `{Cᵢeⱼ*−Cⱼeᵢ*}` (linear in `C`) on the `panelSupportPoly`
coordinates, then assemble the device inputs `g`/`c`/`hg` and invoke `exists_good_realization`,
flipping the B0 node `\leanok`.

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

3. **B0 — `lem:rows-polynomial-in-normals`** (the keystone; likely 2–4 commits,
   builder decomposes). Build the device inputs for the panel-normal family:
   `g` = the rigidity-row functionals, `c` = their degree-2 `MvPolynomial`
   coordinates (via the validated `normalsJoin` minor + `complementIso` linear +
   the `{Cᵢeⱼ*−Cⱼeᵢ*}` annihilator family), `φ` = a basis coordinate iso,
   `hg` = the eval identity, `hcoord` = green
   `infinitesimalMotions_eq_dualCoannihilator`. Seed point `p₀` = moment-curve normals (reuse
   `isGeneralPosition_ofParam` + `exists_independent_rigidityRows_of_forest`).
   - ~~Sub-commit 1: lift the `⋀²`-coordinate bilinearity to a coordinate-as-`MvPolynomial`
     lemma.~~ **DONE (2026-06-04):** `normalsJoin_basis_repr` (`⋀²`-coord = `2×2` minor),
     `normalsJoinPoly` + `normalsJoinPoly_eval` + `normalsJoinPoly_totalDegree_le` (degree-2
     `MvPolynomial` lift). Node still RED.
   - ~~Sub-commit 2: push that `MvPolynomial` coordinate through the fixed linear
     `complementIso` to a `panelSupportExtensor`-coordinate-as-`MvPolynomial` (degree stays 2).~~
     **DONE (2026-06-05):** `panelSupportPoly` + `panelSupportPoly_eval` +
     `panelSupportPoly_totalDegree_le` (the `⋀^k`-coordinate of `panelSupportExtensor` as a
     degree-2 `MvPolynomial`, `m(t,s) = repr_k (complementIso (b₂ s)) t` the fixed-iso matrix
     coefficient). Node still RED. (Friction: the `Finsupp`-codomain `map_sum` snag — route the
     coordinate through `Finsupp.lapply t ∘ₗ repr.toLinearMap`; TACTICS-QUIRKS §34.)
   - Sub-commit 3 (next): the `{Cᵢeⱼ*−Cⱼeᵢ*}` per-edge annihilator family (linear in `C`) on the
     `panelSupportPoly` coordinates, then assemble `g`/`c`/`hg`, invoke `exists_good_realization`;
     flip the node `\leanok`.

4. **`lem:case-I-splice-seed`** — construct `p₀` on `G` with `D(|V(G)|−1)`
   independent parent rows: transport the IH realizations of `H` and `G/E(H)`
   onto `G` and certify block-triangular row independence (genericity-free, via
   pin-a-body Lemma 5.1's column split). The genuine geometric content of Case I.

5. **`lem:case-I-realization`** — compose B0 + splice-seed + device ⇒
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
