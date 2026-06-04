# Phase 21b — Genericity device + realization layer (work log)

**Status:** in progress (opened 2026-06-03; realization layer re-planned
2026-06-04; node-decomposition re-plan 2026-06-06; N7 decomposed into glue +
placement 2026-06-04; N7b placement decomposed into N7b-1/2/3 2026-06-04; N7b-1/2/3 GREEN
2026-06-04; N7b-1 honest index-subfamily bridge GREEN 2026-06-04 — the honesty-gate
resolution for the N7b assembly's new block). Cold-start-ready hand-off below.

Sub-phase scoped out of Phase 21 (user decision, risk #4/#7) — the **analytic
sibling** of the Phase-21a meet. Two halves: (1) the **genericity device**
(Claim 6.4/6.9 — rigidity-matrix entries are polynomials in the panel
coordinates, so one good realization lifts to a generic one), **GREEN**; and
(2) the **realization layer** of Theorem 5.5 (producers exhibiting a rigid
panel framework for each inductive case), the remaining build.

Forward-mode: the authoritative node list + green inventory is the blueprint
dep-graph `algebraic-induction.tex` (`sec:molecular-algebraic-induction`). This
file carries state, decisions, blockers, and the ordered hand-off — it does
*not* duplicate the dep-graph. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 21b*. Lean:
`Molecular/AlgebraicInduction.lean` + mirror bricks under
`Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative* + *Forward-mode reduction
chains* + *Genericity device …*.

## Current state

**Green: the device + the realization-layer scaffolding.** The device
(`exists_good_realization{,_const,_ofParam}`), the panel layer, the
cycle-realization, the `R(G,p)` coordinatization, the block-pin machinery, the
relativized motive + base case (`def:rank-hypothesis`, `lem:theorem-55-base`),
the rank-side accounting iffs (`lem:case-I` / `lem:case-II`, green-modulo-21b),
the **B0 keystone** (`lem:rows-polynomial-in-normals` — the device closure on the
*varying* panel family), the Case-I splice **glue** (`lem:case-I-splice-seed`), the
**`V(G)`-relative count bridge N1–N3** (`lem:relative-screw-split` /
`lem:relative-device-count` / `lem:isInfRigidOn-of-relative-count`), and the **three Case-II
placement sub-nodes N7b-1/N7b-2/N7b-3** (`lem:case-II-placement-new-rows` — a transversal hinge's
`D−1` independent panel rows, now also in the **honest index-subfamily form**
`exists_independent_panelRow_subfamily_of_edge` — an actual `panelRow ends`-index-subset of size
`D−1`, the honesty-gate input N7a wants; `lem:case-II-placement-old-rows` — the inductive rows'
`ofNormals` graph-swap transport; `lem:case-II-placement-block-independent` — the abstract pin-a-body
column split joining the two blocks) are all green and axiom-clean {propext, Classical.choice,
Quot.sound}. (Authoritative inventory: the blueprint dep-graph. Per-commit history: *Completed
items* in the Hand-off.) **The next concrete commit is the N7b assembly** (combine the new
index-subset with an old index-subset on `G`, build the seed `q₀`, join via N7b-3); the
functional-vs-`panelRow` laundering risk the prior hand-off flagged is resolved for the new block.

**Remaining: the realization producers, re-planned 2026-06-06** into the ordered
node list in the Hand-off. Three forward facts shape the plan:
- The device's output is an **absolute** codimension bound `#s + dim Z ≤ D·card α`
  over the ambient body type; the producers need the **`V(G)`-relative motive**
  `IsInfinitesimallyRigidOn V(G)`. The adapter is the relative-count bridge
  **N1–N3**, now **GREEN** (landed 2026-06-04). **The device-to-motive glue
  `hasFullRankRealization_of_independent_panelRow` (`lem:realization-of-independent-rows`)
  is also GREEN (2026-06-04):** the honest `N2 ∘ N3` closure shared by both
  producers — a witnessed independent `panelRow` family of size `D(|V(G)|−1)` at one
  seed `q₀` ⇒ `HasFullRankRealization`. **N7 was NOT a mechanical "N3 + device"
  composition** (the splitting-off `G_v^{ab}` is an *edge substitution* of `G`, not a
  subgraph — it adds the fresh `e₀` and drops `v`'s two edges, so rigidity-on-`t`
  does not free-transport; the producer must *construct* the seed family across the
  substitution). So N7 was decomposed (mirroring the Case-I glue/placement split):
  the green glue above, plus the genuinely-geometric **placement** node N7b
  (`lem:case-II-realization-placement`, construct the seed `(q₀, s)`). N7b's three
  sub-nodes N7b-1/2/3 are now all green (the `D−1` new rows, the old-row transport,
  the pin-a-body block split); the remaining red is the **N7b assembly** — pick `q₀`/`s`
  and bridge the independent-functionals-in-the-`panelRow`-span to an actual independent
  `panelRow` subfamily of size `D(|V(G)|−1)` that the glue N7a consumes.
- The rigid-subgraph contraction is **mostly built, not fully**: `rigidContract`
  (`Induction.lean:1854`) + its vertex-drop (`:1869`) + the matroid-side
  `contraction_isMinimalKDof` (`:1998`) are green, but the graph↔matroid
  minimality bridge `(rigidContract).IsMinimalKDof` (**N4**) is a deliberate
  Phase-20 carry-forward (`Induction.lean:2956–2961`) that gates Case I.
- `thm:theorem-55` does **not** flip in 21b: its recursion needs all three
  case-producers, and Case III is Phases 22–23. **Phase 21b closes when the two
  producers `lem:case-I-realization` (N6) + `lem:case-II-realization` (N7) are
  green.**

## Architectural choices

- **Forward-mode, nodes beside the consumers.** The realization spine + device
  live in `algebraic-induction.tex` `sec:molecular-algebraic-induction`.
- **The motive is `V(G)`-relative.** `IsInfinitesimallyRigidOn (s : Set α)` =
  "every infinitesimal motion is constant on `s`"; `HasFullRankRealization k G :=
  ∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`. The absolute
  null-space form is `α`-dependent and unsatisfiable for non-spanning inductive
  subgraphs. → `DESIGN.md` *Realization motive must be V(G)-relative*.

## Lemma checklist

Authoritative node list + green inventory: the blueprint dep-graph. Tracked here
only as the RED frontier (the build) + retirements; the Hand-off carries the
per-node detail.

**GREEN — the `V(G)`-relative count bridge (landed 2026-06-04):**
- [x] N1 `lem:relative-screw-split` — `finrank (pinnedMotionsOn V(G)) = D·|V(G)ᶜ|`
  (`finrank_pinnedMotionsOn_vertexSet`; via `iInfKerProjEquiv` + `finrank_pi_const`).
- [x] N2 `lem:relative-device-count` — device re-wrapped relative
  (`exists_relative_full_count_ofParam`; `#s + dim Z ≤ D·|α|` ⇒ `dim Z ≤ D(|V(G)ᶜ|+1)`).
- [x] N3 `lem:isInfRigidOn-of-relative-count` — relative full count ⇒ `IsInfinitesimallyRigidOn V(G)`
  (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`; singleton-block Case-I bridge + N1 dim-match).
- [x] N7a `lem:realization-of-independent-rows` — the device-to-motive glue
  (`hasFullRankRealization_of_independent_panelRow`; `N2 ∘ N3`, witnessed independent `panelRow`
  family of size `D(|V(G)|−1)` ⇒ `HasFullRankRealization`). Shared by both producers. **GREEN 2026-06-04.**

**RED — the build (ordered; detail in Hand-off):**
- [ ] N7b `lem:case-II-realization-placement` — construct the seed `(q₀, s)` for the 1-extension
  across the edge substitution (KT 6.12). The genuine geometry; feeds N7a. **Decomposed
  2026-06-04** into three buildable sub-nodes (blueprint, mirrors the Case-I placement split):
  - [x] N7b-1 `lem:case-II-placement-new-rows` — **GREEN 2026-06-04**. A transversal hinge `e=uv`
    incident to `v` gives `D−1` independent rigidity rows, each in *that edge's* panel-row span
    (`exists_independent_panelRow_of_edge`; the per-edge span identity `span_panelRow_edge_eq` +
    `linearIndependent_hingeRow` + `finrank_hingeRowBlock`). The panel-row form of
    `exists_independent_rigidityRows_of_edge`; transversality `he` is the satisfiable
    general-position output (`supportExtensor_ne_zero_of_isGeneralPosition`), not laundered.
    **Honest index-subfamily form GREEN 2026-06-04** (`exists_independent_panelRow_subfamily_of_edge`,
    same blueprint node) — the honesty-gate bridge the N7b assembly *actually* consumes: a transversal
    hinge gives an *index subset* `s ⊆ {e}×pc×pc` of size `D−1` whose **actual**
    `panelRow ends`-subfamily is independent (not just members-of-span). The per-edge family spans a
    `(D−1)`-dim space (`span_panelRow_edge_eq` + `finrank_hingeRowBlock` through the injective dual
    map), so `Submodule.exists_fun_fin_finrank_span_eq` extracts an independent subfamily of *actual*
    panel rows; `Equiv.ofInjective` re-indexes by `⋀^k`-pair into the honest index subset. This is
    the literal `panelRow`-subfamily form `exists_good_realization_ofParam`'s `hindep` wants.
  - [x] N7b-2 `lem:case-II-placement-old-rows` — **GREEN 2026-06-04**.
    `PanelHingeFramework.exists_independent_panelRow_transport`: transport an independent `panelRow`
    family across the `ofNormals` graph swap along an *injective* reindex `f` (the `e₀`-free
    subfamily) with a per-row match `hrow` (the rows match because `panelRow`/`supportExtensor`
    read only `ends`+`q`, not the graph — `rfl` when the assembly's `q₀`/`ends` agree on `G−v`).
    `LinearIndependent.comp` + a `funext` family rewrite. Both `G_v^{ab}` and `G` sit above `G−v`
    (`removeVertex_le`/`removeVertex_le_splitOff`); `e₀`'s constraint is recovered in N7b-1.
  - [x] N7b-3 `lem:case-II-placement-block-independent` — **GREEN 2026-06-04**.
    `BodyHingeFramework.linearIndependent_sum_pinned_block`: the abstract pin-a-body column
    split — given a new block `rn` pinned at body `v` (independent *as functionals of `v`'s
    screw* `rn i ∘ₗ single v`, `hnewpin`) and an old block `ro` reading `0` at the `v`-column
    (`hold`, edges `e₀`-free) with `ro` independent (`holdindep`), the union `Sum.elim rn ro`
    is independent. `Fintype.linearIndependent_iff` + evaluate at `Function.update 0 v x`: old
    terms vanish, forcing new coeffs by `hnewpin`; residual forces old coeffs by `holdindep`.
    Mirrors `linearIndependent_hingeRow_star`; count-agnostic (the `D(|V(G)|−1)` total is N7b's
    job, satisfiable from N7b-1's `D−1` + N7b-2's `D(|V(G)|−2)`).
- [ ] N7b `lem:case-II-realization-placement` — assemble the seed `(q₀, s)` from N7b-1/2/3.
  **Honesty-gate bridge now RESOLVED** (N7b-1 honest index-subfamily form green): the new-block
  half is an actual `panelRow ends`-index subset. **Remaining assembly:** put the old block
  (N7b-2's transport) into the same honest *index-subset* shape on `G`, form the seed `q₀`
  (inductive normals on `G−v` + `v`'s general-position normal), and join the two index subsets
  as one independent `panelRow`-subfamily of size `D(|V(G)|−1)` via N7b-3 (re-express the new
  block as `rn` = functionals-of-`v`'s-screw, the old block as `ro` reading 0 at the `v`-column).
- [ ] N7 `lem:case-II-realization` — compose N7a (glue) + N7b (placement). Discharges `hsplit`.
- [ ] N4 `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction bridge; gates Case I.
- [ ] N5 `lem:case-I-splice-placement` — the splice geometry (decompose first).
- [ ] N6 `lem:case-I-realization` — compose N4+N5+glue(N7a)+B0+N3/device. Discharges `hcontract`.
- [ ] `thm:theorem-55` / `prop:rigidity-matrix-prop11` / `lem:case-III` — carry to Phases 22–23.

**RETIRED (item 1, deleted; retirement note in `AlgebraicInduction.lean`):** the four
absolute-motive Case-I producers (`hasFullRankRealization_ofParam_of_*`,
`…_of_pinnedMotionsOn`) and the orphaned vacuous block-internal chain. The genuine
block-pin bricks (`isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`, etc.)
are **retained** (blueprint `lem:pinned-motions-on-rank-bound`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N7b (Case-II placement) decomposes into three sub-nodes before any build.** Per the
  hand-off's "decompose before building" gate (process lesson (a)), the genuinely-geometric
  N7b is split into N7b-1 (the re-inserted `v`'s two hinges give `D−1` independent panel rows
  via `exists_independent_panelSupportExtensor`), N7b-2 (the IH's `D(|V(G)|−2)` rows transport
  through the common subgraph `G−v` — NOT a free inclusion-transport, since `splitOff` is an
  edge substitution), and N7b-3 (the two blocks jointly independent, pin-a-body Lemma 5.1
  column split). N7b assembles the seed `(q₀, s)`; the count is `(D−1) + D(|V(G)|−2) =
  D(|V(G)|−1)`. Mirrors the Case-I placement split.
- **The Case-I splice splits into a green `glue` + a red `placement`.** The
  original `lem:case-I-splice-seed` promised to *produce* a placement, so flipping
  it green while the Lean merely *assumes* the two legs' rigidity would launder
  the deliverable. Resolution: the green `isInfinitesimallyRigidOn_of_splice` is
  the honest **glue** (two legs realized on a common `F` ⇒ rigid on `V(G)`,
  hypotheses = satisfiable IH facts); the **placement** (one `F` realizing both
  legs generically) is the red `lem:case-I-splice-placement` (N5). → blueprint
  honesty gate / producer scrutiny.
- **The device's `hcoord` is a `≤`-containment, not equality.** At degenerate
  panel normals some `C(p(e)) = 0`, so `panelRow` *under*-spans `rigidityRows` and
  equality fails — but the device's generic output point is unknown, so it must
  work at degenerate `q`. It needs only `Z ⊆ (span (range g))ᵒ` (the `⊆`-half of
  `span_panelRow`, holds at every `q`); equality consumers pass `le_of_eq`.
- **B0 coordinatizes against the concrete `Pi.basis (screwBasis k)`, not
  `Module.finBasis`.** `B.dualBasis.equivFun (g i) ⟨a,t⟩ = (g i)(Pi.single a (sb t))`
  is a computable degree-2 panel poly; `Module.finBasis` is opaque. Price: a
  reindex via `exists_good_realization_reindex` (`LinearEquiv.funCongrLeft`).
- **The Case-I splice seed is genericity-free.** Block-triangular row independence
  (KT 6.3 + pin-a-body Lemma 5.1 column split) from the two IH legs; the device
  only lifts the seed to a generic point afterward.
- **B0 coordinate bilinearity is mathlib-supported.** `exteriorPower.basis_repr_apply`
  + `ιMultiDual_apply_ιMulti` + `Matrix.det_fin_two`; the device parameter is the
  panel **normals**, entries degree-2.
- **Coordinatize `R(G,p)` as a functional family.** Rows are `hingeRow u v r`;
  `Z = (span rigidityRows).dualCoannihilator`. → TACTICS-QUIRKS §30/§32/§33.

### Promoted
- *Build the keystone first (forward-mode + linear reduction chain → single-use
  wrapper sprawl).* → `DESIGN.md` *Forward-mode reduction chains*.
- *A producer node may not carry a load-bearing hypothesis no node discharges, and
  it must be **satisfiable**, not merely type-correct.* → `blueprint/CLAUDE.md`
  *the honesty gate* + *producer scrutiny*.
- *An absolute (ambient-type) rigidity/rank motive is unsatisfiable for
  non-spanning subgraphs; carry it relative to `V(G)`.* → `DESIGN.md` *Realization
  motive must be V(G)-relative*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive.* →
  TACTICS-QUIRKS § 33.
- *`map_sum` won't push `Basis.repr` through a `∑` — route via `Finsupp.lapply t
  ∘ₗ repr.toLinearMap`.* → TACTICS-QUIRKS § 34.

## Blockers / open questions

- **N1–N3 (the `V(G)`-relative count bridge) is GREEN** (landed 2026-06-04) —
  adapted the device's absolute count to `IsInfinitesimallyRigidOn V(G)` via mathlib
  `LinearMap.iInfKerProjEquiv` + the green block-pin bricks. **N7 (Case II producer)
  is the next build** (cheapest full producer; needs only N3 + device).
- **N4 (graph↔matroid contraction-minimality bridge) gates Case I.**
  `(rigidContract).IsMinimalKDof` is not built (Phase-20 carry-forward 1,
  `Induction.lean:2956–2961`); the matroid side is green. Build-shaped but
  nontrivial (the matroid-of-a-mapped-graph identification is the content).
- **N5 (Case-I splice placement) is the one genuinely hard node** — research-shaped
  geometry (KT 6.2/6.6, the witness-transfer); decompose before building.
- **`thm:theorem-55`, `prop:rigidity-matrix-prop11`, Case III carry to Phases
  22–23** — not 21b close-conditions. (`prop11`'s `hub`, the Phase-19 partition
  count `D + def ≤ dim Z`, is an untracked hypothesis; independent.)

## Hand-off / next phase

**For the `coordinate-phase` orchestrator (cold-start ready).** The nodes below
are an ordered list; do them top to bottom, re-reading this section after each
commit (the building subagent updates it). Each commit lands Lean + flips its
blueprint node's `\leanok` (or adds green infra) + updates this file. **Mind the
shape tags — this is NOT uniformly build work:** `N4` (contraction bridge) is
build-shaped-but-nontrivial, and `N5` (splice placement) is genuinely hard
geometry that **warrants its own decomposition pass** (dispatch a planning/recon
subagent to break it into sub-nodes) before a build commit. **Do not** re-introduce
the retired vacuous lemmas. Scope: the remaining work is *known-construction*
formalization (KT 2011), not open math; `apnelson1/Matroid` offers no reusable
leverage (no `Pi`-finrank / generic-realization machinery).

**The device-to-motive glue N7a `lem:realization-of-independent-rows` is GREEN
(landed 2026-06-04).** `hasFullRankRealization_of_independent_panelRow` = the honest
`N2 ∘ N3` closure: a witnessed independent `panelRow` family of size `D(|V(G)|−1)` at
*one* seed normal `q₀` ⇒ `HasFullRankRealization k G`. Both producers reduce to it. It
carries no laundered deliverable — the witnessed-rank `(q₀, s)` is the placement's
*satisfiable* geometric output, not the rank concluded (honesty split, like Case-I
glue/placement).

**Correction to the prior "N7 needs only N3 + device" hand-off.** That understated
N7: the splitting-off `G_v^{ab}` is an *edge substitution* of `G` (adds fresh `e₀`,
deletes `v`'s two edges), **not a subgraph**, so the inductive rigidity-on-`t` does
*not* free-transport to the parent `G` and the seed family must be *constructed* across
the substitution (recover `e₀`'s constraint from `v`'s two new edges). That seed
construction is the genuine geometry — split out as the red node below.

**N7b `lem:case-II-realization-placement` is now DECOMPOSED (2026-06-04, this commit).**
The genuine geometry — construct, from the inductive realization of `G_v^{ab}` (rigid on
`V(G)∖{v}`), a seed normal assignment `q₀` for `G` (in particular a panel normal `n` for the
re-inserted `v`) and a linearly independent family `s` of `D(|V(G)|−1)` `panelRow`s of
`ofNormals G ends q₀` — splits into three buildable sub-nodes in the blueprint, mirroring the
Case-I placement split. KT §6.3 Lemma 6.8 / eq. (6.12). This commit is a planning/decomposition
commit (blueprint + notes only, no Lean), per the hand-off's "decompose before building" gate.

**N7b-1 `lem:case-II-placement-new-rows` is GREEN (landed 2026-06-04, this commit).**
`BodyHingeFramework.exists_independent_panelRow_of_edge`: a transversal hinge `e=uv` (distinct
endpoints, `supportExtensor e ≠ 0`) gives `D−1 = screwDim k − 1` linearly independent rigidity rows,
each in *that edge's* panel-row span `span {panelRow ends (e, ·, ·)}`. The panel-row form of
`exists_independent_rigidityRows_of_edge` (`finrank_hingeRowBlock` basis + `linearIndependent_hingeRow`
lift), with membership routed through the new per-edge span identity `span_panelRow_edge_eq` (the
annihilator-family span `span_annihRow_eq_dualAnnihilator` carried through `(screwDiff u v).dualMap`).
The transversality `he` is the *satisfiable* general-position output of the assembly's normal choice
(`supportExtensor_ne_zero_of_isGeneralPosition`), taken as a hypothesis here exactly as the per-edge
brick does — not a laundered deliverable.

**N7b-2 `lem:case-II-placement-old-rows` is GREEN (landed 2026-06-04, this commit).**
`PanelHingeFramework.exists_independent_panelRow_transport`: transport the IH's `D(|V(G)|−2)`
independent `panelRow` rows of `ofNormals G_v^{ab} ends₁ q₁` to independent rows of
`ofNormals G ends₂ q₂` along an *injective* reindex `f : s₂ → s₁` (the `e₀`-free subfamily,
= rows of `G−v`) with a per-row match hypothesis `hrow`. NOT a free inclusion-transport: `splitOff`
is an edge substitution (`e₀` deleted in `G`, `v`'s two edges added), neither graph a subgraph of
the other — both sit above `G−v` (`removeVertex_le`/`removeVertex_le_splitOff`, green). The match
`hrow` is `rfl` whenever the assembly's `q₀`/`ends` agree on `G−v` (`panelRow`/`supportExtensor`
read only `ends`+`q`, not the graph). Proof: `LinearIndependent.comp f hf` + a `funext` family
rewrite. The `e₀`-row's constraint is recovered from `v`'s two new edges in N7b-1.

**N7b-3 `lem:case-II-placement-block-independent` is GREEN (landed 2026-06-04, this commit).**
`BodyHingeFramework.linearIndependent_sum_pinned_block`: the **abstract pin-a-body column split** —
given a new block `rn` carried by body `v`'s incident hinges, independent *as functionals of `v`'s
screw* (`hnewpin : LinearIndependent ℝ (fun i => rn i ∘ₗ LinearMap.single ℝ _ v)`), and an old block
`ro` reading `0` at the `v`-column (`hold : ∀ j x, ro j (Function.update 0 v x) = 0`, edges
`e₀`-free) with `ro` independent (`holdindep`), the union `Sum.elim rn ro` is independent. Proof:
`Fintype.linearIndependent_iff`, evaluate a vanishing combination at `Function.update 0 v x` — old
terms vanish (`hold`), forcing new coeffs by `hnewpin`; residual forces old coeffs by `holdindep`.
Mirrors `linearIndependent_hingeRow_star` (same pin-a-body skeleton). Placed in `RigidityMatrix.lean`
alongside the `_star`/`_forest` siblings; needs `[DecidableEq α]` in the binder (the statement uses
`LinearMap.single`). **Count-agnostic** — the `D(|V(G)|−1)` total is N7b's job and is satisfiable
from N7b-1's `D−1` (`hnewpin`-discharging, `hingeRow u v` at `single v` is `−c i`, independent iff
`c` is) + N7b-2's `D(|V(G)|−2)` (`hold`-discharging, `G−v` edges avoid `v`). Honest: the
column-split hypotheses are discharged-by-construction at the assembly, not the conclusion smuggled.

**Honesty-gate bridge LANDED (2026-06-04): `exists_independent_panelRow_subfamily_of_edge`.** The
hand-off's flagged "Watch": N7b-1 produced rows that are *members of* the per-edge `panelRow`-span,
while the glue N7a's `hindep` wants an actual `LinearIndependent ℝ (fun i : s => panelRow ends i)`
indexed by a `Set` of panel-row indices. **This is now resolved for the new block:** the honest
index-subfamily form (same blueprint node `lem:case-II-placement-new-rows`) gives a transversal
hinge an *index subset* `s ⊆ {e}×pc×pc` of size `D−1` whose actual `panelRow ends`-subfamily is
independent — via `Submodule.exists_fun_fin_finrank_span_eq` on the `(D−1)`-dim per-edge span +
`Equiv.ofInjective` re-indexing. No functional-vs-`panelRow` laundering remains on the new block.

**Next concrete commit: N7b `lem:case-II-realization-placement`** — assemble the seed `(q₀, s)`,
now that the honesty gate is resolved for the new block:
1. Put the **old block** (N7b-2's transport) into the same honest *index-subset* shape on `G` — an
   `s_old ⊆ (E(G−v))×pc×pc` of actual `panelRow ends`-rows of `ofNormals G ends q₀`, size
   `D(|V(G)|−2)` (the inductive realization is rigid on `V(G)∖{v}`, so it carries that many
   independent panel rows; transport them to `G` along the common subgraph `G−v` via N7b-2 — the
   per-row match is `rfl` once `q₀`/`ends` agree on `G−v`).
2. Form the **seed** `q₀`: inductive normals on `G−v`'s bodies + `v`'s general-position normal
   (N7b-1's transversality, satisfiable via `supportExtensor_ne_zero_of_isGeneralPosition`).
3. **Join** `s_new ∪ s_old` (disjoint: new uses edge `e`, old uses `G−v` edges) as one
   independent `panelRow`-subfamily of size `D(|V(G)|−1)` via N7b-3 — re-express the new block as
   `rn` (functionals of `v`'s screw) and the old block as `ro` (reading 0 at the `v`-column,
   since `G−v` edges avoid `v`); `linearIndependent_sum_pinned_block` makes the union independent.
   Then feed the joined index subset + size to N7a, and N7 (one-line N7a∘N7b discharging
   `theorem_55`'s `hsplit`). **Remaining watch:** the new∪old union is a `Set`-union of two index
   subsets, but N7b-3 is stated for a `Sum.elim rn ro`; reconcile the `Sum`-indexed independence
   with the `Set`-union `panelRow`-subfamily (a `Sum (↥s_new) (↥s_old) ≃ ↥(s_new ∪ s_old)` reindex
   under disjointness) before flipping N7b green.

**The `V(G)`-relative count bridge N1–N3 is GREEN (landed 2026-06-04).** The device
(`exists_good_realization_ofParam`, green) gives the *absolute* codimension bound
`#s + dim Z(G,p) ≤ D·card α`; the bridge converts it to `IsInfinitesimallyRigidOn V(G)`:
- **N1 `finrank_pinnedMotionsOn_vertexSet`** — `finrank (pinnedMotionsOn V(G)) = D·|V(G)ᶜ|`,
  the free isolated bodies (via `pinnedMotionsOn_vertexSet_eq_iInf_ker_proj` +
  mathlib `LinearMap.iInfKerProjEquiv` + `finrank_pi_const`). The one piece with content.
- **N2 `exists_relative_full_count_ofParam`** — re-wraps `exists_good_realization_ofParam`:
  given `#s ≥ D(|V(G)|−1)` (`hcard`) and `V(G).Nonempty` (`hne`), a generic `q` attains
  `dim Z ≤ D·(|V(G)ᶜ|+1)`. Mechanical (`Set.ncard_add_ncard_compl` + omega).
- **N3 `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`** — from `dim Z ≤ D(|V(G)ᶜ|+1)` and
  `V(G).Nonempty` conclude `IsInfinitesimallyRigidOn V(G)`, via `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`
  at a singleton block `{v₀}` + N1 dimension-match (`finrank_pinnedMotions_add_screwDim`).

Then, in order:
1. **N7b `lem:case-II-realization-placement`**, decomposed into N7b-1 (GREEN) → N7b-2 (GREEN) →
   N7b-3 (GREEN) → N7b-assembly (the sub-nodes are all green; **N7b assembly is the next concrete
   commit** — see the honesty-gate watch above on the functionals-in-span → `panelRow` subfamily
   bridge) → **N7 `lem:case-II-realization`** (one-line N7a∘N7b). Discharges `hsplit`.
2. **N4 `lem:rigidContract-isMinimalKDof`** — the graph↔matroid contraction bridge
   (independent of N1–N3): `(G.rigidContract H r).IsMinimalKDof n 0` from the green
   matroid-side `contraction_isMinimalKDof` (`Induction.lean:1998`) + a
   `matroidMG`-of-`(map ∘ deleteEdges)` correspondence (the content). Phase-20
   carry-forward 1 (`Induction.lean:2956–2961`); gates the Case-I IH application.
3. **N5 `lem:case-I-splice-placement`** — the genuinely hard node. **Decompose
   first** (KT eqs. 6.2/6.6: the boundary-panel intersection + combined
   block-triangular independence). Exhibit one parent `F` realizing both legs at a
   generic point; the glue `isInfinitesimallyRigidOn_of_splice` (green) + the device
   lift then conclude. The device's `hindep` comes from
   `exists_independent_panelSupportExtensor` via the hinge-row block (`panelRow`'s `s`).
4. **N6 `lem:case-I-realization`** — compose N4 + N5 + glue (N7a) + B0 + N3/device ⇒
   `HasFullRankRealization k G`. Discharges `theorem_55`'s `hcontract`.

**Phase 21b closes when N6 + N7 are green.** `thm:theorem-55` does not flip here
(its recursion needs Case III, deferred to Phases 22–23, where it flips); same for
`prop:rigidity-matrix-prop11` (+ brick `hub`, the Phase-19 partition count).

**Completed items:** Item 1 (motive relativized, base green) + Item 2 (accounting
re-stated rank-side) — 2026-06-05; Item 3 (B0 keystone) + Item 4 (Case-I splice
glue) — 2026-06-06; **N1–N3 (`V(G)`-relative count bridge) — 2026-06-04**;
**N7a `lem:realization-of-independent-rows` (device-to-motive glue, shared by both
producers) — 2026-06-04** (and N7 decomposed into glue + red placement N7b);
**N7b placement decomposed into the three buildable sub-nodes N7b-1/2/3 — 2026-06-04**
(planning commit, blueprint + notes); **N7b-1 `lem:case-II-placement-new-rows`
(`exists_independent_panelRow_of_edge` + the per-edge span identity `span_panelRow_edge_eq`)
— 2026-06-04**; **N7b-2 `lem:case-II-placement-old-rows`
(`exists_independent_panelRow_transport`, the `ofNormals` graph-swap row transport) — 2026-06-04**;
**N7b-3 `lem:case-II-placement-block-independent` (`linearIndependent_sum_pinned_block`, the abstract
pin-a-body column split joining the new+old blocks) — 2026-06-04**;
**N7b-1 honest index-subfamily bridge `exists_independent_panelRow_subfamily_of_edge` (same
blueprint node `lem:case-II-placement-new-rows`; the honesty-gate resolution — actual independent
`panelRow ends`-index-subset of size `D−1`, via `Submodule.exists_fun_fin_finrank_span_eq` +
`Equiv.ofInjective`) — 2026-06-04**.
Per-node detail in the blueprint dep-graph.

**Process lessons (don't repeat).**
(a) Build the keystone / validate the target shape *before* growing a reduction
chain (→ `DESIGN.md` *Forward-mode reduction chains*).
(b) A producer hypothesis must be **satisfiable**, not just type-correct — check
it against a concrete small instance (→ `blueprint/CLAUDE.md` *honesty gate /
producer scrutiny*).
(c) For a vertex-reducing induction the realization motive must be carried relative
to `V(G)`, not absolute over the ambient type (→ `DESIGN.md` *Realization motive
must be V(G)-relative*).
(d) When checking whether existing work covers a need, **cross-check the actual
statement, not the name.** The rigid-subgraph contraction was called "missing" by
a spike and "done" by a recon — both wrong; the truth (matroid side green,
graph-level `(rigidContract).IsMinimalKDof` = N4 not built) only surfaced by
reading the statement (matroid- vs graph-side) and the deferral comment at
`Induction.lean:2956–2961`.
(e) **A "cheapest full producer" claim is itself a hand-off hypothesis to verify
against the graph operation, not inherit.** N7 was tagged "needs only N3 + device";
the actual obstruction is that `splitOff` is an *edge substitution* (`G_v^{ab}` adds
`e₀`, deletes `v`'s edges), so neither it nor `G` is a subgraph of the other — the
seed-row witness must be *constructed* across the substitution (the green
`withGraph` monotonicity only travels between a graph and its subgraphs, via the
common lower bound `G − v`). Both case producers therefore split the same way:
green device-to-motive glue (`lem:realization-of-independent-rows`, N7a) + red
placement (the seed construction). Validate the *transport* direction against the
graph op before sizing a producer.

**Session note.** Commits since an inadvertent earlier push are local. Match
author `bryangingechen@gmail.com`; do **not** push without asking.
