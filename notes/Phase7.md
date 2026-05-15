# Phase 7 — Lovász–Yemini matroid identification (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §7 for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 7 runs in **forward blueprint mode** (Option C,
hybrid skeleton) per `../blueprint/DESIGN.md` *Recommendation for
Phase 6* (the rule generalizes to subsequent phases). The blueprint
chapter `chapter/rigidity-matroid.tex` is the authoritative dep-graph
and lemma index throughout; this file does **not** duplicate it.

## Current state

Phase 6 closed Laman's theorem in both directions; the project
carries no `sorry`s. Phase 7 builds on top of Phase 6's row-LI
infrastructure (`RigidityMatroid.lean`) to ship the converse of the
Lovász–Yemini "easy direction" already in place, completing the
rigidity-matroid ↔ $(2, 3)$-count matroid identification in dim 2
and packaging the rigidity matroid as a
`Mathlib.Combinatorics.Matroid` instance.

Eight commits in so far. The **first three** lifted Phase 5 Laman
machinery to `IsSparse` (degree-≤-3 existence, non-adjacent triple,
the five blocker contradiction primitives, the per-pair typeII
tight-blocker). The **fourth** was a docs-only commit pinning the
statement-form convention (forward preservation = operation form;
reverse decomposition = flat form) and prepping the blueprint for
the upcoming sparse-reverse landing. The **fifth** landed
`IsSparse.exists_typeI_or_typeII_reverse` in `Sparsity.lean` in
flat form. The **sixth** refactored
`IsLaman.exists_typeI_or_typeII_reverse` to a flat-form shell over
the sparse version, deleting the operation-form intermediates and
promoting `typeI_iso_of_two_neighbors` /
`typeII_iso_of_three_neighbors` to public. The **seventh** opened
Phase 7 forward: created `CombinatorialRigidity/MatroidIdentification.lean`
with the **conditional Type I row-LI lift**
`typeI_edgeSetRowIndependent_extend` (operation-form, row-LI
analogue of Phase 5's `typeI_isInfinitesimallyRigid_extend`), wired
the new file into the top-level entry, and flipped `\leanok` on the
blueprint entry `lem:typeI-rowIndependent-extend`. The **eighth**
(this commit) lands the **unconditional Type I row-LI wrapper**
`typeI_edgeSetRowIndependent_lift`: takes `p' a ≠ p' b` instead of
the LI hypothesis, picks `q` off the line through `p' a, p' b` via
the un-privatized `exists_off_line_off_finite_dim_two`
(`S = ∅`, since the matroid hard direction needs no injectivity
constraint), then composes with the conditional core. Flips
`\leanok` on `lem:typeI-rowIndependent-lift`.

**Multi-session plan** for the forward-blueprint work:

- **Session 2 — Commit 2 ("flat-form sparse reverse")** [✓ done]:
  landed `IsSparse.exists_typeI_or_typeII_reverse`.
- **Session 2 — Commit 3 ("Laman reverse cleanup")** [✓ done]:
  refactored `IsLaman.exists_typeI_or_typeII_reverse` to flat form.
- **Session 3 — Commit 4 ("Type I row-LI conditional core")** [✓
  done]: landed `typeI_edgeSetRowIndependent_extend` in
  `MatroidIdentification.lean`. Mirrors Phase 5's conditional core
  convention; the unconditional wrapper is next.
- **Session 3 — Commit 5 ("Type I row-LI unconditional wrapper")**
  [✓ done in this commit]: landed `typeI_edgeSetRowIndependent_lift`
  in `MatroidIdentification.lean`; un-privatized
  `exists_off_line_off_finite_dim_two` in `HennebergRigidity.lean`
  so the wrapper can reuse it with `S = ∅`.
- **Session 3+:** Type II row-LI conditional core + unconditional
  wrapper (the latter needs the row-LI analogue of openness, i.e.
  `EdgeSetRowIndependent.eventually` or similar, plus the
  perpendicular-perturbation pattern from
  `exists_nonCollinear_rigid_placement_dim_two`); then
  `IsSparse.exists_rowIndependent_placement` (the |E|-induction);
  then the iff and the `Matroid` packaging.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Statement form: reverse = flat, forward = operation form.**
  See `../DESIGN.md` *Statement-form conventions* and the blueprint
  aside at `chapter/rigidity-matroid.tex` §3.1 (just before
  *Lifting row-independence through Henneberg moves*). Phase 7's
  `IsSparse.exists_typeI_or_typeII_reverse` lands flat; the row-LI
  lifts land in operation form (about `Henneberg.typeI G' a b`); the
  inductive proof bridges the two via `typeI_iso_of_two_neighbors`
  per step. Phase 5's existing `IsLaman.exists_typeI_or_typeII_reverse`
  gets converted from operation form (its current state) to flat
  form in Commit 3 of this phase's multi-session plan.

- **Forward-mode blueprint authoring** (Option C). The blueprint
  chapter `chapter/rigidity-matroid.tex` is the authoritative
  dep-graph; `\lean{...}` and `\leanok` get added as each Lean
  lemma lands. We do **not** maintain a parallel lemma checklist
  here. Rationale: `../blueprint/DESIGN.md` *Recommendation for
  Phase 6* (proved out by Phase 6).

- **New file `MatroidIdentification.lean`.** Phase 7's Lean content
  lives in its own file imported by nothing yet (Phase 7 is a
  terminal chapter). `RigidityMatroid.lean` stays as the row-LI
  predicate / easy-direction file; growing it past ~1000 LoC mixes
  conceptually distinct content. If the Henneberg lifts grow beyond
  ~600 LoC mid-phase, split into `MatroidHenneberg.lean` +
  `MatroidIdentification.lean` (the Phase 5 / Phase 6 split pattern).

- **Package as `Matroid`, defer the count-matroid construction.**
  Phase 7 builds `SimpleGraph.rigidityMatroid V d : Matroid (Sym2 V)`
  via `IndepMatroid`. The Lov–Yem identification is stated as
  "rigidity-matroid independent sets in dim 2 = $(2, 3)$-sparse
  subsets of $E(K_V)$", **not** as `Matroid` equality, because the
  general $(k, \ell)$-count matroid is not in mathlib and packaging
  it is parallel work (a worthy upstream contribution but not
  Phase 7's deliverable).

- **"Some generic placement" formulation.** The hard direction's
  conclusion is $\exists p, \mathrm{EdgeSetRowIndependent}\,p\,I$.
  Avoid introducing a "generic placement" notion (Zariski-open
  subset, measure-zero exclusion); the existential suffices for the
  matroid axioms and for the iff. This mirrors Phase 6's choice to
  stay matroid-agnostic until needed.

- **Proof route: Jordán §2.2 induction on $|E|$.** Follow Jordán's
  modern presentation of Lovász–Yemini (Theorem 2.2.1): induct on
  the edge count, with each step picking a min-degree-$\le 3$ vertex
  in the sparse graph and reversing the corresponding Henneberg
  move (Lemma 2.1.4(a) for degree $\le 2$ — Type I reverse; Lemma
  2.1.4(b) for degree $3$ — Type II reverse). Inductive case: lift
  the row-LI placement of the smaller sparse graph back along the
  Henneberg move via the Type I / Type II row-LI lifts. This avoids
  a separate sparse-to-Laman extension lemma and reuses Phase 5's
  tight-subset machinery (`IsTightOn.union_inter` — Jordán Lemma
  2.1.2) for the reverse-decomposition step. (Jordán's "critical set"
  ↔ our `IsTightOn` synonym, plus the Lemma 2.1.2 / 2.1.3 ↔ our
  tight-subset-lattice correspondence, are documented in the new
  chapter's *Terminology* aside.)

## Lemma checklist

**Maintained in the blueprint, not here.** The authoritative checklist
is `chapter/rigidity-matroid.tex`, visible as a dep-graph at
`blueprint/web/dep_graph_document.html` after `inv bp && inv web`.
A red node = not yet formalized; a green node = formalized and
`\leanok`-tagged. Pick leaf-most red.

## Decisions made during this phase

- **Generalize, do not duplicate.** Where Phase 5's Laman-only lemmas
  actually use sparsity (not tightness) in their proof, lift the
  hypothesis from `IsLaman` to `IsSparse` and delete the Laman
  wrapper; rewrite callers to use `h.isSparse.foo` directly. Three
  passes so far: (1) `exists_degree_le_three` and
  `exists_nonadj_among_three_neighbors` moved to `Sparsity.lean`;
  (2) the five blocker-contradiction primitives
  (`no_isTightOn_excluding_three_neighbors`, the three
  `contradiction_*_pair` templates, `False_of_pairwise_blocker_or_edge`)
  likewise moved; (3) `typeII_reverse_blocker` factored into a sparse
  inner lemma in `Sparsity.lean` plus a thin Laman shell in
  `Henneberg.lean` that does only the iso+edge-count conversion
  `¬ G'.IsLaman → ¬ G'.IsSparse 2 3` (the one step that genuinely needs
  the tight global edge count). The supporting `image_edgesIn_comap`
  was promoted from private in `Henneberg.lean` to public in
  `Sparsity.lean` at the same time. The remaining Laman-only piece
  (`typeII_reverse_witness_or_blocker`) is now a thin dispatcher over
  the factored blocker; sparse-graph reverse decomposition can reuse
  `IsSparse.typeII_reverse_blocker` directly without going through
  Laman.

- **Flat-form sparse reverse: subtype `{w // w ≠ v}` instead of
  `Sym2 V` predicate.** The flat conclusion of
  `IsSparse.exists_typeI_or_typeII_reverse` could in principle describe
  `G - v` and `G^{u,w}_v` via predicates on `V` (e.g. `G' ≤ G` with
  `G'.Adj` agreeing on edges not incident to `v`). Instead it uses
  `G.comap (Subtype.val : {w // w ≠ v} → V)` (and the same plus a
  bridging `fromEdgeSet`) — explicitly describing the smaller graph on
  the smaller vertex type. The reason is consumer ergonomics: the
  downstream row-LI lifts will work on `G' : SimpleGraph {w // w ≠ v}`,
  and Phase 5's existing iso constructors
  (`typeI_iso_of_two_neighbors`, `typeII_iso_of_three_neighbors`)
  already produce isos at that subtype. A `SimpleGraph V`-side
  description would require a separate iso layer at every consumer.

- **Laman reverse cleanup (Commit 6).**
  `IsLaman.exists_typeI_or_typeII_reverse` becomes a flat-form shell
  over `IsSparse.exists_typeI_or_typeII_reverse`:
  `IsLaman.two_le_degree` bumps `deg v ≤ 2` to `= 2`;
  `typeI_isLaman_iff` and `typeII_edgeSet_ncard` + bridge presence
  bump `G'.IsSparse 2 3` to `G'.IsLaman`. Statement mirrors the sparse
  shape and additionally exposes the two Type I neighbors. Net ~280
  LoC deleted in `Henneberg.lean` (`exists_typeI_or_typeII_iso`,
  `typeII_reverse_blocker`, `typeII_reverse_witness_or_blocker`, plus
  private branch helpers); `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors` go public so the
  `LamanTheorem.lean` callsite reconstructs the iso before the
  operation-form forward preservation.

- **Type I row-LI conditional core (Commit 7).**
  `MatroidIdentification.lean` opens with
  `typeI_edgeSetRowIndependent_extend`. Mirrors Phase 5's
  `typeI_isInfinitesimallyRigid_extend` structure: same hypothesis
  on `q` (linear independence of `(q - p' a, q - p' b)`), but on the
  row-LI / dual side instead of the kernel side. Proof partitions
  `(typeI G' a b).edgeSet` via `LinearIndepOn.union` into
  `Sym2.map some '' G'.edgeSet` (old) + `{s(none, some a), s(none, some b)}`
  (new). Old LI: factor through
  `restrictMap.dualMap : Dual ℝ (Framework V 2) →ₗ Dual ℝ (Framework (Option V) 2)`,
  injective since `restrictMap = LinearMap.funLeft ℝ _ some` is
  surjective (some is injective). New LI: extract coefficients via
  test motions `x_α = (none ↦ α, some _ ↦ 0)`, then use
  `LinearIndependent.pair_iff` on `hLI`. Disjoint spans: any joint
  element vanishes when evaluated on `x_α` (old span: trivially;
  new span: forces both coefficients to zero by the same argument).
  Conditional core has no `\leanok` on the existential blueprint
  entry yet; the wrapper lands next commit and flips both.

- **Type I row-LI unconditional wrapper (Commit 8).**
  `typeI_edgeSetRowIndependent_lift` composes
  `exists_off_line_off_finite_dim_two` with the conditional core,
  passing `S = ∅` since the matroid hard direction needs no
  injectivity. The helper was promoted from private to public in
  `HennebergRigidity.lean` in the same commit (its docstring now
  cross-references both Phase 5's `S = Set.range p` use and Phase 7's
  `S = ∅` use). The `p ∘ some = p'` constraint discharges by
  `funext fun _ => rfl`. Flips `\leanok` on
  `lem:typeI-rowIndependent-lift`.

## Blockers / open questions

- **Type II row-LI lift collinearity gap.** The Type II move places
  the new vertex on the line through `u, w`; for row-LI we also need
  `p(u), p(w), p(z)` not collinear (or the third new row collapses
  into the span of the first two). Phase 5's `IsInfinitesimallyRigid.
  eventually` + perpendicular-perturbation approach (`exists_nonCollinear_rigid_placement_dim_two`)
  is the obvious template, adapted to row-LI rather than IR. Open:
  whether row-LI is itself open (it is, via `LinearIndependent.eventually`
  or similar), which makes the perturbation argument the same shape.
  The injectivity-preservation piece of the template is now mirrored
  as `Function.Injective.eventually_update_of_continuousAt` in
  `Mathlib/Topology/Separation/Hausdorff.lean` — see the mirrored
  FRICTION entry — so the row-LI wrapper can reuse it instead of
  rebuilding the `∀ᶠ`-injectivity argument inline.

- **Matroid `IndepMatroid` axioms in dim 2.** Once the iff
  *row-LI at some $p$* ↔ *$(2, 3)$-sparse* is in hand, the
  augmentation axiom factors through the (purely combinatorial)
  matroid structure on $(2, 3)$-sparse sets. The four matroid
  axioms need to be discharged for the rigidity-matroid `IndepMatroid`
  builder; expect ~100 LoC. Open: how cleanly does
  `IndepMatroid.ofExistsMatroid` or a similar mathlib pattern apply.

## Hand-off / next phase

_Written when the phase finishes._
