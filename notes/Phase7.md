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

The first commit (this one) lifts two Phase 5 Laman lemmas to
`IsSparse` versions in `Sparsity.lean` —
`IsSparse.exists_degree_le_three` and
`IsSparse.exists_nonadj_among_three_neighbors`. The Laman wrappers
(`IsLaman.exists_degree_le_three`,
`IsLaman.exists_nonadj_among_three_neighbors`) are deleted; the
former's one caller (`IsLaman.exists_two_le_degree_le_three`) and the
latter's two callers (in `Henneberg.lean`) now invoke
`h.isSparse.foo` directly. Blueprint follows: the two entries move
from `chapter/laman.tex` to `chapter/sparsity.tex` under a new
*Low-degree vertex and non-adjacency consequences* subsection.

Next: lift Phase 5's private `IsLaman.*` blocker machinery in
`Henneberg.lean` (`no_isTightOn_excluding_three_neighbors`,
`typeII_reverse_witness_or_blocker`, the three contradiction
templates, `False_of_pairwise_blocker_or_edge`) to `IsSparse`. Then
land `IsSparse.exists_typeI_or_typeII_reverse` (Jordán Lemma 2.1.4)
and re-derive `IsLaman.exists_typeI_or_typeII_reverse` from it.
Downstream: Type I and Type II row-LI lifts, the inductive existence
theorem, and the `IndepMatroid` packaging.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

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
  wrapper; rewrite callers to use `h.isSparse.foo` directly. First
  pass: `exists_degree_le_three` and
  `exists_nonadj_among_three_neighbors` moved to `Sparsity.lean`.
  Next pass will do the same for the private Henneberg blocker
  machinery. Rationale: a one-line forwarder `IsLaman.foo (h : ...) := h.isSparse.foo` is
  just duplication at the API level; eliminating it keeps the
  Laman/sparse split honest about which lemmas genuinely need
  tightness.

## Blockers / open questions

- **Sparse-graph reverse decomposition** (`IsSparse.exists_typeI_or_typeII_reverse`,
  Jordán Lemma 2.1.4). The sparse-graph analogue of Phase 5
  milestone 1 (`IsLaman.exists_typeI_or_typeII_reverse`). Should reuse
  the same tight-subset machinery (`IsTightOn.union_inter`, Phase 5's
  three-pair tight-union argument) but without the Laman-specific
  blocker complications, since we only need sparsity-preservation
  not tightness-preservation. Open: how much of Phase 5's milestone-1
  Lean code generalizes by dropping `IsLaman` hypotheses to `IsSparse`,
  versus needing a fresh implementation.

- **Type II row-LI lift collinearity gap.** The Type II move places
  the new vertex on the line through `u, w`; for row-LI we also need
  `p(u), p(w), p(z)` not collinear (or the third new row collapses
  into the span of the first two). Phase 5's `IsInfinitesimallyRigid.
  eventually` + perpendicular-perturbation approach (`exists_nonCollinear_rigid_placement_dim_two`)
  is the obvious template, adapted to row-LI rather than IR. Open:
  whether row-LI is itself open (it is, via `LinearIndependent.eventually`
  or similar), which makes the perturbation argument the same shape.

- **Matroid `IndepMatroid` axioms in dim 2.** Once the iff
  *row-LI at some $p$* ↔ *$(2, 3)$-sparse* is in hand, the
  augmentation axiom factors through the (purely combinatorial)
  matroid structure on $(2, 3)$-sparse sets. The four matroid
  axioms need to be discharged for the rigidity-matroid `IndepMatroid`
  builder; expect ~100 LoC. Open: how cleanly does
  `IndepMatroid.ofExistsMatroid` or a similar mathlib pattern apply.

## Hand-off / next phase

_Written when the phase finishes._
