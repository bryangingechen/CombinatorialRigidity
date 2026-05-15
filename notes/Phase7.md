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

Four commits in so far. The **first three** lifted Phase 5 Laman
machinery to `IsSparse` (degree-≤-3 existence, non-adjacent triple,
the five blocker contradiction primitives, the per-pair typeII
tight-blocker). The **fourth** (this one) is a docs-only commit:
documents the **statement-form convention** (forward preservation =
operation form; reverse decomposition = flat form) and updates the
blueprint for the upcoming `IsSparse.exists_typeI_or_typeII_reverse`
landing. No Lean changes this commit. (Several blueprint nodes
temporarily lose `\leanok` until the next-session Lean refactor
catches up — `thm:isLaman-exists-typeI-or-typeII-reverse` will be
green again after Commit 2 of the multi-session plan below.)

**Multi-session plan** for the forward-blueprint work:

- **Session 2 — Commit 2 ("flat-form sparse reverse"):**
  Land `IsSparse.exists_typeI_or_typeII_reverse` in `Sparsity.lean`
  in flat form per the blueprint statement at
  `chapter/rigidity-matroid.tex` §3.1. Re-flip `\leanok` on its
  blueprint entry.
- **Session 2 — Commit 3 ("Laman reverse cleanup"):**
  Refactor `IsLaman.exists_typeI_or_typeII_reverse` in
  `Henneberg.lean` to flat form, calling the new sparse version and
  bumping `G'.IsSparse` → `G'.IsLaman` via the global edge count.
  Delete the now-unused `IsLaman.exists_typeI_or_typeII_iso`,
  `IsLaman.typeII_reverse_blocker`, and
  `IsLaman.typeII_reverse_witness_or_blocker` (~140 LoC removal).
  Update the callsite in `LamanTheorem.lean` to reconstruct the iso
  via `typeI_iso_of_two_neighbors` / `typeII_iso_of_three_neighbors`
  before invoking the operation-form forward preservation. Re-flip
  `\leanok` on `thm:isLaman-exists-typeI-or-typeII-reverse`.
- **Session 3+ — Phase 7 forward:** Row-LI lifts in **operation
  form** (about `Henneberg.typeI G' a b`, etc.), matching Phase 5's
  forward preservation convention. Then
  `IsSparse.exists_rowIndependent_placement` (bridges flat reverse →
  operation forward at each inductive step) and matroid identification.

Downstream after the multi-session plan completes: Type I and Type II
row-LI lifts, the inductive existence theorem, and the `IndepMatroid`
packaging.

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

## Blockers / open questions

- **Sparse-graph reverse decomposition + Laman cleanup** — the
  multi-session plan in *Current state* (Commits 2 and 3) covers
  this. All blocker contradiction primitives plus
  `typeII_reverse_blocker` already live in `Sparsity.lean` as
  `IsSparse.*`, so the Phase 5 framework is fully reusable.
  Remaining Lean work: the outer existence theorem
  `IsSparse.exists_typeI_or_typeII_reverse` (Commit 2) and the
  flat-form Laman re-derivation (Commit 3).

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
