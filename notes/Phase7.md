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

Eleven commits in. The first six lifted Laman-only machinery to
`IsSparse` and landed `IsSparse.exists_typeI_or_typeII_reverse` in
flat form (entry points `60a2176..6d59be2`); the next five landed the
four operation-form row-LI lifts plus the row-LI openness lemma in
`MatroidIdentification.lean` (entry points `91403e7..57f8f1f`). The
chapter dep-graph in `chapter/rigidity-matroid.tex` has only the
`|E|`-induction theorem `thm:isSparse-exists-rowIndependent-placement`,
the iff `thm:edgeSet-rowIndependent-iff-isSparse`, and the `Matroid`
packaging left to discharge.

**Multi-session plan** for the forward-blueprint work:

- **Commits 2–6** [✓ done]: sparse-side lifting + flat-form sparse
  reverse + Laman reverse cleanup. Entry points
  `60a2176..6d59be2`.
- **Commits 7–11** [✓ done]: Type I / Type II row-LI conditional
  cores + unconditional wrappers + row-LI openness lemma. Entry
  points `91403e7..57f8f1f`.
- **Next: refine sparse reverse decomp + pendant lift** —
  strengthen `IsSparse.exists_typeI_or_typeII_reverse` to a 3-way
  split (pendant / Type I / Type II, with `deg v ≥ 1` enforced
  inside the proof by restricting to the induced subgraph on
  positive-degree vertices); add a new pendant lift
  `typeI_pendant_edgeSetRowIndependent_lift` (or similar) in
  `MatroidIdentification.lean`. Update the Laman shell
  `IsLaman.exists_typeI_or_typeII_reverse` in `Henneberg.lean` to
  consume the strengthened form. Blueprint statement of
  `thm:isSparse-exists-typeI-or-typeII-reverse` already updated
  (this commit) and `\leanok` removed until Lean catches up;
  pendant lift entry `lem:pendant-rowIndependent-lift` added
  alongside the typeI lift. See *3-way reverse decomposition*
  decision below for the rationale.
- **Then: `IsSparse.exists_rowIndependent_placement`** — the
  `|E|`-induction theorem. With the 3-way split landed, the
  induction matches the blueprint sketch directly: each branch
  strictly decreases `|E|`; the pendant case uses the new lift, the
  Type I and Type II cases use the existing lifts via the existing
  iso constructors. Lives in `MatroidIdentification.lean`.
- **Then the iff** `edgeSet_rowIndependent_iff_isSparse_dim_two`
  (combine the hard direction with Phase 6's easy direction
  `isSparse_of_edgeSetRowIndependent_dim_two`).
- **Then the `Matroid` packaging** via `IndepMatroid` (~100 LoC
  expected; see Blockers).

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Statement form: reverse = flat, forward = operation form.**
  See `../DESIGN.md` *Statement-form conventions* and the blueprint
  aside at `chapter/rigidity-matroid.tex` §3.1 (just before
  *Lifting row-independence through Henneberg moves*). Phase 7's
  `IsSparse.exists_typeI_or_typeII_reverse` lands flat; the row-LI
  lifts land in operation form; the inductive proof bridges the two
  via `typeI_iso_of_two_neighbors` per step.

- **Forward-mode blueprint authoring** (Option C). The blueprint
  chapter `chapter/rigidity-matroid.tex` is the authoritative
  dep-graph; `\lean{...}` and `\leanok` get added as each Lean
  lemma lands. No parallel lemma checklist here.

- **New file `MatroidIdentification.lean`.** Phase 7's Lean content
  lives in its own file. `RigidityMatroid.lean` stays as the row-LI
  predicate / easy-direction file. If the Henneberg lifts grow beyond
  ~600 LoC mid-phase, split into `MatroidHenneberg.lean` +
  `MatroidIdentification.lean` (the Phase 5 / Phase 6 split pattern).

- **Package as `Matroid`, defer the count-matroid construction.**
  Phase 7 builds `SimpleGraph.rigidityMatroid V d : Matroid (Sym2 V)`
  via `IndepMatroid`. The Lov–Yem identification is stated as
  "rigidity-matroid independent sets in dim 2 = $(2, 3)$-sparse
  subsets of $E(K_V)$", **not** as `Matroid` equality, because the
  general $(k, \ell)$-count matroid is not in mathlib.

- **"Some generic placement" formulation.** The hard direction's
  conclusion is $\exists p, \mathrm{EdgeSetRowIndependent}\,p\,I$.
  No "generic placement" notion (Zariski-open, measure-zero); the
  existential suffices.

- **Proof route: Jordán §2.2 induction on $|E|$.** Each step picks a
  min-degree-$\le 3$ vertex in the sparse graph and reverses the
  corresponding Henneberg move (Lemma 2.1.4(a) for degree $\le 2$ —
  Type I reverse; Lemma 2.1.4(b) for degree $3$ — Type II reverse).
  Inductive case: lift the row-LI placement via the Type I / Type II
  row-LI lifts. Reverse-decomposition step reuses Phase 5's
  tight-subset machinery (`IsTightOn.union_inter` — Jordán Lemma
  2.1.2). (Jordán's "critical set" ↔ our `IsTightOn`; documented in
  the chapter's *Terminology* aside.)

## Lemma checklist

**Maintained in the blueprint, not here.** The authoritative checklist
is `chapter/rigidity-matroid.tex`, visible as a dep-graph at
`blueprint/web/dep_graph_document.html` after `inv bp && inv web`.
A red node = not yet formalized; a green node = formalized and
`\leanok`-tagged. Pick leaf-most red.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Generalize, do not duplicate.** Where Phase 5's Laman-only lemmas
  actually use sparsity (not tightness), lift the hypothesis from
  `IsLaman` to `IsSparse` and delete the Laman wrapper. Three passes:
  (1) `exists_degree_le_three` and `exists_nonadj_among_three_neighbors`
  moved to `Sparsity.lean`; (2) the five blocker-contradiction
  primitives moved likewise; (3) `typeII_reverse_blocker` factored into
  a sparse inner lemma + thin Laman shell (the iso+edge-count
  conversion `¬ G'.IsLaman → ¬ G'.IsSparse 2 3` is the one step that
  genuinely needs the tight global edge count). `image_edgesIn_comap`
  was promoted from private in `Henneberg.lean` to public in
  `Sparsity.lean` at the same time.

- **Flat-form sparse reverse: subtype `{w // w ≠ v}` instead of `Sym2 V`
  predicate.** The flat conclusion of
  `IsSparse.exists_typeI_or_typeII_reverse` could in principle describe
  `G - v` and `G^{u,w}_v` via `SimpleGraph V`-predicates, but instead
  uses `G.comap (Subtype.val : {w // w ≠ v} → V)`. Reason: consumer
  ergonomics — the downstream row-LI lifts work on
  `G' : SimpleGraph {w // w ≠ v}`, and Phase 5's existing iso
  constructors already produce isos at that subtype.

- **Laman reverse cleanup (Commit 6).**
  `IsLaman.exists_typeI_or_typeII_reverse` becomes a flat-form shell
  over `IsSparse.exists_typeI_or_typeII_reverse`: `IsLaman.two_le_degree`
  bumps `deg v ≤ 2` to `= 2`; `typeI_isLaman_iff` and
  `typeII_edgeSet_ncard` + bridge presence bump `G'.IsSparse 2 3` to
  `G'.IsLaman`. Net ~280 LoC deleted in `Henneberg.lean`
  (`exists_typeI_or_typeII_iso`, `typeII_reverse_blocker`,
  `typeII_reverse_witness_or_blocker`, branch helpers);
  `typeI_iso_of_two_neighbors` / `typeII_iso_of_three_neighbors` go
  public so the `LamanTheorem.lean` callsite reconstructs the iso
  before the operation-form forward preservation.

- **Type I row-LI conditional core (Commit 7).**
  `typeI_edgeSetRowIndependent_extend` mirrors Phase 5's
  `typeI_isInfinitesimallyRigid_extend` on the row-LI / dual side.
  Partitions `(typeI G' a b).edgeSet` via `LinearIndepOn.union` into
  `Sym2.map some '' G'.edgeSet` (old) + the two new edges (new). Old
  LI: factor through `restrictMap.dualMap` (injective since
  `restrictMap = LinearMap.funLeft ℝ _ some` is surjective). New LI
  + disjoint spans: extract coefficients via test motions
  `x_α = (none ↦ α, some _ ↦ 0)` plus `LinearIndependent.pair_iff`
  on `hLI`.

- **Type I row-LI unconditional wrapper (Commit 8).**
  `typeI_edgeSetRowIndependent_lift` composes
  `exists_off_line_off_finite_dim_two` (with `S = ∅` — the matroid
  hard direction needs no injectivity) and the conditional core. The
  helper was un-privatized in `HennebergRigidity.lean` for cross-file
  reuse.

- **Type II row-LI conditional core (Commit 9).**
  `typeII_edgeSetRowIndependent_extend` mirrors Phase 5's
  `typeII_isInfinitesimallyRigid_extend` with an additional
  `G'.Adj a b` hypothesis. Partition via `LinearIndepOn.union`. New-row
  LI: three-step `LinearIndepOn.insert` peeling, routed through a
  `typeII_new_rows_coeff_zero` helper that rescales `q - p' b`
  evaluations back to `q - p' a` via `hcoll`. Disjointness: same
  `x_α` argument plus the row identity
  `(s-1) row newA - s row newB = s(s-1) T(G'.rigidityRow p' eAB)`
  closes via G'-LI + dualMap-injectivity.

- **Row-LI openness (Commit 10).**
  `EdgeSetRowIndependent.eventually` is the row-LI analogue of
  `IsInfinitesimallyRigid.eventually`. Obstacle:
  `Module.Dual ℝ (Framework V d)` carries no canonical norm.
  Resolution: transport along `b.dualBasis.equivFun` to `Fin n → ℝ`;
  continuity comes from `@[fun_prop]`-tagged
  `continuous_rigidityMap_apply`; transport back via
  `LinearMap.linearIndependent_iff` + `LinearEquiv.ker`.

- **3-way reverse decomposition (planned for Commit 12).** The
  original sparse reverse decomp returned `deg v ≤ 2` (Type I) or
  `= 3` (Type II); the `deg ≤ 2` branch silently lumped together
  pendant (`deg = 1`), Type I proper (`deg = 2`), and the
  degenerate `deg = 0` case. K₁,₅ (sparse with only deg-1 leaves
  and one deg-5 centre) shows that the reverse will pick a pendant
  vertex, so the `|E|`-induction consumer cannot avoid the deg-1
  case. Strengthening the reverse to a 3-way split (pendant /
  Type I / Type II, with `deg v ≥ 1` enforced internally by
  restricting to the induced subgraph on positive-degree vertices)
  puts the complexity in the structure theorem instead of every
  consumer, exposes neighbour data uniformly across all three
  branches, and matches the blueprint's `|E|`-induction proof
  sketch verbatim. A new pendant lift
  `lem:pendant-rowIndependent-lift` lands alongside.

- **Type II row-LI unconditional wrapper (Commit 11).**
  `typeII_edgeSetRowIndependent_lift` mirrors Phase 5's
  `typeII_isGenericallyRigidInj_two` minus injectivity. A private
  helper `exists_nonCollinear_rowIndependent_placement_dim_two`
  perturbs `p' c` perpendicular to `(p' a, p' b)` if collinear (using
  row-LI openness); the wrapper picks `s = 1/2` and
  `q := p'' a + s • (p'' b - p'' a)`. `p' a ≠ p' b` from row-LI alone
  (zero row at `s(a, b)` would contradict LI). Blueprint statement of
  `lem:typeII-rowIndependent-lift` relaxed to drop the `p|_V = p'`
  constraint (the perturbation genuinely changes `p'|_c`).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Mirror `LinearIndependent.dualMap_of_surjective`* → FRICTION
  [mirrored] *`Function.Injective.eventually_of_continuousAt`* and
  related (the post-Phase-5 mirror landed in commit `757e4d5`).
- *Sym2-eq case split in `typeII_isInfinitesimallyRigid_extend`* →
  FRICTION [resolved] *"Sym2-symmetry case split … understated by
  blueprint"* + TACTICS-GOLF § 5 *Lifting Subtype-Sym2 equalities*,
  subsection "the other direction".
- *Test-motion gadget named in blueprint; Lean tightened* → FRICTION
  [resolved] *"Test motion `x_α` gadget in Phase 7 understated by
  blueprint prose"*.
- *`elemSkewMap_ofLp_inr_apply` proof collapse via wider simp + grind*
  → FRICTION [resolved] + TACTICS-GOLF § 1 *Tricks*.
- *Phase 5 + Phase 7 golf: replace 5-step `γ • _ = _` rewrite chain
  with `eq_inv_smul_iff₀`* → already covered by TACTICS-GOLF § 7's
  search decision tree (no new section needed).

### Cleanup pass summaries

- `Henneberg.lean`: ~280 LoC net deletion across `exists_typeI_or_typeII_iso`,
  `typeII_reverse_blocker`, `typeII_reverse_witness_or_blocker`, and
  branch helpers; `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors` un-privatized.
- `Sparsity.lean`: gained `exists_degree_le_three`,
  `exists_nonadj_among_three_neighbors`, the five
  `IsSparse.contradiction_*_pair` blocker primitives,
  `IsSparse.typeII_reverse_blocker`, and `image_edgesIn_comap` (all
  lifted from `Henneberg.lean`); plus the flat-form
  `IsSparse.exists_typeI_or_typeII_reverse`.
- `HennebergRigidity.lean`: `exists_off_line_off_finite_dim_two` and
  `exists_not_mem_span_singleton_dim_two` un-privatized for cross-file
  reuse from `MatroidIdentification.lean`.
- `RigidityMatroid.lean`: `EdgeSetRowIndependent.eventually` (Commit 10).
- `MatroidIdentification.lean`: new file (Commit 7); cumulatively
  holds the four operation-form row-LI lifts (typeI / typeII × extend
  / lift) and `exists_nonCollinear_rowIndependent_placement_dim_two`.
- `TrivialMotions.lean`: `elemSkewMap_ofLp_inr_apply` collapsed to
  one line (Commit 10's cleanup pass).

## Blockers / open questions

- **Matroid `IndepMatroid` axioms in dim 2.** Once the iff
  *row-LI at some $p$* ↔ *$(2, 3)$-sparse* is in hand, the
  augmentation axiom factors through the (purely combinatorial)
  matroid structure on $(2, 3)$-sparse sets. The four matroid axioms
  need to be discharged for the rigidity-matroid `IndepMatroid`
  builder; expect ~100 LoC. Open: how cleanly does
  `IndepMatroid.ofExistsMatroid` or a similar mathlib pattern apply.

- **Unify the Phase 5 IR + Phase 7 row-LI typeII conditional cores.**
  `typeII_isInfinitesimallyRigid_extend` and
  `typeII_edgeSetRowIndependent_extend` share the same algebraic
  backbone — the row identity
  `(s-1) · rigidityRow newA − s · rigidityRow newB =
   s(s-1) · restrictMap.dualMap (G'.rigidityRow ⟨s(a,b), h_ab⟩)`
  — used in **kernel** form (IR) and **dual / span** form (row-LI).
  The same duality applies to the Type I cores (simpler, no deleted
  row). Three factoring options:
  1. *Cheap.* Extract the row identity as shared lemmas in
     `Henneberg.lean`. Both `extend` proofs shrink by ~15 LoC each.
  2. *Medium.* Extract a "Henneberg row-decomposition" lemma stating
     the full block factorisation. Likely subsumed by option 3.
  3. *Principled.* Prove
     `rank R_typeII p_ext = rank R_{G'} p' + 2` once, derive IR and
     row-LI as corollaries. Requires more rank-of-`RigidityMap` API
     than we currently have. Best done after the `Matroid` packaging
     pins down what other rank lemmas the project ends up wanting.

  Recommendation: do option 1 once option 3 is ruled out or
  postponed; option 2 is a half-step that would get redone under
  option 3.

## Hand-off / next phase

_Written when the phase finishes._
