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

Eighteen commits in (this commit = Commit 17a; the prior commit
`a8f3e42` was the research-only docs revision of the augmentation
proof route). The
first six lifted Laman-only machinery to `IsSparse` and landed
`IsSparse.exists_typeI_or_typeII_reverse` in flat form (entry points
`60a2176..6d59be2`); the next five landed the four operation-form
row-LI lifts plus the row-LI openness lemma in
`MatroidIdentification.lean` (entry points `91403e7..57f8f1f`); Commit
12 refined the sparse reverse to a 3-way split (pendant / Type I /
Type II) and reflowed the Laman shell to consume it; Commit 13 added
the pendant row-LI lift (`typeI_pendant_edgeSetRowIndependent_lift`);
Commit 14 landed the hard-direction `|E|`-induction theorem
`IsSparse.exists_rowIndependent_placement` (`MatroidIdentification.lean`),
the supporting iso transport `EdgeSetRowIndependent.iso`
(`RigidityMatroid.lean`), and the private perturbation helper
`exists_distinct_rowIndependent_placement_dim_two`; Commit 15
generalised `exists_affinelySpanning_rigid_placement` to the
property-polymorphic `exists_affinelySpanning_of_eventually`
(retiring the IR-specific wrapper), then landed the iff
`edgeSet_rowIndependent_iff_isSparse_dim_two` in
`MatroidIdentification.lean`. The blueprint nodes
`thm:isSparse-exists-rowIndependent-placement`,
`lem:edgeSet-rowIndependent-iso`, the renamed
`lem:exists-affinelySpanning-of-eventually`, and
`thm:edgeSet-rowIndependent-iff-isSparse` are all `\leanok`.

**Scope expanded in Commit 16.** Following user direction, Phase 7
now closes on the **general $(k, \ell)$-count matroid** in the
matroidal regime $\ell < 2k$ (Whiteley 1996, Lee--Streinu 2008) rather than packaging the planar rigidity matroid as
a one-off. Concretely: build `SimpleGraph.countMatroid V k ℓ : Matroid
(Sym2 V)` once, with the combinatorial $(k, \ell)$-augmentation as
its only non-trivial axiom; then specialize
`SimpleGraph.rigidityMatroid V := countMatroid V 2 3 ...` and bridge
to row-LI via the existing iff. The linear-matroid framing of
Lovász--Yemini (`Matroid.ofFun` at a generic placement; matroid-iso
identification) is **deferred to Phase 8** — that phase will add
`apnelson1/Matroid` as a dependency and ship the iso
`linearRigidityMatroid V 2 = rigidityMatroid V`. The blueprint chapter
splits to match (new `chapter/count-matroid.tex` for the abstract
construction; `chapter/rigidity-matroid.tex` retains the row-LI
machinery and the specialization).

**Commit 17 proof route resolved (this commit).** Research-only:
the original `union_with_bonus` sketch doesn't close (bonus edges
must be I-edges; J\\I edges aren't). Replaced with the Lee--Streinu
component-based proof; split into Commits 17a (block intersection
closure + minimum I-block), 17b (I-components + edge partition),
17c (augmentation assembly). See *Blockers / open questions* for
the full proof outline and *Multi-session plan* for the 17a/b/c
decomposition. No Lean changes this commit. The blueprint
`lem:isSparse-aug` proof sketch in `count-matroid.tex` is updated
to match.

**Multi-session plan** for the forward-blueprint work:

- **Commits 2–6** [✓ done]: sparse-side lifting + flat-form sparse
  reverse + Laman reverse cleanup. Entry points
  `60a2176..6d59be2`.
- **Commits 7–11** [✓ done]: Type I / Type II row-LI conditional
  cores + unconditional wrappers + row-LI openness lemma. Entry
  points `91403e7..57f8f1f`.
- **Commit 12** [✓ done]: refine sparse reverse to 3-way split
  (pendant / Type I / Type II); reflow the Laman shell to discard
  the pendant branch via `IsLaman.two_le_degree`. The
  positive-degree restriction is via a new
  `IsSparse.exists_one_le_degree_le_three` helper in `Sparsity.lean`
  (handshake + sparsity on `S := {v | 1 ≤ deg v}`; assume for
  contradiction every `v ∈ S` has `deg v ≥ 4`, then
  `4 |S| ≤ 2 |E| ≤ 4 |S| − 6`).
- **Commit 13** [✓ done]: pendant row-LI lift
  (`typeI_pendant_edgeSetRowIndependent_lift` +
  `_extend` in `MatroidIdentification.lean`). The pendant case
  lifts row-LI through `typeI G' a a` (the new vertex joins to a
  single old vertex); `q` only needs `q ≠ p' a` (via mathlib's
  `exists_ne`), vastly simpler than the `q - p' a, q - p' b` LI
  condition of the general typeI lift. The blueprint
  `lem:pendant-rowIndependent-lift` is pinned.
- **Commit 14** [✓ done]: `|E|`-induction theorem
  `IsSparse.exists_rowIndependent_placement` in
  `MatroidIdentification.lean`. Strong induction on `Fintype.card V`
  (each Henneberg reverse strictly decreases `card V`, and the base
  case covers `H.edgeSet = ∅` uniformly — including `card V ≤ 1`).
  Each branch: apply IH to the smaller subtype graph, invoke the
  branch's row-LI lift, reconstruct the iso to
  `typeI / typeII H' ...` via `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors`, and transport row-LI back via
  the new iso-transport lemma `EdgeSetRowIndependent.iso`
  (`RigidityMatroid.lean`). The Type I branch needs `p' a ≠ p' b`
  for `typeI_edgeSetRowIndependent_lift`, supplied by the new
  private helper `exists_distinct_rowIndependent_placement_dim_two`
  (perturbs `p' a` along `t • v` with `v ≠ 0` and small `t ≠ 0`,
  preserving row-LI via `EdgeSetRowIndependent.eventually`). The
  blueprint `thm:isSparse-exists-rowIndependent-placement` and
  `lem:edgeSet-rowIndependent-iso` are pinned `\leanok`.
- **Commit 15** [✓ done]: refactor + iff. Generalise
  `exists_affinelySpanning_rigid_placement` to the property-polymorphic
  `exists_affinelySpanning_of_eventually` (takes `∀ᶠ p in 𝓝 p₀, P p`
  for arbitrary `P`); inline the IR existential at the single Phase 6
  caller in `LamanTheorem.lean`; specialise at row-LI's openness
  (`EdgeSetRowIndependent.eventually`) in the iff's `(⇒)` direction.
  Land `edgeSet_rowIndependent_iff_isSparse_dim_two` in
  `MatroidIdentification.lean` combining the hard direction with
  Phase 6's easy direction `isSparse_of_edgeSetRowIndependent_dim_two`.
  Blueprint: rename `lem:exists-affinelySpanning-rigid-placement`
  → `lem:exists-affinelySpanning-of-eventually` (restated
  property-polymorphically with prose aside about the factoring);
  pin `thm:edgeSet-rowIndependent-iff-isSparse` `\leanok`.
- **Commit 16** [this commit]: scope expansion to the general
  $(k, \ell)$-count matroid (docs + blueprint scaffold only; no Lean
  yet). Notes / ROADMAP §7 / new blueprint chapter
  `count-matroid.tex` + restructured `rigidity-matroid.tex`;
  Whiteley 1996 and Lee--Streinu 2008 bibliography entries.
- **Commits 17a / 17b / 17c**: combinatorial augmentation
  lemma `IsSparse.exists_aug_of_lt_two_mul` (final name TBD) in
  `Sparsity.lean`. *Updated Commit 17 plan*: the original sketch
  ("iterate `union_inter` / `union_with_bonus`") doesn't close in
  the matroidal regime because `union_with_bonus` requires bonus
  edges `F ⊆ G.edgesIn`, i.e. *I-edges*, whereas the natural bonus
  edges (J \\ I) aren't in `G = fromEdgeSet I`. The replacement
  route follows Lee--Streinu 2008 (Theorem 5(1,2,4)) via I-block /
  I-component structure:
  - **Commit 17a** [✓ done, this commit]: matroidal-regime block
    closure scaffolding in `Sparsity.lean`. Landed
    `IsTightOn.union_inter_of_pair` (`ℓ < 2 * k` corollary of
    `IsTightOn.union_inter`: two I-tight sets sharing a common
    pair `{u, v}` have I-tight intersection and union; the size
    proviso `ℓ ≤ k * #(s ∩ t)` is auto-discharged via
    `#(s ∩ t) ≥ 2`) and
    `IsSparse.exists_isTightOn_of_insert_not_sparse` (violation
    extraction: from `¬ (fromEdgeSet (insert s(u,v) I)).IsSparse k ℓ`
    plus I-sparsity, extract a Finset `S` with `{u, v} ⊆ S` that
    is `(fromEdgeSet I)`-tight). The intermediate
    `edgeSet_fromEdgeSet_insert` glue lemma (`u ≠ v` → adding
    `s(u, v)` to `I` inserts exactly the singleton into
    `fromEdgeSet`'s edgeSet) is private to the section.
    *Deviation from the plan*: dropped the `IsSparse.minBlockOn`
    definition (Finset.inf over the family of I-blocks containing
    `{u, v}`); the *maximum* I-block is what 17b's I-component
    needs, and union closure from `union_inter_of_pair` builds it
    directly without going through a minimum.
  - **Commit 17b** [planned]: I-component theory in
    `Sparsity.lean`. A maximal I-block; lemma that I-components are
    pairwise edge-disjoint (for matroidal regime they overlap in
    `≤ 1` vertex by Lee--Streinu Theorem 5(2)); lemma that each
    non-free I-edge lives in a unique I-component; the partition
    identity `|I| = Σ_C |I ∩ C.sym2| + |I, free|`. The free-edge
    case is non-trivial only for the lower range ℓ ∈ [0, k); for
    the upper range ℓ ∈ [k, 2k) every edge is in a component.
  - **Commit 17c** [planned]: augmentation assembly. For each
    e ∈ J\\I, the contradiction hypothesis "no augmentation"
    forces endpoints of e into some I-component. J-sparsity at
    each I-component C gives `|J ∩ C.sym2| ≤ |I ∩ C.sym2|`.
    Per-component sum: `|J in-component| ≤ |I in-component|`.
    Free J-edges are in `J ∩ I` (since J \\ I edges are all
    in-component), so `|J ∩ I, free| ≤ |I, free|`. Combine:
    `|J| ≤ |I|`, contradicting `|I| < |J|`. Estimated total
    ~340--390 LoC across the three commits.
- **Commit 18** [planned]: new file
  `CombinatorialRigidity/CountMatroid.lean`. Defines
  `SimpleGraph.countMatroid V k ℓ (h : ℓ < 2 * k) : Matroid (Sym2 V)`
  via `IndepMatroid.ofFinite`. `@[simp] countMatroid_E`,
  `@[simp] countMatroid_indep_iff`. Pins
  `def:countMatroid` and
  `thm:countMatroid-indep-iff` `\leanok` in the new
  blueprint chapter.
- **Commit 19** [planned]: in `MatroidIdentification.lean`, define
  `SimpleGraph.rigidityMatroid V := countMatroid V 2 3 (by omega)`
  and the matroid-form Lovász--Yemini
  `rigidityMatroid_indep_iff_edgeSetRowIndependent` bridging through
  `edgeSet_rowIndependent_iff_isSparse_dim_two`. Pins
  `def:rigidityMatroid` and
  `thm:rigidityMatroid-indep-iff-rowIndependent` `\leanok`.
  Closes Phase 7.

Deferred to **Phase 8** (own work log): linear-matroid framework via
`apnelson1/Matroid`; `genericRigidityMatroid V d`; matroid-iso
`genericRigidityMatroid V 2 = rigidityMatroid V`.

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

- **General $(k, \ell)$-count matroid; specialize to $(2, 3)$
  for Lovász--Yemini.** *Updated in Commit 16.* Standard
  matroid-theory result (Whiteley 1996; Lee--Streinu 2008; survey
  presentation Nixon--Ross 2012 §5): for $0 \le \ell < 2k$ and finite
  $V$, the $(k, \ell)$-sparse subsets of $E(K_V)$ are the
  independent sets of a matroid on $\mathrm{Sym}_2 V$. Phase 7
  ships this general construction
  `SimpleGraph.countMatroid V k ℓ` with the combinatorial
  $(k, \ell)$-augmentation as its only non-trivial
  `IndepMatroid` axiom; specializes
  `SimpleGraph.rigidityMatroid V := countMatroid V 2 3 ...` and
  bridges to row-LI via
  `edgeSet_rowIndependent_iff_isSparse_dim_two`.
  *Originally planned* (Commits 1--15) as a one-off rigidity
  matroid construction; expanded in Commit 16 on user direction
  because the matroidal regime is a coherent abstract object
  whose augmentation proof generalises without extra cost, and
  the linear-matroid iso framing (deferred to Phase 8) wants a
  named matroid on the count side to talk about.

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

- **Property-polymorphic affinely-spanning + iff (Commit 15).**
  `exists_affinelySpanning_rigid_placement`'s moment-curve /
  Vandermonde body was IR-specific only at the `obtain ⟨p₀, hp₀⟩`
  and the `hp₀.eventually` pullback. Generalised to
  `exists_affinelySpanning_of_eventually` consuming
  `∀ᶠ p in 𝓝 p₀, P p`; no wrapper kept (row-LI would be a pure
  alias, IR saved one `obtain` at one call site). Iff `(⇒)` calls
  it with `hp.eventually` from `EdgeSetRowIndependent.eventually`;
  iff `(⇐)` is the hard direction on
  `H = fromEdgeSet (Subtype.val '' I)` then `LinearIndependent.comp`
  along an injective reindex `toH : I → H.edgeSet` (row-equality is
  `rfl` after `Sym2` induction; `convert ... using 1` closes via
  defeq through `Sym2.lift`).

- **Hard-direction `|E|`-induction (Commit 14).**
  `IsSparse.exists_rowIndependent_placement` runs strong induction on
  `Fintype.card V`: base case `H.edgeSet = ∅` returns the zero
  placement; inductive step applies the 3-way sparse reverse, picks
  the row-LI lift for the branch (pendant / Type I / Type II), and
  transports back via `EdgeSetRowIndependent.iso` after the iso
  constructor recovers the operation form. The Type I branch routes
  `p'` through `exists_distinct_rowIndependent_placement_dim_two` to
  satisfy `p' a ≠ p' b`. The new iso-transport lemma
  `EdgeSetRowIndependent.iso` factors `G.rigidityRow (q ∘ φ)` as
  `Lφ.toLinearMap.dualMap ∘ H.rigidityRow q ∘ φ.mapEdgeSet`, where
  `Lφ : Framework V d ≃ₗ[ℝ] Framework W d` is precomposition with
  `φ.symm` (the framework-side `LinearEquiv` analogue of `motion ∘
  φ.symm`); LI transports along the bijection + injective dualMap.

- **Pendant row-LI lift (Commit 13).**
  `typeI_pendant_edgeSetRowIndependent_extend` + `..._lift` handle the
  `b = a` degeneracy of the Type I lift (parallel edges collapse to a
  single new edge `s(none, some a)`). Structure mirrors
  `typeI_edgeSetRowIndependent_extend` with the new-edge `Set` shrunk
  from `{newA, newB}` to `{newA}`: LI on the singleton via
  `linearIndepOn_singleton_iff` (row newA ≠ 0 by the
  `none ↦ q - p' a, some _ ↦ 0` test motion evaluating to
  `‖q - p' a‖² > 0`), disjoint spans via the standard `x_α`
  argument with `α = q - p' a`. The unconditional lift wraps with
  `exists_ne (p' a)` over `Nontrivial (EuclideanSpace ℝ (Fin 2))`.
  No `[Finite V]` needed (pendant doesn't go through `eventually`).

- **3-way reverse decomposition (Commit 12).**
  `IsSparse.exists_typeI_or_typeII_reverse` now splits on
  `G.degree v ∈ {1, 2, 3}` (pendant / Type I / Type II) and exposes
  neighbour data uniformly across all three branches. The degree
  positivity (`deg v ≥ 1`) comes from a new helper
  `IsSparse.exists_one_le_degree_le_three` in `Sparsity.lean`: assume
  for contradiction every `v ∈ S := {v | 1 ≤ deg v}` has `deg v ≥ 4`,
  then handshake gives `4 |S| ≤ 2 |E|`, and sparsity at `S`
  (size ≥ 2 from any edge) gives `|E| + 3 ≤ 2 |S|`, contradicting
  `4 |S| ≤ 4 |S| − 6`. The Laman shell discards the pendant branch
  via `IsLaman.two_le_degree`; Type I / Type II consumers are
  unchanged. Pendant row-LI lift lands separately.

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
  `exists_one_le_degree_le_three` (Commit 12),
  `exists_nonadj_among_three_neighbors`, the five
  `IsSparse.contradiction_*_pair` blocker primitives,
  `IsSparse.typeII_reverse_blocker`, and `image_edgesIn_comap` (all
  lifted from `Henneberg.lean`); plus the flat-form
  `IsSparse.exists_typeI_or_typeII_reverse`, refined to a 3-way
  split (pendant / Type I / Type II) in Commit 12. New matroidal-
  regime block-closure scaffolding in Commit 17a:
  `IsTightOn.union_inter_of_pair`, `edgeSet_fromEdgeSet_insert`,
  and `IsSparse.exists_isTightOn_of_insert_not_sparse`.
- `HennebergRigidity.lean`: `exists_off_line_off_finite_dim_two` and
  `exists_not_mem_span_singleton_dim_two` un-privatized for cross-file
  reuse from `MatroidIdentification.lean`.
- `RigidityMatroid.lean`: `EdgeSetRowIndependent.eventually` (Commit 10);
  `EdgeSetRowIndependent.iso` (Commit 14);
  `exists_affinelySpanning_rigid_placement` → property-polymorphic
  `exists_affinelySpanning_of_eventually` (Commit 15).
- `MatroidIdentification.lean`: new file (Commit 7); cumulatively
  holds the four operation-form row-LI lifts (typeI / typeII × extend
  / lift), `exists_nonCollinear_rowIndependent_placement_dim_two`,
  the pendant row-LI lift `typeI_pendant_edgeSetRowIndependent_extend`
  + `..._lift` (Commit 13), `exists_distinct_rowIndependent_placement_dim_two`,
  the hard-direction `|E|`-induction theorem
  `IsSparse.exists_rowIndependent_placement` (Commit 14), and the iff
  `edgeSet_rowIndependent_iff_isSparse_dim_two` (Commit 15).
- `LamanTheorem.lean`: Phase 6 caller inlined the `obtain` of the
  IR witness and now calls
  `exists_affinelySpanning_of_eventually hp₀.eventually` (Commit 15).
- `TrivialMotions.lean`: `elemSkewMap_ofLp_inr_apply` collapsed to
  one line (Commit 10's cleanup pass).

## Blockers / open questions

- **$(k, \ell)$-count matroid augmentation in the matroidal regime
  $\ell < 2k$.** *Updated post Commit 16: proof route resolved to
  Lee--Streinu component-based argument; cost-estimated; split into
  Commits 17a/b/c (see multi-session plan).* The original sketch
  ("iterate `union_inter` / `union_with_bonus` to build a saturating
  $I$-tight $S^*$") doesn't close in the matroidal regime: in the
  $|S \cap S_e| = 1$ case the close-the-gap inequality of
  `union_with_bonus` requires $\lceil (\ell - k|S \cap S_e|)
  / 1 \rceil$ bonus *I-edges* between $S \setminus S_e$ and
  $S_e \setminus S$ — but the natural bonus edges
  ($J \setminus I$ edges with endpoints in $S \cup S_e$) live in
  $J$, not $I$, so they don't contribute to
  `(fromEdgeSet I).edgesIn (S ∪ S_e)` and can't satisfy
  `union_with_bonus`'s `hF_sub`.

  **Replacement route (Lee--Streinu 2008 / Whiteley 1996), via
  I-component theory:** for each $e \in J \setminus I$ failing
  augmentation, endpoints of $e$ lie in some I-block, hence in
  some I-component (= maximal I-block). I-components are pairwise
  edge-disjoint (Lee--Streinu Theorem 5(2)); in the upper range
  $\ell \in [k, 2k)$ they additionally overlap in $\le 1$ vertex
  and have no free edges, in the lower range $\ell \in [0, k)$
  free I-edges are possible but free $J \setminus I$ edges are
  excluded by the contradiction hypothesis. J-sparsity at each
  I-component $C$ gives $|J \cap C^{\otimes 2}| \le k|C| - \ell =
  |I \cap C^{\otimes 2}|$. Summing across the component partition
  of edges and adding the (J-free, I-free) edges of $J \cap I$
  gives $|J| \le |I|$, contradiction. See the *Commits 17a/b/c*
  entries in the multi-session plan for the lemma split; total
  estimate ~340--390 LoC. The block intersection closure
  (Lee--Streinu Theorem 5(1)) is the existing
  `IsTightOn.union_inter` specialized to two blocks sharing a
  $\ge \lceil \ell/k \rceil$-size set of vertices, so no new
  upstream-style lemma is needed there — only project-internal
  block/component scaffolding.

- **Future-friction: a pebble-game algorithm.** Lee--Streinu's
  $(k, \ell)$-pebble game is the algorithmic complement to the
  block/component proof above: an explicit greedy procedure that
  certifies $(k, \ell)$-sparsity by maintaining $k$ pebbles per
  vertex and a directed orientation, accepting edges when
  $\mathrm{peb}(u) + \mathrm{peb}(v) \ge \ell + 1$. Formalizing
  it would yield a decision algorithm and an alternative proof
  route for the augmentation axiom (rejected edges $\leftrightarrow$
  tight components). Phase 7 does **not** depend on it — the
  component-based proof above closes the matroid axiom directly
  via `union_inter`. Logged here as an interesting future
  deliverable; not on the critical path.

- **Matroid `IndepMatroid` packaging.** Uses
  `IndepMatroid.ofFinite` from
  `Mathlib.Combinatorics.Matroid.IndepAxioms`. Trivial axioms:
  `indep_empty` (`fromEdgeSet ∅ = ⊥`, vacuously sparse);
  `indep_subset` (`(fromEdgeSet I).IsSparse k ℓ` is monotone in
  `I`); `subset_ground` (baked into the predicate). The
  augmentation axiom is the lemma above. Expected ~30 LoC for the
  packaging itself plus the simp-lemmas.

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
