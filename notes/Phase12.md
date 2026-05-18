# Phase 12 — Body-bar Tay theorem (planning)

**Status:** planning. Not yet started.

This file is the per-phase work record. See `../ROADMAP.md` §12
(to be added when planning lands) for the high-level summary and
`../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 12 is a **forward-mode** new-theorem phase
(analogous to Phases 6–10, contrasted with the structural-edit
mode of Phase 11). The blueprint chapter
`blueprint/src/chapter/body-bar.tex` (to be opened in Layer 0) will
serve as the authoritative dep-graph and lemma index for the phase;
this file carries everything else — architectural choices, Layer
plan, decisions, blockers, hand-off. Per `notes/CLAUDE.md` the
lemma checklist below is a high-level outline; the leaf-level
to-do list lives in the blueprint dep-graph during the phase.

**Target theorem (Tay 1984, Theorem 5.3 / Whiteley 1988, Theorem 8).**
Let `G = (V, E)` be a finite multigraph with `b = |V|` and let
`d = n(n+1)/2`. Then `G` admits an infinitesimally rigid
independent body-bar framework in `Rⁿ` iff
- `|E| = d(b − 1)`, and
- every `m`-body sub-multigraph has at most `d(m − 1)` edges;

equivalently (Tutte–Nash-Williams 1961), iff `G` is the
edge-disjoint union of `d` spanning trees.

**Proof route.** Whiteley 1988 §2–§3 (matroid-union route). Three
ingredients:
1. **Theorem 1 (Whiteley):** the generic `k`-frame matroid `F(G,X)`
   on a multigraph equals the union of `k` copies of the cycle
   matroid. Pure linear algebra over indeterminates.
2. **Theorem 2 (Pym–Perfect):** matroid union of submodular-defined
   matroids is itself defined by `∑ gⱼ`. Together with (1), this
   yields the count `|E'| ≤ k|V'| − k` characterization of
   `k`-forest decomposability (Tutte–Nash-Williams as a corollary).
3. **Theorem 8 (Whiteley = Tay):** lift (1)+(2) from indeterminate
   to body-bar realizations via a specialization argument. Whiteley
   uses Proposition 6 (irreducible-variety lifting) for the fully
   general statement; **Phase 12 ships only the witness-specialization
   form (L5a below)** — the lift to "almost all body-bar
   realizations" via the irreducible-variety machinery is deferred
   to Phase 13 prep or skipped if K–T's reductions don't need it.

**References.** All in `../.refs/`:
- Tay 1984 (`tay-1984-rigidity-multi-graphs-i.pdf`) — primary,
  the original body-bar theorem (Theorems 4.4 / 5.3); §4 carries
  Tay's own induction-based proof and §6 the Henneberg replacements
  for body-bar.
- Whiteley 1988 (`whiteley-1988-union-of-matroids.pdf`) — the
  matroid-union proof route, the one we follow.
- Whiteley 1996 (`whiteley-1996-matroids-discrete-geometry.pdf`) —
  modern unified presentation of Tay-type matroids.
- Tutte 1961, Nash-Williams 1961, Edmonds 1965 (in `.refs/`) —
  tree-packing primary sources for the corollary.
- Katoh–Tanigawa 2011 (`katoh-tanigawa-2011-molecular-conjecture.pdf`)
  + arXiv preprint — forward-design reference; Phase 12 API should
  be reusable by the eventual molecular-conjecture phases.

## Current state

Planning. Nothing committed yet. References gathered; matroid-package
survey complete; Whiteley 1988 §2–§3 and Tay 1984 §4–§5 read. Next
concrete step: Layer 0 — open `blueprint/src/chapter/body-bar.tex`
with the Whiteley-route dep-graph (red nodes), decide on multigraph
carrier and place a project-organization friction entry if the
decision creates an audit surface for later phases.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Whiteley 1988 proof route over Tay 1984.** Whiteley's
  matroid-union → specialization route directly reuses Phase 7/8
  matroid machinery and sets up infrastructure that
  Katoh–Tanigawa 2011 (Phase 13/14 target) also needs:
  panel-hinge rigidity is characterized by the matroid-union
  count on the modified multigraph `((d+1 choose 2)−1)G`, an
  argument that does not lift cleanly out of Tay's induction-based
  proof. Tay 1984 §4–§5 is heavier in new combinatorial scaffolding
  (relative motion space `M(i,j)`, induced constraints, Theorem 4.3
  circuit-exchange) and treats tree-packing as a corollary citation,
  not a structural ingredient.

- **Matroid-union access via mirror, not upstream-then-consume.**
  `apnelson1/Matroid` ships matroid-union (`Matroid.Union`,
  `union_indep_iff'`) and Edmonds' matroid-partition theorem
  (`matroid_partition'`, `matroid_partition_eRk'`) in
  `WIP/Union.lean` (597 lines, 0 active sorries — the one match is
  a commented-out scrap from an old approach). The file is unbuilt
  in the package only because its `import Matroid.Constructions.Submodular`
  points to a file renamed to `WIP/Submodular.lean` (1236 lines,
  0 sorries). We vendor both files under a new
  `CombinatorialRigidity/Matroid/` mirror directory (analogous to
  the existing `CombinatorialRigidity/Mathlib/` mirror) so Phase 12
  is unblocked; the mirror is marked upstream-eligible to
  `apnelson1/Matroid` and will be retired once those files land
  in the package's built tree.

- **Multigraph carrier — L0 decision, two options listed.**
  `SimpleGraph V` (the Phase 1–11 carrier) cannot natively express
  the multi-edges that Tay's count `d(b−1)` requires
  (`d = n(n+1)/2 ≥ 1`; for `n ≥ 2` we have `d ≥ 3`, so most rigid
  body-bar multigraphs have parallel edges between many pairs).
  Two options, picked in Layer 0:

  - **(M-A) Use the vendored `Graph V β` from `apnelson1/Matroid`.**
    Already underlies `cycleMatroid`. Native multi-edge support.
    Costs: introduces a second graph type to the project; Phase
    1–11 lemmas stay on `SimpleGraph`, Phase 12 onward speaks
    `Graph`. Refactor pressure on later phases that want to
    cross-quote.

  - **(M-B) Thin wrapper `BodyBarGraph V := Sym2 V → ℕ`.**
    Edge-multiplicity function. Keeps the project's
    `SimpleGraph`-centric idiom and stays under `Sym2 V` for
    cardinality bookkeeping. Costs: redo a slice of the
    `cycleMatroid` API on this wrapper (probably via a transport
    along an `Equiv` between `BodyBarGraph V`'s edge bag and a
    suitable `Graph` instance), and accept that the project's
    "graphic matroid" identity is bridged rather than reused.

  Recommendation pending; lean toward (M-A) because Katoh–Tanigawa's
  `((d+1 choose 2)−1)G` parallel-multiplication operation is
  natively expressible there and the mirror sub-directory is
  already a precedent for taking a dependency on the package's
  graph idioms.

- **Plücker / extensor coordinates handled inline, no separate phase.**
  Body-bar bars carry "2-extensor" coordinates in `Rᵈ`, `d = n(n+1)/2`,
  which is the Plücker embedding of `Gr(2, n+1)` cut out by the
  quadratic p-relations. Phase 12 only needs the **standard-basis
  specialization** `b_e = (0,…,0,1,0,…,0)` (Whiteley's witness),
  which sits vacuously on `V(p-relations)` (degenerate Plücker
  coords represent boundary points of the Grassmannian, not actual
  lines). Tay's theorem as we state it asserts existence of an
  independent realization, witnessed by this specialization;
  Whiteley's "almost all body-bar realizations are rigid" via
  Proposition 6 is **deferred** (L5b). This keeps Phase 12 free
  of irreducible-variety / Zariski-open infrastructure.

- **Tree-packing primary, count condition derived.** Phase 12 ships
  Tutte–Nash-Williams as a theorem in its own right (the matroid-
  partition theorem specialized to `d` copies of `cycleMatroid`)
  and uses it as the linchpin equivalence in Tay's theorem,
  matching Whiteley's exposition. The count form
  `|E'| ≤ d|V'| − d` follows from tree-packing via Whiteley's
  Corollary 3 (Theorem 2 → submodular function argument).

## Prerequisites audit (matroid package)

What's available unbuilt vs. ready in `apnelson1/Matroid`. See the
session's earlier survey for file:line citations.

**Ready (built, zero sorries, just import):**
- `Graph.cycleMatroid` and full API (`Matroid/Graphic.lean`,
  669 L). Multi-edge support native. Rank `|V| − c(G)` via
  `eRank_cycleMatroid_add_numberOfComponents`. Bases =
  `IsAcyclicSet` = forests. Duality, contraction, parallel
  edges, signed-incidence representation over any field
  (`cycleMatroidRep`).
- `Matroid.Constructions.Matching` (143 L, 0 sorries) — needed
  transitively by `WIP/Union.lean`.
- `Matroid.ofFun` (the `Matroid/Representation/Map.lean` linear-
  matroid constructor used in Phase 8) — used to package the
  body-bar generic structure matroid as a `Matroid (Sym2 V × ℕ)`
  (or the equivalent edge type of the chosen carrier).
- `Matroid.Intersection` — built; available as a fallback for
  matroid-union via duality if the mirror ever has issues.

**Unbuilt but proved (vendor in Layer 1):**
- `WIP/Submodular.lean` (1236 L, 0 sorries, 6 `Classical.`,
  1 `noncomputable`) — ships `PolymatroidFn`, `ofSubmodular`,
  `polymatroid_rank_eq`. The polymatroid-of-submodular-function
  construction is the bridge underlying matroid-union's rank
  formula.
- `WIP/Union.lean` (597 L, 0 active sorries) — ships
  `Matroid.union M₁ M₂`, `Matroid.Union (Ms : ι → Matroid α)`,
  `union_indep_iff` / `union_indep_iff'`, `polymatroid_of_adjMap`,
  `adjMap_rank_eq`, `matroid_partition` / `matroid_partition'` /
  `matroid_partition_eRk'`, base-construction lemmas, and a
  matroid-intersection alternate proof.

**Trim list for the mirror:** the Submodular file is large; only
the polymatroid framework (`PolymatroidFn`, `ofSubmodular`,
`polymatroid_rank_eq`) and the lemmas Union depends on are
strictly required. Aggressive trim is a Layer 1 task — track the
exact subset there.

## Layer plan

A new chapter `blueprint/src/chapter/body-bar.tex` opens in
Layer 0 and serves as the authoritative dep-graph for the phase.
Per-Layer dep-graph nodes referenced below as `def:foo` /
`lem:foo` / `thm:foo` are the chapter's labels; create them as
each Layer's Lean lands and flip `\leanok` to green when the
matching Lean lemma names.

### Layer 0 — Phase opening; multigraph carrier decided; new chapter

**Lean:** (none yet) — the chapter and `Phase12.md` ship together.

**Blueprint:** open `chapter/body-bar.tex`. Sections:
- *Body-bar frameworks* (definitions; landing in L4).
- *The general k-frame matroid* (Whiteley §2.1; landing in L2).
- *Matroid union via submodular functions* (Whiteley §2.2;
  landing in L1+L2 split).
- *Tree-packing / Tutte–Nash-Williams* (landing in L3).
- *Tay's theorem* (landing in L5a).

Initial dep-graph is fully red; nodes flip green per Layer.

**Decisions to capture in this Layer's commit:**
- (M-A) vs (M-B) multigraph carrier (see *Architectural choices*).
- Mirror directory placement and naming
  (`CombinatorialRigidity/Matroid/Constructions/{Submodular,Union}.lean`).
- Sync user-facing status surfaces per the *When this commit opens
  a phase* discipline in `../CLAUDE.md`: ROADMAP `§Phase 12` planning
  section + Status table row; `README.md`; `home_page/index.md`;
  `blueprint/src/chapter/intro.tex` §Phase plan enumerate +
  dep-graph-status line.

### Layer 1 — Matroid-union mirror

**Lean:** vendor `WIP/Submodular.lean` + `WIP/Union.lean` under
`CombinatorialRigidity/Matroid/Constructions/`. Concretely:
- `CombinatorialRigidity/Matroid/Constructions/Submodular.lean`
- `CombinatorialRigidity/Matroid/Constructions/Union.lean`

Both files namespaced under `Matroid` to match upstream. The
broken `import Matroid.Constructions.Submodular` in Union becomes
`import CombinatorialRigidity.Matroid.Constructions.Submodular`.
Trim Submodular to the polymatroid-of-submodular-function
sub-API actually used by Union + downstream Phase 12 layers; the
rest stays in the mirror but unexported (or trimmed wholesale,
to be assessed).

**Friction entries:** open a *Mirrored* entry in `FRICTION.md`
tagged `[matroid]` (analogous to the existing `[mathlib]` mirror
entries) listing the two files + the upstream issue link (to file
against `apnelson1/Matroid`).

**Blueprint:** flip `\leanok` on the matroid-union definition + the
union-indep-iff / matroid-partition statements (re-stated in the
chapter as facts cited from the mirror, not re-proven in prose).

### Layer 2 — `k`-frame matroid = `k`-fold union of cycle matroids (Whiteley Theorem 1)

**Lean:** `CombinatorialRigidity/BodyBar/KFrame.lean` (new file):
- `def Multigraph.kFrameMatroid (G : Multigraph V) (k : ℕ) : Matroid (Edge G × Fin k)` —
  the generic `k`-frame matroid, defined via `Matroid.ofFun` of
  the formal column-vector indexed by `(edge, j-th block)`, with
  indeterminate coefficients realized as a placement
  `Edge G × Fin k → R^(k · |V|)`. (Exact type signature decided
  in L2; alternative: define on `Edge G` directly with a "generic
  point" parameter.)
- `theorem kFrameMatroid_eq_unionPow_cycleMatroid` (Whiteley
  Theorem 1): `kFrameMatroid G k = Matroid.Union (fun _ : Fin k =>
  G.cycleMatroid)`.

Proof: column-reorder argument from Whiteley §2.1. Forward
(`F(G,X)` indep → forest union): identify a nonzero `|E|`-minor
of `F(G,X)` and a nonzero monomial; setting the variables of that
monomial to `1` and the rest to `0` yields a block-diagonal
matrix with each block a forest-incidence matrix. Reverse: given
the forest decomposition `E = ⨆ Eⱼ`, set the j-th variables for
edges of `Eⱼ` and `0` otherwise — reduces to `k` block-diagonal
forest matrices.

**Blueprint:** `def:k-frame-matrix`, `thm:k-frame-union-cycle`
(Whiteley Theorem 1). Cite `Matroid.Union` (mirror).

### Layer 3 — Tree-packing corollary (Tutte–Nash-Williams)

**Lean:** in the same file or a sibling `BodyBar/TreePacking.lean`:
- `theorem Multigraph.unionPow_cycleMatroid_indep_iff_count`: the
  Whiteley Corollary 3 form — independent in `k`-fold cycle-matroid
  union iff `|E'| ≤ k|V'| − k` on every non-empty subset.
  Proof: combine `kFrameMatroid_eq_unionPow_cycleMatroid` with
  `matroid_partition_eRk'` and the cycle-matroid rank formula
  `r(E') = |V'| − c(E')`.
- `theorem Multigraph.exists_kForest_partition_iff_count` — the
  classical Tutte–Nash-Williams: `G = ⨆ⱼ Tⱼ` with each `Tⱼ` a
  forest iff `|E'| ≤ k|V'| − k`.
- `corollary Multigraph.exists_spanningTree_partition_iff_count` —
  the spanning-tree refinement: when the count is tight on the
  whole graph, the `k` forests are spanning trees. (Whiteley
  Theorem 13 / Tay 5.3's "union of d spanning trees" version.)

**Blueprint:** `thm:tutte-nash-williams`, `cor:k-spanning-trees`.

### Layer 4 — Body-bar framework + rigidity matrix

**Lean:** `CombinatorialRigidity/BodyBar/Framework.lean`:
- `def BodyBarFramework.{n} (G : Multigraph V) : Type` — pair of
  the multigraph and a placement `p : Edge G → R^d` (d = n(n+1)/2)
  with the value at each bar interpreted as Plücker / two-extensor
  coordinates. Whether to constrain to `V(p-relations)` at the
  type level (yes / Prop / not at all) is a Layer 4 decision.
- `def BodyBarFramework.rigidityMap : ((V → R^d) →ₗ[ℝ] (Edge G → ℝ))` —
  one row per edge, structured as in Whiteley §3 / Tay §2.
- `def BodyBarFramework.IsInfinitesimallyRigid` — kernel-dimension
  characterization analogous to Phase 4's
  `Framework.IsInfinitesimallyRigid` (rank `d|V| − d`; trivial
  motions span the `d`-dim screw-motion space).
- Basic API mirroring Phase 4: rigidity-map monotonicity, kernel
  bounds, the trivial-motion subspace dimension fact.

**Blueprint:** `def:body-bar-framework`, `def:rigidity-map-body-bar`,
`def:infinitesimally-rigid-body-bar`.

### Layer 5a — Tay's theorem (specialization form)

**Lean:** `CombinatorialRigidity/BodyBar/TayTheorem.lean`:
- `theorem BodyBarFramework.exists_independent_iff_count` (Whiteley
  Theorem 8, witness form): there *exists* a body-bar framework on
  `G` in `Rⁿ` that is independent iff `|E'| ≤ d|V'| − d` for every
  non-empty subset (equivalently `G` is the union of `d`
  edge-disjoint forests, by L3).
- `theorem BodyBarFramework.exists_isInfinitesimallyRigid_iff_count`
  — the rigid + independent version of Tay's theorem (Tay
  Theorem 5.3 / Whiteley Theorem 8 combined): there exists an
  isostatic body-bar framework iff the tight count `|E| = d(b−1)`
  holds with `|E'| ≤ d|V'| − d` on every proper non-empty subset.

**Proof:** specialize each bar's two-extensor coordinate to the
standard basis vector `b_eⱼ = e_j(e) ∈ R^d`, where `j(e)` is the
forest index of `e` in a chosen Tutte–Nash-Williams partition (cf.
Whiteley Theorem 1's reverse direction, lifted from indeterminate
to real). Verify directly that this specialization is independent
+ rigid (block-diagonal `d`-by-`d` forest matrices, each
full-rank). The `b_eⱼ` coordinates lie on `V(p-relations)`
vacuously (single non-zero entry → degenerate Plücker coords),
so this is a valid body-bar realization.

**Blueprint:** `thm:tay-witness` (the existence-of-realization
form). Note that the "almost all body-bar realizations are rigid"
phrasing of Whiteley Theorem 8 is **not** proved in Phase 12 —
the irreducible-variety lift (Whiteley Proposition 6 / Lemma 7)
is deferred. The blueprint chapter should flag this and point at
Phase 13.

### Layer 5b — `[deferred]` Irreducible-variety lift

**Not in Phase 12.** Whiteley Proposition 6 / Lemma 7: if `V` is
an irreducible variety over an infinite field and `F = {F_i}` is
a finite family of polynomials with `V ⊈ V(F_i)` for each `i`,
then `V ⊈ ⋃ V(F_i)`. This is the "almost all body-bar frameworks
on a count-satisfying graph are rigid" upgrade.

Deferred because: (i) Phase 12's target is the existence-of-
realization form, and that's all Tay's theorem strictly says;
(ii) the lift requires irreducible-variety / Zariski-open
infrastructure that this project does not yet have (Phase 8's
linear-interpolation perturbation argument is the one-parameter
case; Whiteley's Proposition 6 is the multi-variable algebraic-
geometry version); (iii) Katoh–Tanigawa's reductions may not
require the lift in this strong form — the K-T existence proofs
use specific carefully-chosen realizations of the modified graphs.
Re-assess at Phase 13 opening; if needed, ship as a structural-
edit phase 12.5 or as Phase 13 Layer 0.

## Lemma checklist

High-level outline; per-Layer leaf-level lemmas live in the
blueprint chapter's dep-graph as red nodes (forward mode).

- [ ] **L1 (mirror):** `Matroid.Union`, `union_indep_iff'`,
  `matroid_partition'`, `matroid_partition_eRk'`,
  `PolymatroidFn`, `ofSubmodular`, `polymatroid_rank_eq`
- [ ] **L2 (k-frame):** `Multigraph.kFrameMatroid`,
  `kFrameMatroid_eq_unionPow_cycleMatroid` (Whiteley Theorem 1)
- [ ] **L3 (tree-packing):**
  `unionPow_cycleMatroid_indep_iff_count` (Whiteley Corollary 3),
  `exists_kForest_partition_iff_count` (Tutte–Nash-Williams),
  `exists_spanningTree_partition_iff_count`
- [ ] **L4 (framework):** `BodyBarFramework`, `rigidityMap`,
  `IsInfinitesimallyRigid`, basic monotonicity API
- [ ] **L5a (Tay):** `exists_independent_iff_count`,
  `exists_isInfinitesimallyRigid_iff_count`

## Open questions

- **Multigraph carrier (M-A vs M-B).** Decide in Layer 0.
- **Plücker coordinates: typed or untyped?** Should
  `BodyBarFramework.placement : Edge G → R^d` carry the
  p-relation constraint at the type level (e.g.,
  `Edge G → V(p-relations)`)? Or as a `Prop` field? Or untyped
  with the p-relations checked only where they matter (rigidity-
  matrix row equation)? Layer 4 decision.
- **`Matroid.ofFun` over what coefficient ring?** Phase 8 used
  `ℝ`; Whiteley's Theorem 1 proof is cleanest over
  `ℚ[X_{i,j}]` (or `ℤ[X_{i,j}]`). Phase 12 likely needs
  `Matroid.ofFun` over a polynomial ring; verify the
  `Matroid/Representation/Map.lean` API supports this. Layer 2
  blocker if it doesn't.
- **Trim depth for the `WIP/Submodular.lean` mirror.** 1236 lines
  is a lot to vendor. Aim to ship only the
  `PolymatroidFn` + `ofSubmodular` + `polymatroid_rank_eq`
  sub-API that Union needs. Layer 1 task.
- **Mirror upstream-issue: file or wait?** Open an issue against
  `apnelson1/Matroid` flagging that `WIP/{Union,Submodular}.lean`
  are zero-sorry / would-build-with-a-one-line-import-fix? Helpful
  for telegraphing the eventual upstream PR; file with the
  mirror.

## Hand-off / next phase

Written at phase end. Anticipated direction:

- **Phase 13 candidate: body-hinge / panel-hinge Tay–Whiteley.**
  Whiteley 1988 §3.3 / Tay 1989. Same matroid-union scaffolding
  applied to the modified multigraph `((d+1 choose 2) − 1)G`,
  with body-hinge framework + hinge-rigidity definitions
  layered on top of Phase 12's body-bar framework. Naturally
  short if Phase 12's L5b deferral holds (no extra variety
  machinery needed for the existence-form theorem).

- **Phase 14 candidate: molecular conjecture (Katoh–Tanigawa
  2011).** The capstone target the user named when scoping
  Phase 12. Needs panel-hinge from Phase 13 + the
  carefully-chosen-realization argument of K–T §3-§4.

The exact phase 13/14 split should be re-litigated when Phase 12
closes; the deferred L5b irreducible-variety lift is the principal
swing factor.
