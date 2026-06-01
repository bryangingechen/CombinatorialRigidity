# Phase 12 — Body-bar Tay theorem (blocked on upstream prereq)

**Status:** BLOCKED at Layer 1. Layer 0 complete (chapter dep-graph
populated); the phase cannot proceed because the matroid-union
machinery it depends on does not build at any `apnelson1/Matroid`
revision. See *Prerequisites audit* (corrected) and *Hand-off / next
phase* (resume criteria). The original prereq audit was conducted
against a state of `apnelson1/Matroid` that does not match any pushed
revision and was wrong.

This file is the per-phase work record. See `../ROADMAP.md` §12
for the high-level summary and `../DESIGN.md` for cross-cutting
design choices — notably *Migrating Phases 1–11 from `SimpleGraph`
to mathlib's `Graph`* (decided against; Phase 12 uses `Graph`, the
rest of the project stays on `SimpleGraph`).

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

Layer 0 done. The phase-opening commit (`6b662ad`/`3676d86`) already
synced the four user-facing status surfaces (ROADMAP Status table +
§12, README, `home_page/index.md`, `intro.tex` Phase plan +
dep-graph-status line) and committed the carrier decision. This commit
populates `blueprint/src/chapter/body-bar.tex` with the full
Whiteley-route dep-graph: 13 red nodes (no `\lean{}`/`\leanok` yet,
forward-mode) across the five subsections, with `\uses{}` chains
encoding the proof plan. `blueprint/verify.sh` green; all 13 nodes
render in the dep-graph; cross-ref / cite checks clean.

References gathered; matroid-package survey complete (verified against
the pinned `apnelson1/Matroid` rev); Whiteley 1988 §2–§3 and Tay 1984
§4–§5 read. **Multigraph carrier decided: mathlib's core `Graph α β`**
(see *Architectural choices*).

**Layer 1 is blocked (2026-06-01).** The planned first step — vendor
`WIP/Submodular.lean` building in isolation — fails: at the pinned rev
`e6852ce` (and at *every* `apnelson1/Matroid` ref, incl. the latest
upstream `main` `f3f7df3`) `WIP/Submodular.lean` imports
`Matroid.Constructions.IsCircuitAxioms`, a module that has **never
been committed** to the package (`git log --all` for that path is
empty), and its `ofSubmodular` is built on the `FinsetCircuitMatroid`
API, which is **commented out** in `Matroid/Axioms/Circuit.lean` and
has been for >1 year. So `PolymatroidFn` / `ofSubmodular` /
`Matroid.Union` exist nowhere as live, buildable code. The only branch
with a live `ofSubmodular` (`galois`) has *no* union machinery at all
and sits on Lean v4.10 (~20 releases behind our v4.30 pin). The
original "0 sorries, unbuilt only because of a renamed import" audit
does not match any pushed revision. See *Hand-off / next phase* for
the resume criteria; the corrected facts are in *Prerequisites audit*
and FRICTION `[matroid]` *WIP/{Union,Submodular} unbuildable*.

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

- **Matroid-union access via mirror, not upstream-then-consume —
  PLAN BLOCKED, see *Prerequisites audit* (corrected).** The intent
  was to vendor `apnelson1/Matroid`'s `WIP/Union.lean` (matroid-union
  `Matroid.Union`, `union_indep_iff'`; Edmonds matroid partition
  `matroid_partition'`, `matroid_partition_eRk'`) and its dependency
  `WIP/Submodular.lean` (`PolymatroidFn`, `ofSubmodular`,
  `polymatroid_rank_eq`) under a new `CombinatorialRigidity/Matroid/`
  mirror, with the broken import fixed. **This does not work:** the
  files do not build at any upstream revision — `WIP/Submodular.lean`
  imports a never-committed `Matroid.Constructions.IsCircuitAxioms`
  module, and its `ofSubmodular` rests on the commented-out
  `FinsetCircuitMatroid` API (dead upstream for >1 year). The "0
  sorries, one renamed import" reading was a mis-audit. Mirroring is
  still the right *access pattern* once the upstream machinery builds;
  it just is not available yet. The fallback — re-build matroid-union
  in the mirror on top of the live API at our pin
  (`IndepMatroid.ofFinite`/`ofFun`) — is genuine formalization, not
  vendoring, and is a deliberate decision recorded under *Hand-off*.

- **Multigraph carrier — DECIDED: mathlib's core `Graph α β`** (was
  the "M-A" option). `SimpleGraph V` (the Phase 1–11 carrier) cannot
  natively express the multi-edges Tay's count `d(b−1)` requires
  (`d = n(n+1)/2 ≥ 1`; for `n ≥ 2`, `d ≥ 3`, so most rigid body-bar
  multigraphs have parallel edges). The carrier is mathlib's **core**
  `Graph α β` (`Mathlib/Combinatorics/Graph/Basic.lean`:
  `vertexSet : Set α`, `IsLink : β → α → α → Prop`, `edgeSet : Set β`)
  — *not* a type vendored from `apnelson1/Matroid`. That package's
  whole `Graph` tree is built on mathlib's `Graph` (verified at our
  pinned rev: `Matroid/Graph/Basic.lean` imports
  `Mathlib.Combinatorics.Graph.*` with no local `structure Graph`,
  and `cycleMatroid (G : Graph α β) : Matroid β`), and the union
  machinery we vendor in Layer 1 speaks the same type. Edges are
  first-class (`edgeSet : Set β`), so the `d(b−1)` / `|E'| ≤ d|V'| − d`
  count bookkeeping is cleaner than under a `Sym2`-multiplicity
  wrapper, and Katoh–Tanigawa's `((d+1 choose 2)−1)G`
  parallel-multiplication is natively expressible.

  Refactor-risk assessment: `Graph α β` is the carrier mathlib has
  committed to (PR leanprover-community/mathlib4#24122,
  *feat(Combinatorics): multigraphs*, apnelson1 / Peter Nelson,
  merged 2025-05-14; embedded-set design mirroring `Matroid`).
  Adopting it tracks mathlib's direction rather than betting on a
  research repo, so carrier refactor risk is near nil. Ongoing
  graph-theory churn on Zulip (`HasAdj` / `GraphLike` unification,
  darts/walks, retrofitting `SimpleGraph` / `Digraph` onto embedded
  sets) is *additive* API on top of `Graph` and does not reshape its
  fields. See Zulip #graph theory *"What kind of graphs are in
  Mathlib already?"* and *"Set in definition of Graph"*. Lake
  resolves one mathlib for the whole build, so the package compiles
  against our mathlib pin — no separate pin-match check needed.

  - **(M-B) Thin wrapper `BodyBarGraph V := Sym2 V → ℕ` — considered,
    not adopted.** Edge-multiplicity function; would keep the
    `SimpleGraph`-centric idiom. Rejected: diverges from mathlib's
    committed carrier, the community explicitly weighed and set aside
    a `Sym2` / edge-labeling representation for multigraphs in favour
    of the `β` edge-type `Graph`, and it would force re-deriving the
    `cycleMatroid` bridge that the `Graph` carrier reuses for free.

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

> **CORRECTED 2026-06-01.** The "Unbuilt but proved (vendor in
> Layer 1)" block below was wrong and is struck through. The truth,
> verified directly against `.lake/packages/Matroid` at the pinned
> rev `e6852ce` and against every fetched upstream ref:
> - `WIP/Submodular.lean` imports `Matroid.Constructions.IsCircuitAxioms`,
>   a module **never committed** to the package on any branch
>   (`git log --all -- Matroid/Constructions/IsCircuitAxioms.lean` is
>   empty). So the file has never built as-is.
> - `WIP/Submodular.lean`'s `ofSubmodular` is built on
>   `FinsetCircuitMatroid.matroid/.mk/.intro_elimination_nontrivial/.matroid_isCircuit_iff`;
>   the entire `FinsetCircuitMatroid` structure + API is **commented
>   out** in `Matroid/Axioms/Circuit.lean` and has been since well
>   before our pin.
> - Consequently `PolymatroidFn` / `ofSubmodular` / `polymatroid_rank_eq`
>   / `Matroid.Union` / `matroid_partition'` are live, buildable code
>   at **no** revision. Latest upstream `main` (`f3f7df3`, +7 from our
>   pin) is identical on all three points. The only branch with a live
>   `ofSubmodular` (`galois`, 2024) has **no** union machinery and is
>   on Lean `v4.10` (~20 releases behind our `v4.30`), so unusable.
>
> Net: the matroid-union route is **blocked** until that machinery
> builds upstream, or we formalize it locally (see *Hand-off*). The
> "Ready (built …)" block below was re-verified and remains accurate.

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

**~~Unbuilt but proved (vendor in Layer 1)~~ — FALSE, see corrected
note above. The files do NOT build at any revision:**
- ~~`WIP/Submodular.lean` (1236 L, 0 sorries) — ships `PolymatroidFn`,
  `ofSubmodular`, `polymatroid_rank_eq`.~~ Imports a never-committed
  `IsCircuitAxioms` module; `ofSubmodular` depends on the
  commented-out `FinsetCircuitMatroid` API. Unbuildable.
- ~~`WIP/Union.lean` (597 L, 0 active sorries) — ships `Matroid.Union`,
  `union_indep_iff'`, `matroid_partition'` / `matroid_partition_eRk'`.~~
  Transitively depends on the unbuildable `Submodular`. Unbuildable.

**~~Trim list for the mirror~~ — moot while blocked.** There is
nothing buildable to trim. If the local-formalization fallback is
chosen (see *Hand-off*), the work is to *construct* `PolymatroidFn` /
`ofSubmodular` / `Matroid.Union` on top of the live API at our pin,
not to trim a vendored file.

## Layer plan

The chapter `blueprint/src/chapter/body-bar.tex` exists as a prose
skeleton (wired into `main.tex`) and serves as the authoritative
dep-graph for the phase once Layer 0 populates its nodes.
Per-Layer dep-graph nodes referenced below as `def:foo` /
`lem:foo` / `thm:foo` are the chapter's labels; create them as
each Layer's Lean lands and flip `\leanok` to green when the
matching Lean lemma names.

**Carrier conventions (from the decided `Graph α β` carrier).**
Bodies = vertices, type `α` (carrier `G.vertexSet : Set α`); bars =
edges, type `β` (carrier `G.edgeSet : Set β`). The graphic matroid is
`G.cycleMatroid : Matroid β`, so the `k`-frame matroid and its union
are also `Matroid β` (ground type = the edge type `β`). Phase-12
graph-level defs (`kFrameMatroid`, the sparsity predicate) live under
`namespace Graph` so dot-notation works on `G : Graph α β` and they
sit beside the package's `Graph.cycleMatroid`; body-bar framework
defs live under `CombinatorialRigidity` / `BodyBar`. The `Graph`
namespace is a deliberate departure from ROADMAP's "everything under
`SimpleGraph` or `CombinatorialRigidity`" convention — update that
convention's wording when the phase opens (Layer 0).

### Layer 0 — Phase opening; carrier decided; populate chapter dep-graph

**Lean:** (none yet) — the chapter and `Phase12.md` ship together.

**Blueprint:** `chapter/body-bar.tex` already exists as a prose
skeleton (intro + the section headers below, wired into `main.tex`);
Layer 0 populates each section with red dep-graph nodes (`\lean{}`
pointers without `\leanok`, `\uses{}` chains per the proof plan).
Sections (in chapter order):
- *Matroid-union machinery* (Whiteley §2.2; landing in L1).
- *The k-frame matroid as a union of cycle matroids* (Whiteley §2.1;
  landing in L2).
- *Tree-packing as a corollary* / Tutte–Nash-Williams (landing in L3).
- *Body-bar frameworks and the rigidity matrix* (definitions;
  landing in L4).
- *Tay's theorem (existence-of-realization form)* (landing in L5a).

Nodes flip green per Layer.

**Decisions to capture in this Layer's commit:**
- Multigraph carrier = mathlib's core `Graph α β` (decided; see
  *Architectural choices*). Record the `vertexSet`/`edgeSet`/`IsLink`
  accessor idioms used downstream.
- Namespace: graph-level defs under `namespace Graph` (dot-notation
  on `G : Graph α β`), framework defs under `CombinatorialRigidity` /
  `BodyBar`. Departs from ROADMAP's "everything under `SimpleGraph`
  or `CombinatorialRigidity`" rule — update that convention's wording
  in the same commit.
- Mirror directory placement and naming
  (`CombinatorialRigidity/Matroid/Constructions/{Submodular,Union}.lean`).
- Sync user-facing status surfaces per the *When this commit opens
  a phase* discipline in `../CLAUDE.md`: ROADMAP `§Phase 12` planning
  section + Status table row; `README.md`; `home_page/index.md`;
  `blueprint/src/chapter/intro.tex` §Phase plan enumerate +
  dep-graph-status line.

### Layer 1 — Matroid-union mirror — **BLOCKED (cannot vendor)**

> **Blocked 2026-06-01.** The original plan (vendor `WIP/Submodular.lean`
> + `WIP/Union.lean` with a one-line import fix) is impossible: those
> files do not build at any `apnelson1/Matroid` revision — see the
> corrected *Prerequisites audit* and FRICTION `[matroid]`
> *WIP/{Union,Submodular} unbuildable*. The struck-through plan below
> is retained for when the upstream machinery builds.

~~**Lean:** vendor `WIP/Submodular.lean` + `WIP/Union.lean` under
`CombinatorialRigidity/Matroid/Constructions/`~~ — not possible
(unbuildable upstream). Two ways forward, both requiring a deliberate
decision (recorded under *Hand-off / next phase*):
1. **Wait for upstream.** Re-attempt the vendor once `apnelson1/Matroid`
   ships a buildable `Matroid.Union` (live `FinsetCircuitMatroid` /
   `IsCircuitAxioms`). Lowest effort; indefinite timeline.
2. **Formalize matroid-union locally.** Build `PolymatroidFn` /
   `ofSubmodular` / `Matroid.Union` / Edmonds partition in the mirror
   on top of the live API at our pin. This is the hardest single piece
   of Phase 12 — effectively its own sub-phase — not a copy-paste.

**Friction entry (DONE):** filed in `FRICTION.md` under [Open] tagged
`[matroid]` — *WIP/{Union,Submodular}.lean unbuildable at all
`apnelson1/Matroid` refs* — recording the analysis and the upstream
issue to file. (Not a *Mirrored* entry: nothing was mirrorable.)

**Blueprint:** flip `\leanok` on the matroid-union definition + the
union-indep-iff / matroid-partition statements (re-stated in the
chapter as facts cited from the mirror, not re-proven in prose).

### Layer 2 — `k`-frame matroid = `k`-fold union of cycle matroids (Whiteley Theorem 1)

**Lean:** `CombinatorialRigidity/BodyBar/KFrame.lean` (new file):
- `def Graph.kFrameMatroid (G : Graph α β) (k : ℕ) : Matroid β` —
  the generic `k`-frame matroid on the edge type `β`, defined via
  `Matroid.ofFun` of the formal `k·|V|`-column matrix whose row for
  edge `e` carries indeterminate coefficients across the `k` blocks.
  (Exact construction — `ofFun` over which coefficient ring, and
  whether the realization is `β → R^(k·|V|)` or restricted to
  `G.edgeSet` — is an L2 decision; see *Open questions*.)
- `theorem Graph.kFrameMatroid_eq_unionPow_cycleMatroid` (Whiteley
  Theorem 1): `kFrameMatroid G k = Matroid.Union (fun _ : Fin k =>
  G.cycleMatroid)` (both sides `Matroid β`).

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
- `def Graph.IsSparse` / `Graph.IsTight (G : Graph α β) (k ℓ : ℕ)` —
  the `Graph`-native `(k,ℓ)`-sparsity / tightness predicate
  (`|E'| ≤ k|V'| − ℓ` on non-empty subsets; tight = sparse + global
  equality). Introduced **fresh** here so Tay can be stated in
  sparsity terms (the form we naturally think of it in); **not**
  migrated from Phase 9/10's `SimpleGraph` sparsity — see
  `../DESIGN.md` *Migrating Phases 1–11 …*. Body-bar Tay is the
  `ℓ = k = d` case.
- `theorem Graph.unionPow_cycleMatroid_indep_iff_isSparse`: the
  Whiteley Corollary 3 form — a set is independent in the `k`-fold
  cycle-matroid union iff `G.IsSparse k k`. Proof: combine
  `kFrameMatroid_eq_unionPow_cycleMatroid` with
  `matroid_partition_eRk'` and the cycle-matroid rank formula
  `r(E') = |V'| − c(E')`.
- `theorem Graph.exists_kForest_partition_iff_isSparse` — the
  classical Tutte–Nash-Williams: `G = ⨆ⱼ Tⱼ` with each `Tⱼ` a
  forest iff `G.IsSparse k k`.
- `corollary Graph.exists_spanningTree_partition_iff_isTight` —
  the spanning-tree refinement: when the count is tight on the
  whole graph (`G.IsTight k k`), the `k` forests are spanning trees.
  (Whiteley Theorem 13 / Tay 5.3's "union of d spanning trees".)

**Blueprint:** `def:graph-sparse`, `thm:tutte-nash-williams`,
`cor:k-spanning-trees`.

### Layer 4 — Body-bar framework + rigidity matrix

**Lean:** `CombinatorialRigidity/BodyBar/Framework.lean`:
- `def BodyBarFramework (n : ℕ) (G : Graph α β) : Type` — pair of
  the multigraph and a placement assigning each bar (edge in `β`,
  or `G.edgeSet`) a value in `R^d` (`d = n(n+1)/2`), interpreted as
  Plücker / two-extensor coordinates. Whether to constrain to
  `V(p-relations)` at the type level (yes / Prop / not at all) is a
  Layer 4 decision (see *Open questions*).
- `def BodyBarFramework.rigidityMap` — a linear map from body
  motions (`G.vertexSet → R^d`) to bar constraints (`G.edgeSet → ℝ`),
  one row per bar, structured as in Whiteley §3 / Tay §2.
- `def BodyBarFramework.IsInfinitesimallyRigid` — kernel-dimension
  characterization analogous to Phase 4's
  `Framework.IsInfinitesimallyRigid` (rank `d·b − d`, `b = |V|`;
  trivial motions span the `d`-dim screw-motion space).
- Basic API mirroring Phase 4: rigidity-map monotonicity, kernel
  bounds, the trivial-motion subspace dimension fact.

**Blueprint:** `def:body-bar-framework`, `def:rigidity-map-body-bar`,
`def:infinitesimally-rigid-body-bar`.

### Layer 5a — Tay's theorem (specialization form)

**Lean:** `CombinatorialRigidity/BodyBar/TayTheorem.lean`:
- `theorem BodyBarFramework.exists_independent_iff_isSparse`
  (Whiteley Theorem 8, witness form): there *exists* an independent
  body-bar framework on `G` in `Rⁿ` iff `G.IsSparse d d` (equivalently
  `G` is the union of `d` edge-disjoint forests, by L3).
- `theorem BodyBarFramework.exists_isInfinitesimallyRigid_iff_isTight`
  — the rigid + independent version of Tay's theorem (Tay
  Theorem 5.3 / Whiteley Theorem 8 combined): there exists an
  isostatic body-bar framework iff `G.IsTight d d` (the tight count
  `|E| = d(b−1)` together with `G.IsSparse d d`).

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
blueprint chapter's dep-graph as red nodes (forward mode). The
chapter dep-graph node labels are listed alongside each Layer (all
red as of Layer 0; flip `\leanok` + add `\lean{}` per Layer).

- [x] **L0 (chapter dep-graph):** `body-bar.tex` populated with 13
  red nodes; user-facing status surfaces synced (phase-open commit).
- [ ] **L1 (mirror) — BLOCKED:** `Matroid.Union`, `union_indep_iff'`,
  `matroid_partition'`, `matroid_partition_eRk'`,
  `PolymatroidFn`, `ofSubmodular`, `polymatroid_rank_eq` —
  nodes `def:matroid-union`, `lem:union-indep-iff`,
  `thm:matroid-partition-rank`. Cannot be vendored: unbuildable at
  every `apnelson1/Matroid` ref (see *Prerequisites audit*). Blocks
  L2–L5a, which all `\uses` the union machinery.
- [ ] **L2 (k-frame):** `Graph.kFrameMatroid`,
  `Graph.kFrameMatroid_eq_unionPow_cycleMatroid` (Whiteley Theorem 1)
  — nodes `def:k-frame-matroid`, `thm:k-frame-union-cycle`
- [ ] **L3 (tree-packing):** `Graph.IsSparse` / `Graph.IsTight`,
  `Graph.unionPow_cycleMatroid_indep_iff_isSparse` (Whiteley
  Corollary 3), `Graph.exists_kForest_partition_iff_isSparse`
  (Tutte–Nash-Williams),
  `Graph.exists_spanningTree_partition_iff_isTight` — nodes
  `def:graph-sparse`, `thm:unionPow-cycle-indep-iff-sparse`,
  `thm:tutte-nash-williams`, `cor:k-spanning-trees`
- [ ] **L4 (framework):** `BodyBarFramework`, `rigidityMap`,
  `IsInfinitesimallyRigid`, basic monotonicity API — nodes
  `def:body-bar-framework`, `def:rigidity-map-body-bar`,
  `def:infinitesimally-rigid-body-bar`
- [ ] **L5a (Tay):** `exists_independent_iff_isSparse`,
  `exists_isInfinitesimallyRigid_iff_isTight` — node `thm:tay-witness`

## Open questions

- **Multigraph carrier.** DECIDED — mathlib's core `Graph α β`
  (see *Architectural choices made up front*).
- **Plücker coordinates: typed or untyped?** Should the body-bar
  placement (`β → R^d`, or on `G.edgeSet`) carry the p-relation
  constraint at the type level (e.g., land in `V(p-relations)`)? Or
  as a `Prop` field? Or untyped with the p-relations checked only
  where they matter (rigidity-matrix row equation)? Layer 4 decision.
- **`Matroid.ofFun` over what coefficient ring?** Phase 8 used
  `ℝ`; Whiteley's Theorem 1 proof is cleanest over
  `ℚ[X_{i,j}]` (or `ℤ[X_{i,j}]`). Phase 12 likely needs
  `Matroid.ofFun` over a polynomial ring; verify the
  `Matroid/Representation/Map.lean` API supports this. Layer 2
  blocker if it doesn't.
- ~~**Trim depth for the `WIP/Submodular.lean` mirror.**~~ Moot —
  the file is unbuildable, there is nothing to vendor/trim (see
  *Prerequisites audit*).
- **Upstream issue: file against `apnelson1/Matroid`.** No longer a
  "would-build-with-a-one-line-fix" telegraph — the honest issue is
  that `WIP/{Union,Submodular}.lean` reference a never-committed
  `IsCircuitAxioms` module and the commented-out `FinsetCircuitMatroid`
  API, so they do not build at any ref. Filing it asks the maintainer
  whether the matroid-union machinery is expected to be revived
  (and roughly when), which directly informs the resume decision
  below. **Action item, not yet filed.**

## Hand-off / next phase

**The phase is PAUSED, blocked at Layer 1 (2026-06-01).** It is not
closed and not complete; do not flip the ROADMAP row to ✓. The next
agent should NOT dispatch "continue Phase 12" work until the blocker
below is resolved by a human decision.

**The blocker.** The whole Whiteley route depends on matroid-union
(`Matroid.Union`, Edmonds partition), which the plan assumed it could
vendor from `apnelson1/Matroid`'s `WIP/{Union,Submodular}.lean`. Those
files do not build at any upstream revision (never-committed
`IsCircuitAxioms`; commented-out `FinsetCircuitMatroid`). Full analysis
in *Prerequisites audit* (corrected) and FRICTION `[matroid]`.

**Resume options (a human picks one):**
1. **Wait for upstream** to ship a buildable `Matroid.Union`, then
   resume Layer 1 as the originally-planned vendor. Lowest effort,
   indefinite timeline. Recommended interim default. Resume trigger:
   `apnelson1/Matroid`'s `WIP/Union.lean` (or a relocated equivalent)
   builds against a Lean toolchain compatible with our mathlib pin.
2. **Formalize matroid-union locally** in the mirror on top of the
   live API at our pin (`IndepMatroid.ofFinite`/`ofFun`): construct
   `PolymatroidFn` / `ofSubmodular` / `Matroid.Union` / Edmonds
   partition. This is real formalization (effectively its own
   sub-phase, the hardest single piece of Phase 12), so it warrants a
   Layer-plan rewrite before any Lean lands.
3. **Switch to Tay 1984's induction route** (avoids matroid-union;
   considered and set aside in *Architectural choices* — heavier in
   new combinatorial scaffolding, no Phase 7/8 reuse). Full Layer-plan
   rewrite + re-read of Tay §4–§5.

**Immediate non-blocked action items** (do not require the decision):
- File the upstream issue against `apnelson1/Matroid` (see *Open
  questions*) — its answer informs option 1's timeline.

Layer 0's dep-graph (`blueprint/src/chapter/body-bar.tex`, 13 red
nodes) is valid forward-mode planning work and stays as-is under all
three options.

### Anticipated follow-on phases (unchanged; gated behind the above)

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
