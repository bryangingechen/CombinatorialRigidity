---
layout: home
title: Combinatorial Rigidity
---

> **⚠️ Caution:** This is an ongoing **experiment** in autoformalization
> using LLMs. I (Bryan) have not yet fully vetted the prose or Lean code,
> so take everything you read here with a grain of salt.

A Lean 4 / mathlib4 formalization of combinatorial rigidity theory. It
began with [**Laman's theorem**](https://en.wikipedia.org/wiki/Laman_graph)
(1970) on rigid graphs in the plane. It now covers Tay's body-bar theorem,
the Tay–Whiteley body-hinge theorem, Katoh–Tanigawa's 2011 proof of the
**molecular conjecture** with its application to molecules, and a
strengthening of the molecular conjecture that appears to be new, the
**pencil realization theorem**. The development carries no `sorry`s.

## The pencil realization theorem

A body-hinge framework in space is a set of rigid bodies joined in pairs by
hinge lines. Katoh and Tanigawa proved Tay and Whiteley's molecular
conjecture in a rank form: a graph's generic body-hinge rank is already
attained when the hinges at each body lie in a common plane, the body's
panel. Dually, it is attained when the hinges at each body pass through a
common point. The pencil realization theorem asks for both at once. Each
body gets a panel and a point of that panel, and every hinge at the body
lies in the panel and passes through the point, so the hinges at a body
form a *pencil* of lines. In the molecular reading, the panel is the plane
of an atom's bonds and the point is the atom's centre.

> **Theorem.** Over every infinite field, every multigraph $G$ with at
> least one body has a pencil realization of rank
> $6(|V(G)| - 1) - \operatorname{def}(\tilde G)$, the rank of a generic
> body-hinge realization of $G$. If $G$ is simple, the points of adjacent
> bodies can be chosen distinct, and if $G$ has a nondegenerate pencil
> realization at all, it has one of that rank.

The question was posed and proved by this project in 2026 (phases 39–40);
we know of no earlier statement of it. In Lean,
`CombinatorialRigidity.Molecular.pencil_realization_theorem` states it for
a multigraph on the whole body set, and `pencilPair_of_nonempty` for every
multigraph with at least one body. The proof is outlined
[below](#how-the-pencil-realization-theorem-is-proved), and given in full
in the [blueprint]({{ '/blueprint/' | relative_url }}).

## Resources

- [Blueprint (web)]({{ '/blueprint/' | relative_url }})
- [Blueprint (PDF)]({{ '/blueprint.pdf' | relative_url }})
- [Dependency graph]({{ '/blueprint/dep_graph_document.html' | relative_url }})
- [API documentation]({{ '/docs/' | relative_url }})
- [Upstreaming dashboard]({{ '/upstreaming/' | relative_url }})
- [GitHub repository](https://github.com/bryangingechen/CombinatorialRigidity)

## Project status

The development proceeded in four arcs, followed by further phases that
strengthen their results (the full plan is in
[`ROADMAP.md`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/ROADMAP.md)):

- **Laman's theorem** (phases 1–6) — for $n \ge 2$, a graph is generically
  rigid in the plane if and only if it contains a spanning subgraph with
  $2n - 3$ edges in which every subgraph on $k \ge 2$ vertices has at most
  $2k - 3$ edges; both directions, via the Henneberg route.
- **Rigidity matroid & sparsity decision** (phases 7–11) — the planar
  rigidity matroid as a mathlib `Matroid`, and an executable,
  certificate-carrying `(k, ℓ)`-pebble game (`Decidable` instances plus a
  `lake exe pebble-game` CLI).
- **Body-bar & body-hinge rigidity** (phases 12–16) — local matroid-union
  machinery (ported from `apnelson1/Matroid`), Tay's body-bar theorem
  (Tay 1984 / Whiteley 1988), and its body-hinge / panel-hinge
  Tay–Whiteley extension.
- **The molecular conjecture** (phases 17–26) — Katoh–Tanigawa 2011's
  proof of the panel-hinge Tay–Whiteley conjecture together with its
  molecule application, the project's largest single undertaking.

All four arcs — phases 1–26 — are complete and carry no `sorry`s: Laman's
theorem
[`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/CombinatorialRigidity/LamanTheorem.lean)
is formalized in both directions, the development is fully green through
the body-hinge Tay–Whiteley theorem, and the molecular-conjecture program
is formalized end-to-end. At full Katoh–Tanigawa strength (all degrees of
freedom, genuine hinges), **Theorem 5.5** (the realization theorem, all
three cases including the hardest, Case III: `k=0`, no proper rigid
subgraph) and **Theorem 5.6** (every simple spanning multigraph realizes
the deficiency rank, reconciling the rigidity-matrix rank with the
combinatorial deficiency) hold at every dimension `d ≥ 2`, and the
**molecular conjecture itself** — Katoh–Tanigawa's Conjecture 1.2, for
simple graphs: such a graph can be realized as an infinitesimally rigid
body-hinge framework iff it can be realized as an infinitesimally rigid
panel-hinge framework — is a theorem of the development
(`PanelHingeFramework.molecular_conjecture`). In the plane, where each hinge
is a pin joining two bodies and each panel is a line, the molecular
conjecture is Jackson–Jordán's 2008 theorem on pin-collinear body-and-pin
frameworks; the development proves it over every infinite field, by
Katoh–Tanigawa's argument (phase 40). On top of it sits the
molecule application: the generic bar-joint rigidity matroid in dimension
three, in linear-matroid form (phase 24); projective invariance plus the
molecule modelling equivalence — the chain identifying bar-joint motions
of the square graph `G²` with molecular and panel-hinge motions of `G`
(phase 25); and the capstone **molecule rank formula**
`r(G²) = 3|V| − 6 − def(G̃)` for a graph of minimum degree at least two
(Jackson–Jordán 2008, Katoh–Tanigawa Corollary 5.7;
`SimpleGraph.molecule_rank_formula`, phase 26) — the combinatorial
flexibility count for a molecule modelled on `G`.

Beyond the four arcs, phase 32 (closed 2026-07-16) added two further
Jackson–Jordán 2008 consequences of the rank formula: **Jacobs'
conjecture** (`G²` is independent in the 3-D generic rigidity matroid
iff it satisfies the 3-D Laman counting condition, unconditional now
that the rank formula is a theorem; `SimpleGraph.jacobs`) and the
**degree-1 rank formula** (the explicit `r(G²)` for connected graphs
with degree-1 vertices, by reduction to the two-core;
`SimpleGraph.degree_one_rank`). Phase 33 (closed 2026-07-17)
generalized the Katoh–Tanigawa chain from the real numbers to an
arbitrary **infinite field of any characteristic**: Theorems 5.5 and
5.6 and the molecular conjecture itself are now proved over any
infinite field, with the original real-number statements as the
special case — a level of generality that appears to be new. (The
molecule application, three-dimensional physical geometry, stays over
the reals.) Phase 34 (closed 2026-07-18) upgraded the
existence-of-realization theorems to their **generic form** ("almost
all realizations attain the generic rank"), following Jackson–Jordán
2010's coordinate approach: every bar-joint realization of `G²` at a
generic placement realizes the molecule rank formula and is rigid
whenever `5G` packs six edge-disjoint spanning trees; Tay's body-bar
theorem holds at every generic choice of bar endpoints; and the
body-hinge theorem holds at every generic choice of hinge positions,
with the non-generic parameter choices confined to the zero set of a
single nonzero polynomial in each case. Phase 35 (closed 2026-07-18)
recovered the **full multigraph strength** of Theorem 5.6 and of the
molecular conjecture itself, which the development above proves for
simple graphs: stating the panel side in Katoh–Tanigawa's own
hinge-coplanar model — each hinge required only to *lie in* a panel at
each endpoint body, rather than being the intersection of the two
panels — both results hold with parallel edges admitted
(`Molecular.molecular_conjecture_multigraph`), while the multigraph
equivalence is provably false for the intersection-based panel-hinge
frameworks the simple-graph statements use. Phases 39–40 (closed
2026-09-25 and 2026-09-29) then proved the pencil realization theorem,
stated above. The blueprint dependency graph is fully green.

### How the pencil realization theorem is proved

Phase 39 (closed 2026-09-25) reduced the theorem, in Lean, to two
*main-component statements*: every simple two-edge-connected multigraph on
at least three bodies has a pencil realization at the deficiency rank with
the points of adjacent bodies distinct, and a nondegenerate one at that rank
whenever it has a nondegenerate pencil realization at all. Phase 40 (closed
2026-09-29) proved both, formalizing a proof first worked out informally and
independently checked. Its first step extended Theorems 5.5 and 5.6 and the
molecular conjecture from dimension three down to the plane (above). The
proof then lifts pictures of the graph in the plane: a picture places each
body at a point of the plane, a height lifts that point into space, and the
hinge of an edge is the line through the lifted points of its ends. The
heights at which each body's point lies in a plane with its neighbours'
points form a linear space, the lifting space, whose dimension at a general
picture is Jackson–Jordán's rank formula for pin-collinear frameworks,
derived here from the plane case. The main component is the closure of
these lifts over the pictures at which the lifting space is smallest. For
every simple connected graph of minimum degree at least two, a general
member of it attains the deficiency rank, by an induction through
cut-vertex, bridge, cycle, ear, split-off and contraction steps; this gives
the first statement. The second does not follow this way, and is proved
instead inside the reduction's own induction.

The table below and `ROADMAP.md` carry the fine-grained status.

| Phase | Topic                       | File(s)                                                          | Status |
|------:|-----------------------------|------------------------------------------------------------------|:------:|
|     1 | Sparsity                    | `EdgesIn.lean`, `Sparsity.lean`                                  |   ✓    |
|     2 | Laman graphs                | `Laman.lean`                                                     |   ✓    |
|     3 | Henneberg moves             | `Henneberg.lean`                                                 |   ✓    |
|     4 | Frameworks                  | `Framework.lean`                                                 |   ✓    |
|     5 | Laman's theorem (⇐)         | `HennebergRigidity.lean`, `LamanTheorem.lean`                    |   ✓    |
|     6 | Laman's theorem (⇒)         | `RigidityMatroid.lean`, `LamanTheorem.lean`                      |   ✓    |
|     7 | Lovász–Yemini matroid id.   | `CountMatroid.lean`, `MatroidIdentification.lean`                |   ✓    |
|     8 | Linear-matroid framing      | `LinearRigidityMatroid.lean`                                     |   ✓    |
|     9 | Pebble game                 | `Search/DFS.lean`, `PebbleGame/{Basic,Algorithm,Correctness}.lean` |   ✓    |
|    10 | Executable pebble game      | `PebbleGame/{Exec,Examples}.lean`, `Main.lean`                   |   ✓    |
|    11 | Witness extraction          | `Search/DFS.lean`, `PebbleGame/{Basic,Algorithm,Correctness,Exec}.lean`, `Main.lean` |   ✓    |
|    12 | Matroid foundations (submodular + union) | `CombinatorialRigidity/Matroid/` (ported from `apnelson1/Matroid`) | ✓ |
|    13 | Tutte–Nash-Williams tree-packing | `BodyBar/TreePacking.lean` | ✓ |
|    14 | k-frame = k-fold cycle union | `BodyBar/KFrame.lean` | ✓ |
|    15 | Body-bar Tay theorem        | `BodyBar/{Framework,TayTheorem}.lean` | ✓ |
|    16 | Body-hinge Tay–Whiteley theorem | `BodyBar/BodyHinge.lean` | ✓ |
|    17 | Grassmann–Cayley extensor algebra | `Molecular/Extensor.lean` | ✓ |
|    18 | Panel-hinge rigidity matrix `R(G,p)` | `Molecular/RigidityMatrix.lean` | ✓ |
|    19 | `M(G̃)`, deficiency, `k`-dof graphs | `Molecular/Deficiency.lean` | ✓ |
|    20 | Combinatorial induction → Theorem 4.9 | `Molecular/Induction/` | ✓ |
|    21 | Algebraic induction: Thm 5.5 base + Cases I & II (+ the Grassmann–Cayley meet and the generic-max-rank device) | `Molecular/{Meet,AlgebraicInduction}/` | ✓ |
|    22 | The algebraic-induction realization layer at `d=3`: Cases I & III, Theorem 5.5 and Theorem 5.6 at full strength | `Molecular/` | ✓ |
|    23 | Case III at general `d` (Lemma 6.13) → Theorem 5.5/5.6 → the Molecular Conjecture (Conjecture 1.2) | `Molecular/` | ✓ |
|    24 | 3-D generic bar-joint rigidity matroid (linear-matroid form) | `GenericRigidityMatroid.lean` | ✓ |
|    25 | projective duality + the molecule modelling equivalence | `SquareGraph.lean`, `GeneralPositionPlacement.lean`, `Molecular/Molecule/` | ✓ |
|    26 | the molecule application (Corollary 5.7) | `Molecular/Molecule/`, `GenericRigidityMatroid.lean` | ✓ |
|    39 | the pencil realization theorem: reduction to two main-component statements | `Molecular/Molecule/Pencil/` | ✓ |
|    40 | the pencil realization theorem: the main-component proof of the two statements (and the plane case of Theorems 5.5/5.6) | `Molecular/` | ✓ |

See [`ROADMAP.md`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/ROADMAP.md)
for the full mathematical and engineering plan,
[`DESIGN.md`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/DESIGN.md)
for cross-cutting design rationale, and per-phase work logs under
[`notes/`](https://github.com/bryangingechen/CombinatorialRigidity/tree/master/notes).

## Building locally

```sh
lake exe cache get   # fetch precompiled mathlib oleans
lake build
```

The Lean toolchain version is pinned in `lean-toolchain` and tracks
mathlib.
