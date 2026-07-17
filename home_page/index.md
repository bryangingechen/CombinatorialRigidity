---
layout: home
title: Combinatorial Rigidity
---

> **⚠️ Caution:** This is an ongoing **experiment** in autoformalization
> using LLMs. I (Bryan) have not yet fully vetted the prose or Lean code,
> so take everything you read here with a grain of salt.

A Lean 4 / mathlib4 formalization of combinatorial rigidity theory,
working toward [**Laman's theorem**](https://en.wikipedia.org/wiki/Laman_graph) (1970):

> For $n \ge 2$, a graph is generically rigid in the plane if and only if
> it contains a spanning subgraph with $2n - 3$ edges in which every
> subgraph on $k \ge 2$ vertices has at most $2k - 3$ edges.

## Resources

- [Blueprint (web)]({{ '/blueprint/' | relative_url }})
- [Blueprint (PDF)]({{ '/blueprint.pdf' | relative_url }})
- [Dependency graph]({{ '/blueprint/dep_graph_document.html' | relative_url }})
- [API documentation]({{ '/docs/' | relative_url }})
- [Upstreaming dashboard]({{ '/upstreaming/' | relative_url }})
- [GitHub repository](https://github.com/bryangingechen/CombinatorialRigidity)

## Project status

The development proceeds in four arcs (the full plan is in
[`ROADMAP.md`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/ROADMAP.md)):

- **Laman's theorem** (phases 1–6) — both directions, via the Henneberg route.
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

All four arcs — phases 1–26 — are complete and carry no `sorry`s: the main
theorem
[`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/CombinatorialRigidity/LamanTheorem.lean)
is formalized in both directions, the development is fully green through
the body-hinge Tay–Whiteley theorem, and the molecular-conjecture program
is formalized end-to-end. At full Katoh–Tanigawa strength (all degrees of
freedom, genuine hinges), **Theorem 5.5** (the realization theorem, all
three cases including the hardest, Case III: `k=0`, no proper rigid
subgraph) and **Theorem 5.6** (every simple spanning multigraph realizes
the deficiency rank, reconciling the rigidity-matrix rank with the
combinatorial deficiency) hold at every dimension `d ≥ 3`, and the
**molecular conjecture itself** — Katoh–Tanigawa's Conjecture 1.2, for
simple graphs: such a graph can be realized as an infinitesimally rigid
body-hinge framework iff it can be realized as an infinitesimally rigid
panel-hinge framework — is a theorem of the development
(`PanelHingeFramework.molecular_conjecture`). On top of it sits the
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
the reals.) The blueprint dependency graph is fully green.
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
