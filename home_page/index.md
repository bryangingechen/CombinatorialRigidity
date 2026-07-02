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
  proof of the panel-hinge Tay–Whiteley conjecture, the project's largest
  single undertaking and current frontier.

Phases 1–16 are complete and carry no `sorry`s: the main theorem
[`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/CombinatorialRigidity/LamanTheorem.lean)
is formalized in both directions, and the development is fully green
through the body-hinge Tay–Whiteley theorem. Within the
molecular-conjecture program, the Grassmann–Cayley extensor algebra
(Lemma 2.1), the panel-hinge rigidity matrix `R(G,p)`, the deficiency
matroid `M(G̃)`, the combinatorial induction (Theorem 4.9), and the
algebraic induction realizing that reduction at the rigidity-matrix rank
(phases 17–23) are built. At full Katoh–Tanigawa strength (all degrees of
freedom, genuine hinges), **Theorem 5.5** (the realization theorem, all
three cases including the hardest, Case III: `k=0`, no proper rigid
subgraph) and **Theorem 5.6** (every multigraph realizes the deficiency
rank, reconciling the rigidity-matrix rank with the combinatorial
deficiency) are formalized at every dimension `d ≥ 3`, and the **molecular
conjecture itself** — Katoh–Tanigawa's Conjecture 1.2: a graph can be
realized as an infinitesimally rigid body-hinge framework iff it can be
realized as an infinitesimally rigid panel-hinge framework — is now a
theorem in the development
(`PanelHingeFramework.molecular_conjecture`). The current frontier is the
molecule application (phases 24–26): the 3-D bar-joint rigidity matroid,
projective invariance, and the protein-flexibility rank formula for the
square graph `G²`.
The table below and `ROADMAP.md` carry the fine-grained, live status.

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
|   24–26 | the 3-D bar-joint matroid, projective invariance, and the molecule application (Cor 5.7) | `Molecular/` | ◷ |

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
