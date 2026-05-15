---
layout: home
title: Combinatorial Rigidity
---

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

All six phases are complete; the project carries no `sorry`s. The
main theorem
[`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/CombinatorialRigidity/LamanTheorem.lean)
in `LamanTheorem.lean` is fully formalized in both directions.

The development is divided into six phases, each in its own file under
[`CombinatorialRigidity/`](https://github.com/bryangingechen/CombinatorialRigidity/tree/master/CombinatorialRigidity).

| Phase | Topic                       | File(s)                                                        | Status |
|------:|-----------------------------|----------------------------------------------------------------|:------:|
|     1 | Sparsity                    | `EdgesIn.lean`, `Sparsity.lean`                                |   ✓    |
|     2 | Laman graphs                | `Laman.lean`                                                   |   ✓    |
|     3 | Henneberg moves             | `Henneberg.lean`                                               |   ✓    |
|     4 | Frameworks                  | `Framework.lean`                                               |   ✓    |
|     5 | Laman's theorem (⇐)         | `HennebergRigidity.lean`, `LamanTheorem.lean`                  |   ✓    |
|     6 | Laman's theorem (⇒)         | `RigidityMatroid.lean`, `LamanTheorem.lean`                    |   ✓    |

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
