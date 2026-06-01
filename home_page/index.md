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

Phases 1–11 are complete and carry no `sorry`s; **Phase 12 (Tay's
body-bar theorem) is blocked on an upstream prerequisite**, see below. The main theorem
[`SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le`](https://github.com/bryangingechen/CombinatorialRigidity/blob/master/CombinatorialRigidity/LamanTheorem.lean)
in `LamanTheorem.lean` is fully formalized in both directions; the
Lovász–Yemini matroid identification has landed in both combinatorial
form (Phase 7) and linear-matroid form via `Matroid.ofFun` (Phase 8,
`linearRigidityMatroid_eq_rigidityMatroid`). Phase 9 ships the basic
`(k, ℓ)`-pebble game of Lee–Streinu 2008 in the matroidal regime
`ℓ < 2k` with matroidal-independence corollary
`countMatroid_indep_iff_runPebbleGame`, on top of a verified-DFS
warmup under `CombinatorialRigidity/Search/`. Phase 10 bridges Phase
9's `noncomputable` `runPebbleGame` to an actually-runnable decision
procedure: the computable wrapper `runPebbleGameExec` under
`[LinearOrder V]`, canonical `Decidable` instances for `IsSparse k ℓ`
/ `IsTight` / `IsLaman`, and a `lake exe pebble-game` CLI binary
reading an edge-list file. Both `#eval (decide G.IsLaman)` and the
CLI reduce through the same compiled `runPebbleGameExec` body.
**Phase 11** reshapes Phase 9/10's `Option`-shaped pebble-game
algorithms (workhorses, math/exec wrappers, and `Decidable`
instances) to return a verdict-bearing `PebbleGameResult G k ℓ`
inductive whose constructors carry inline witnesses — the blocking
subset `V'` on the `NOT_SPARSE` branch, the partial orientation `D`
on the accept branches — and bumps the CLI to emit those witnesses
as `ARCS u v` / `BLOCKING n` + `VERTEX w` lines alongside the
trichotomy label, making the CLI's classification externally
checkable. The maximal reshape folds Phase 9's existence-style
failure-witness theorems into the reshaped `tryAddEdgeWith`'s
recursion (the certificate-form correctness theorem collapses into
the verdict's type) rather than shipping the witness work as a
sibling extraction wrapper.

**Phase 12** (blocked on an upstream prerequisite) extends the
development to body-bar frameworks in `Rⁿ`, targeting **Tay's
theorem** (Tay 1984): a multigraph `G` is the underlying graph of
an infinitesimally rigid body-bar framework in `Rⁿ` iff `G` is the
edge-disjoint union of `d = n(n+1)/2` spanning trees. The proof
route follows Whiteley 1988's matroid-union framing —
Tutte–Nash-Williams falls out as a corollary of Edmonds'
matroid-partition theorem applied to `d` copies of the cycle
matroid. Layer 0 (the forward-mode dep-graph in
`blueprint/src/chapter/body-bar.tex`) has landed, but the phase is
**blocked at Layer 1**: the matroid-union machinery it depends on
(`Matroid.Union`, Edmonds matroid partition) lives only in
`apnelson1/Matroid`'s `WIP/{Union,Submodular}.lean`, which do **not**
build at any upstream revision — they need a never-committed
`IsCircuitAxioms` module and the long-commented-out
`FinsetCircuitMatroid` API. The phase is on hold pending that
machinery building upstream (or a decision to formalize matroid-union
locally); Tay's theorem in existence-of-realization form (with the
algebraic-geometry lift to "almost all realizations are rigid"
deferred) is the eventual target. The longer-horizon
target beyond Phase 12 is the **molecular conjecture**
(Katoh–Tanigawa 2011).

The development is divided into the phases below, with Lean source
under
[`CombinatorialRigidity/`](https://github.com/bryangingechen/CombinatorialRigidity/tree/master/CombinatorialRigidity)
(early phases land in their own files; later phases may extend
existing files or refactor across several).

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
|    12 | Body-bar Tay theorem        | `CombinatorialRigidity/Matroid/`, `BodyBar/` (Layer 0 done; blocked)               |  ⋯  |

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
