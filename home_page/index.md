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

Phases 1–15 are complete and carry no `sorry`s; **the body-bar
program (Phases 12–15) lands Tay's theorem**, and **Phase 16 (in
progress)** extends it to the body-hinge / panel-hinge Tay–Whiteley
theorem — see below. The main theorem
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

**Phases 12–15** (the body-bar program) extend the development to
body-bar frameworks in `Rⁿ`, targeting **Tay's theorem** (Tay 1984):
a multigraph `G` is the underlying graph of an infinitesimally rigid
body-bar framework in `Rⁿ` iff `G` is the edge-disjoint union of
`d = n(n+1)/2` spanning trees, via Whiteley 1988's matroid-union
framing. The program was re-scoped from a single blocked "Phase 12"
into a dependency-ordered chain after a 2026-06 re-investigation found
the matroid-union machinery already fully formalized (zero-sorry) in
`apnelson1/Matroid`, just bit-rotted onto a superseded constructor.
**Phase 12 (complete)** formalizes the abstract prerequisites —
the matroid-from-submodular-function construction + polymatroid rank
(Edmonds 1970), matroid union (Nash-Williams 1966 / Edmonds), Rado's
theorem (Rado 1942), and Edmonds' matroid-partition theorem (Edmonds
1965) — **locally** under `CombinatorialRigidity/Matroid/`, ported
from Peter Nelson's `apnelson1/Matroid` (Apache-2.0) and rebased onto
its live `FiniteCircuitMatroid` constructor; all
`blueprint/src/chapter/matroid-union.tex` dep-graph nodes are green.
**Phase 13 (complete)** derives Tutte–Nash-Williams tree-packing
(a multigraph is the edge-disjoint union of `k` forests iff it is
`(k,k)`-sparse, by specializing the Edmonds matroid-partition theorem
to `k` copies of `Graph.cycleMatroid`, with the connected-tight
spanning-tree refinement); **Phase 14 (complete)** then
identifies the `k`-frame matroid with the `k`-fold cycle-matroid union
(Whiteley Theorem 1), and **Phase 15 (complete)** assembles Tay's theorem
(`Graph.BodyBarFramework.tay_witness`) in existence-of-realization form —
a multigraph carries an independent (resp. isostatic) body-bar framework
in `ℝⁿ` iff it is `(d,d)`-sparse (resp. `(d,d)`-tight), `d = n(n+1)/2` —
the standard-basis witness for existence, the block-diagonal rank-upper-bound
for the converse (the algebraic-geometry lift to "almost all realizations
are rigid" deferred).

**Phase 16 (in progress)** extends this to the **body-hinge /
panel-hinge Tay–Whiteley theorem** (Tay 1989, Whiteley 1988),
existence-of-realization form, **via the matroid-union reduction to
Phase 15**. A hinge in `ℝⁿ` is an `(n−2)`-dimensional affine subspace
(a pin-joint in 2-space, a line-hinge in 3-space) that constrains all
but one of the `δ = n(n+1)/2` relative screw freedoms of the two bodies
it joins, so it behaves like a bundle of `δ−1` coincident body-bars.
A body-hinge framework on `G` is therefore the induced body-bar
framework on `(δ−1)·G` (each hinge replaced by `δ−1` parallel bars),
and the target — `G` carries an independent (resp. isostatic)
body-hinge framework iff `(δ−1)·G` is `(δ,δ)`-sparse (resp. tight) —
reduces node-for-node to Phase 15's `tay_witness` on `(δ−1)·G`. The
`(δ−1)·G` device is the multiplied graph of the longer-horizon
**molecular conjecture** (Katoh–Tanigawa 2011).

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
|    12 | Matroid foundations (submodular + union) | `CombinatorialRigidity/Matroid/` (ported from `apnelson1/Matroid`) | ✓ |
|    13 | Tutte–Nash-Williams tree-packing | `BodyBar/TreePacking.lean` | ✓ |
|    14 | k-frame = k-fold cycle union | `BodyBar/KFrame.lean` | ✓ |
|    15 | Body-bar Tay theorem        | `BodyBar/{Framework,TayTheorem}.lean` | ✓ |
|    16 | Body-hinge Tay–Whiteley theorem | `BodyBar/BodyHinge.lean` (planned) | in progress |

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
