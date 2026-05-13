# CombinatorialRigidity

A Lean 4 / mathlib4 formalization of combinatorial rigidity theory, working
toward **Laman's theorem** (1970): for `n ≥ 2`, a graph is generically rigid
in the plane iff it contains a `(2, 3)`-tight spanning subgraph.

The development was originally hosted under `Archive/CombinatorialRigidity/`
in a fork of mathlib4 and has been lifted to this standalone, mathlib-downstream
project; commit history is preserved with paths rewritten.

## Project status

* Phases 1–5 complete: sparsity / Laman / Henneberg / frameworks / the (⇐)
  direction of Laman's theorem.
* Phase 6 (the (⇒) direction, via rigidity-matroid duality) not yet started;
  `IsGenericallyRigid.exists_isLaman_le` is the remaining `sorry`.

See `ROADMAP.md` for the canonical hand-off doc — read it first when picking
up the project. `DESIGN.md` carries cross-cutting design rationale and
`TACTICS.md` carries tactical guidance. Per-phase work logs live under
`notes/`.

## Build

```
lake exe cache get   # fetch precompiled mathlib oleans (optional but fast)
lake build
```

Lean toolchain version is pinned in `lean-toolchain` and tracks mathlib.
