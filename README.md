# CombinatorialRigidity

[![Build & deploy site](https://github.com/bryangingechen/CombinatorialRigidity/actions/workflows/push.yml/badge.svg)](https://github.com/bryangingechen/CombinatorialRigidity/actions/workflows/push.yml)

A Lean 4 / mathlib4 formalization of combinatorial rigidity theory, working
toward **Laman's theorem** (1970): for `n ≥ 2`, a graph is generically rigid
in the plane iff it contains a `(2, 3)`-tight spanning subgraph. Phase 7
extends the development to the **Lovász–Yemini matroid identification**:
the planar rigidity matroid coincides with the `(2, 3)`-count matroid on
`E(K_V)`, packaged as a mathlib `Matroid` instance. Phase 8 reframes the
planar rigidity matroid as a linear matroid via `Matroid.ofFun` (from the
`apnelson1/Matroid` library) at a uniformly generic placement, and states
Lovász–Yemini in linear-matroid form. Phase 9 formalizes the basic
`(k, ℓ)`-pebble game of Lee–Streinu 2008 in the matroidal regime
`ℓ < 2k`, with a certificate-form correctness theorem and the matroidal-
independence corollary against the Phase 7 count matroid. Phase 10
bridges Phase 9's `noncomputable` `runPebbleGame` to an actually-runnable
decision procedure: a `Decidable G.IsLaman` instance backed by a
computable wrapper `runPebbleGameExec`, plus a `lake exe pebble-game` CLI
binary. Phase 11 reshapes Phase 9/10's `Option`-shaped
pebble-game algorithms to return a verdict-bearing inductive carrying
inline witnesses — a blocking subset `V'` on the `NOT_SPARSE` branch,
the partial orientation `D` on the accept branches — and bumps the CLI
to emit those witness lines alongside the trichotomy label, making the
CLI's classification externally checkable. **Phases 12–15** (in
progress) extend the development to higher-dimensional body-bar
rigidity, targeting **Tay's theorem** (Tay 1984) — `G` admits an
infinitesimally rigid body-bar framework in `Rⁿ` iff `G` is the
edge-disjoint union of `d = n(n+1)/2` spanning trees — via Whiteley's
matroid-union route (Whiteley 1988). The route is built bottom-up:
Phase 12 formalizes the abstract matroid-union / Edmonds-partition
machinery locally (ported from the `apnelson1/Matroid` library),
Phase 13 derives Tutte–Nash-Williams tree-packing, Phase 14 identifies
the `k`-frame matroid with the `k`-fold cycle-matroid union, and
Phase 15 assembles Tay's theorem. The longer-horizon target beyond is
the **molecular conjecture** (Katoh–Tanigawa 2011).

The development was originally hosted under `Archive/CombinatorialRigidity/`
in a fork of mathlib4 and has been lifted to this standalone, mathlib-downstream
project; commit history is preserved with paths rewritten.

## Links

* [Project website](https://bryangingechen.github.io/CombinatorialRigidity/)
* [Blueprint (web)](https://bryangingechen.github.io/CombinatorialRigidity/blueprint/)
* [Blueprint (PDF)](https://bryangingechen.github.io/CombinatorialRigidity/blueprint.pdf)
* [Dependency graph](https://bryangingechen.github.io/CombinatorialRigidity/blueprint/dep_graph_document.html)
* [API documentation](https://bryangingechen.github.io/CombinatorialRigidity/docs/)

## Project status

* **Phases 1–15 complete.**
* **Phases 1–11 (complete)** — sparsity, Laman, Henneberg, frameworks,
  both directions of Laman's theorem
  (`isGenericallyRigid_two_iff_exists_isLaman_le`), the Lovász–Yemini
  matroid identification (combinatorial form), the linear-matroid
  framing of the planar rigidity matroid
  (`linearRigidityMatroid_eq_rigidityMatroid`), the basic
  `(k, ℓ)`-pebble game of Lee–Streinu 2008 with matroidal-independence
  corollary (`countMatroid_indep_iff_runPebbleGame`), the executable
  pebble game (a computable wrapper `runPebbleGameExec` under
  `[LinearOrder V]`, canonical `Decidable` instances for
  `IsSparse k ℓ` / `IsTight` / `IsLaman` in the matroidal regime
  `ℓ < 2k`, and a `lake exe pebble-game` CLI binary), and the
  witness-extraction reshape that bumps `runPebbleGame` /
  `runPebbleGameExec` to a two-constructor verdict
  `PebbleGameResult G k ℓ` carrying inline witnesses on every branch
  (`.accept D _ _` with `D : PartialOrientation V`; `.reject V' _ _`
  with `V' : Finset V`). The CLI prints `LAMAN` /
  `SPARSE_NOT_TIGHT` / `NOT_SPARSE` as before, followed by witness
  lines (`ARCS u v` per arc on accept; `BLOCKING n` + `VERTEX w`
  lines per blocking-subset element on reject). Both `#eval` and
  the CLI reduce through the same compiled `runPebbleGameExec`
  body. The project carries no `sorry`s through Phase 11. See
  `notes/Phase11.md` for the layer plan; the blueprint reshape
  lands in-place in `chapter/{dfs,pebble-game,executable}.tex`.
  Phase 10 details are in `notes/Phase10.md` and
  `blueprint/src/chapter/executable.tex`.
* **Phases 12–15 (body-bar program)** — re-scoped from a single
  blocked "Phase 12" into a dependency-ordered chain after a 2026-06
  re-investigation found the matroid-union machinery already fully
  formalized (zero-sorry) in `apnelson1/Matroid`, just bit-rotted onto
  a superseded constructor:
  * **Phase 12 (complete)** — matroid foundations: the
    matroid-from-submodular-function construction + polymatroid rank
    (Edmonds 1970), matroid union (Nash-Williams 1966 / Edmonds) with
    its independence characterization, Rado's theorem (Rado 1942), and
    Edmonds' matroid-partition rank formula (Edmonds 1965), formalized
    **locally** under `CombinatorialRigidity/Matroid/`. The Lean is
    ported from Peter Nelson's `apnelson1/Matroid` (Apache-2.0; same
    license as this project and mathlib), rebased onto the package's
    live `FiniteCircuitMatroid` constructor. All
    `blueprint/src/chapter/matroid-union.tex` dep-graph nodes are green
    and carry no `sorry`s. See `notes/Phase12.md` for the Layer plan,
    prerequisites audit, and attribution discipline.
  * **Phase 13 (complete)** — Tutte–Nash-Williams tree-packing:
    specializing Phase 12's Edmonds matroid-partition theorem to `k`
    copies of `Graph.cycleMatroid`, a multigraph is the edge-disjoint
    union of `k` forests iff it is `(k,k)`-sparse
    (`Graph.tutte_nash_williams`), with the connected-tight spanning-tree
    refinement `Graph.isSpanningTreePacking_of_isTight` (Whiteley
    Theorem 13). Introduces a `Graph`-native `(k,ℓ)`-sparsity predicate.
    See `notes/Phase13.md`.
  * **Phase 14 (complete)** — the `k`-frame matroid = `k`-fold
    cycle-matroid union restricted to `E(G)` (Whiteley Theorem 1):
    the generic `k`-frame matroid `F(G,X)` (a linear matroid over
    indeterminate coefficients) equals `(⋃ⱼ G.cycleMatroid) ↾ E(G)`
    (`Graph.kFrameMatroid_eq_unionPow_cycleMatroid`), matching the two
    `(k,k)`-sparsity count-characterizations by matroid extensionality.
    `BodyBar/KFrame.lean`. See `notes/Phase14.md`.
  * **Phase 15 (complete)** — **Tay's theorem** itself in
    existence-of-realization form (`Graph.BodyBarFramework.tay_witness`):
    for `d = n(n+1)/2`, a multigraph `G` carries an independent body-bar
    framework in `ℝⁿ` iff `G` is `(d,d)`-sparse, and an isostatic one iff
    `(d,d)`-tight. The standard-basis witness (two-extensor coordinates
    `b_e = e_{j(e)}` on a tree-packing) gives the existence directions;
    the converse is the body-bar Lovász–Yemini rank-upper-bound
    (`finrank (span (rows on E')) ≤ d·r(E')`, the real specialization of
    Phase 14's `k`-frame forward count). `BodyBar/{Framework,TayTheorem}.lean`.
    See `notes/Phase15.md`. Whiteley's full
    "almost-all-realizations-are-rigid" lift via irreducible-variety
    machinery (Proposition 6) is deferred. The longer-horizon target
    beyond is the **molecular conjecture** (Katoh–Tanigawa 2011).

See `ROADMAP.md` for the canonical hand-off doc — directory layout, status,
mathematical plan, and engineering conventions. `DESIGN.md` carries
cross-cutting design rationale; `TACTICS-GOLF.md` carries idiom / golfing guidance and `TACTICS-QUIRKS.md` covers build-failure rescue.
Per-phase work logs live under `notes/`.

`CLAUDE.md` is the operating manual for AI coding agents (Claude Code et al.)
— it covers reading order, the per-session workflow, the end-of-session
friction review, and the `notes/PhaseN.md` template. Human contributors can
skim it but the primary audience is automated tooling.

## Build

```
lake exe cache get   # fetch precompiled mathlib oleans (optional but fast)
lake build
```

Lean toolchain version is pinned in `lean-toolchain` and tracks mathlib.

## Blueprint

The mathematical blueprint lives under `blueprint/`. The web and PDF
versions are built and deployed automatically by GitHub Actions on every
push to `master` (see `.github/workflows/push.yml`); to build it locally:

```sh
cd blueprint
pip install -r requirements.txt
inv web     # plastex output in blueprint/web/
inv bp      # PDF in blueprint/print/print.pdf
inv serve   # preview the web build at http://localhost:8000
```

The landing page source is in `home_page/`. Its `_config.yml` and the CI
workflow assume the GitHub Pages site is published at
`https://bryangingechen.github.io/CombinatorialRigidity/`; if the repo is
ever renamed or moved to a different owner, update both files together.

## Automation

- **`.github/workflows/hopscotch.yml`** — daily cron that tries to
  advance the mathlib pin in `lake-manifest.json` to mathlib's current
  `master`. Opens (or refreshes) a PR if the new commit builds; opens
  a tracking issue with the bisected breaking commit if not.
- **`.github/dependabot.yml`** — monthly grouped PR bumping any
  GitHub Actions used in `.github/workflows/`.
