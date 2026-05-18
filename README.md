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
binary. Phase 11 (in progress) reshapes Phase 9/10's `Option`-shaped
pebble-game algorithms to return a verdict-bearing inductive carrying
inline witnesses — a blocking subset `V'` on the `NOT_SPARSE` branch,
the partial orientation `D` on the accept branches — making the CLI's
output externally checkable.

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

* **Phases 1–10 complete; Phase 11 in progress** — sparsity, Laman, Henneberg, frameworks,
  both directions of Laman's theorem
  (`isGenericallyRigid_two_iff_exists_isLaman_le`), the Lovász–Yemini
  matroid identification (combinatorial form), the linear-matroid
  framing of the planar rigidity matroid
  (`linearRigidityMatroid_eq_rigidityMatroid`), the basic
  `(k, ℓ)`-pebble game of Lee–Streinu 2008 with certificate-form
  correctness theorem (`runPebbleGame_correct`) and matroidal-
  independence corollary (`countMatroid_indep_iff_runPebbleGame`),
  and the executable pebble game — a computable wrapper
  `runPebbleGameExec` under `[LinearOrder V]`, canonical `Decidable`
  instances for `IsSparse k ℓ` / `IsTight` / `IsLaman` in the
  matroidal regime `ℓ < 2k`, and a `lake exe pebble-game` CLI binary
  that reads an edge-list file and prints
  `LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`. Both `#eval` and the
  CLI reduce through the same compiled `runPebbleGameExec` body. The
  project carries no `sorry`s. See `notes/Phase10.md` and
  `blueprint/src/chapter/executable.tex` for Phase 10 details.
  **Phase 11** reshapes the pebble-game algorithms (Phase 9
  workhorses, Phase 10 wrappers and `Decidable` instances) to
  return a `PebbleGameResult G k ℓ` verdict whose constructors
  carry inline witnesses — folding the deferred witness-extraction
  work into the canonical algorithm. The CLI then prints a
  checkable certificate on every branch. See `notes/Phase11.md`
  for the layer plan; the blueprint reshape lands in-place in
  `chapter/{dfs,pebble-game,executable}.tex` alongside each
  Layer's Lean.

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
