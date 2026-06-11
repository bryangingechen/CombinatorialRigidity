# CombinatorialRigidity

[![Build & deploy site](https://github.com/bryangingechen/CombinatorialRigidity/actions/workflows/push.yml/badge.svg)](https://github.com/bryangingechen/CombinatorialRigidity/actions/workflows/push.yml)

> [!CAUTION]
> This is an ongoing **experiment** in autoformalization using LLMs.
> I (Bryan) have not yet fully vetted the prose or Lean code, so take everything you read here with a grain of salt.

A Lean 4 / mathlib4 formalization of combinatorial rigidity theory. Its
first goal is **Laman's theorem** (1970): for `n ≥ 2`, a graph is
generically rigid in the plane iff it contains a `(2, 3)`-tight spanning
subgraph. Beyond Laman's theorem the project formalizes the planar
rigidity matroid and an executable `(k, ℓ)`-sparsity decision procedure
(the Lee–Streinu pebble game), the abstract matroid-union machinery, Tay's
body-bar theorem and the body-hinge / panel-hinge Tay–Whiteley theorem
(Tay 1984/1989, Whiteley 1988), and — the longest-horizon target, in
progress — Katoh–Tanigawa 2011's proof of the **molecular conjecture**.

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

The development proceeds in four arcs (full plan in `ROADMAP.md`):

* **Laman's theorem** (phases 1–6) — both directions, via the Henneberg
  route, landing `isGenericallyRigid_two_iff_exists_isLaman_le`.
* **Rigidity matroid & sparsity decision** (phases 7–11) — the planar
  rigidity matroid as a mathlib `Matroid` (Lovász–Yemini, combinatorial
  and linear-matroid forms), and the Lee–Streinu `(k, ℓ)`-pebble game as
  an executable, certificate-carrying decision procedure (`Decidable`
  instances for `IsSparse` / `IsTight` / `IsLaman` and a
  `lake exe pebble-game` CLI emitting inline witnesses).
* **Body-bar & body-hinge rigidity** (phases 12–16) — abstract
  matroid-union / Edmonds-partition machinery (ported locally from
  `apnelson1/Matroid`), Tutte–Nash-Williams tree-packing, the `k`-frame
  matroid as a cycle-matroid union, Tay's body-bar theorem, and the
  body-hinge / panel-hinge Tay–Whiteley extension.
* **The molecular conjecture** (phases 17–26) — Katoh–Tanigawa 2011's
  proof, the project's largest single undertaking: the Grassmann–Cayley
  extensor algebra (Lemma 2.1), the panel-hinge rigidity matrix `R(G,p)`,
  the deficiency matroid `M(G̃)`, the combinatorial induction
  (Theorem 4.9), and the algebraic induction realizing that reduction at
  the rigidity-matrix rank (Theorem 5.5).

Phases 1–16 are complete and carry no `sorry`s — the development is fully
green through the body-hinge Tay–Whiteley theorem
(`Graph.BodyHingeFramework.body_hinge_tay`). Within the
molecular-conjecture program, phases 17–22 build the extensor algebra, the
panel-hinge rigidity matrix, the deficiency matroid, the combinatorial
induction, and the algebraic induction realizing that reduction at the
rigidity-matrix rank. All three cases of the realization theorem (Theorem
5.5) are now formalized at `d=3`, including the hardest, Katoh–Tanigawa's
**Case III** (`k=0`, no proper rigid subgraph); the formalized instance
holds modulo a small, explicitly tracked family of carried hypotheses —
chiefly the nested use of the induction at every degree of freedom. The
current frontier — now in progress — is discharging those carries by
restating the induction at full Katoh–Tanigawa strength (all `k`, genuine
hinges), then general `d`. The per-phase status table is on the
[project website](https://bryangingechen.github.io/CombinatorialRigidity/);
`ROADMAP.md` and the per-phase logs under `notes/` carry the detail.

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
