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
(Tay 1984/1989, Whiteley 1988), and — the longest-horizon target —
Katoh–Tanigawa 2011's proof of the **molecular conjecture**, now fully
formalized at every dimension together with its molecule application, the
protein-flexibility rank formula `r(G²) = 3|V| − 6 − def(G̃)`.

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
  (Theorem 4.9), the algebraic induction realizing that reduction at
  the rigidity-matrix rank (Theorem 5.5), and the molecule application
  (Corollary 5.7).

All four arcs — phases 1–26 — are complete and carry no `sorry`s. The
development is fully green through the body-hinge Tay–Whiteley theorem
(`Graph.BodyHingeFramework.body_hinge_tay`), and the molecular-conjecture
program is formalized end-to-end at full Katoh–Tanigawa strength (all
degrees of freedom, genuine hinges): **Theorem 5.5** (the realization
theorem, all three cases including the hardest, Case III: `k=0`, no proper
rigid subgraph) and **Theorem 5.6** (every simple spanning multigraph
realizes the deficiency rank, reconciling the rigidity-matrix rank with the
combinatorial deficiency) hold at every dimension `d ≥ 3`, and the
**molecular conjecture itself** — Katoh–Tanigawa's Conjecture 1.2, for
simple graphs: such a graph can be realized as an infinitesimally rigid
body-hinge framework iff it can be realized as an infinitesimally rigid
panel-hinge framework — is a theorem of the development
(`PanelHingeFramework.molecular_conjecture`). On top of it sits the molecule
application: the generic bar-joint rigidity matroid in dimension three in
linear-matroid form (phase 24), projective invariance plus the molecule
modelling equivalence identifying bar-joint motions of the square graph
`G²` with molecular and panel-hinge motions of `G` (phase 25), and the
capstone **molecule rank formula** `r(G²) = 3|V| − 6 − def(G̃)` for a graph
of minimum degree at least two (Jackson–Jordán 2008, Katoh–Tanigawa
Corollary 5.7; `SimpleGraph.molecule_rank_formula`, phase 26) — the
combinatorial flexibility count for a molecule modelled on `G`. The
per-phase status table is on the
[project website](https://bryangingechen.github.io/CombinatorialRigidity/);
`ROADMAP.md` and the per-phase logs under `notes/` carry the detail.

Beyond the four arcs, phase 32 (closed 2026-07-16) added two further
Jackson–Jordán 2008 consequences of the rank formula: **Jacobs'
conjecture** (`G²` is independent in the 3-D generic rigidity matroid
iff it satisfies the 3-D Laman counting condition, unconditional now
that the rank formula is a theorem; `SimpleGraph.jacobs`) and the
**degree-1 rank formula** (the explicit `r(G²)` for connected graphs
with degree-1 vertices — where the rank formula's minimum-degree
hypothesis fails — by reduction to the two-core;
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
whenever `5G` packs six edge-disjoint spanning trees
(`SimpleGraph.molecule_generic_square_packing`); Tay's body-bar
theorem holds at every generic choice of bar endpoints; and the
body-hinge theorem holds at every generic choice of hinge positions —
a framework at generic hinges is infinitesimally rigid iff `(D−1)·G`
packs `D` edge-disjoint spanning trees
(`isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`),
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
frameworks the simple-graph statements use. The blueprint dependency
graph is fully green.

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
