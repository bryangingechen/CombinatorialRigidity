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
CLI's classification externally checkable. **Phases 12–15** (complete)
extend the development to higher-dimensional body-bar rigidity,
culminating in **Tay's theorem** (Tay 1984) — `G` admits an
infinitesimally rigid body-bar framework in `Rⁿ` iff `G` is the
edge-disjoint union of `d = n(n+1)/2` spanning trees — via Whiteley's
matroid-union route (Whiteley 1988). The route is built bottom-up:
Phase 12 formalizes the abstract matroid-union / Edmonds-partition
machinery locally (ported from the `apnelson1/Matroid` library),
Phase 13 derives Tutte–Nash-Williams tree-packing, Phase 14 identifies
the `k`-frame matroid with the `k`-fold cycle-matroid union, and
Phase 15 assembles Tay's theorem. **Phase 16** (complete) extends
this to the **body-hinge / panel-hinge Tay–Whiteley theorem** (Tay
1989, Whiteley 1988): a hinge behaves like a bundle of `δ−1` coincident
body-bars (`δ = n(n+1)/2`), so a body-hinge framework on `G` reduces to
a body-bar framework on `(δ−1)·G` (each hinge replaced by `δ−1`
parallel bars), and the rigidity characterization reduces to Phase 15
on `(δ−1)·G`. The longer-horizon target beyond is the **molecular
conjecture** (Katoh–Tanigawa 2011).

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

* **Phases 1–21 + 21a complete (Phase 21 GREEN-modulo-21b — all genericity-free content green, the shared genericity device Claim 6.4/6.9 scoped out into sub-phase 21b as a cited black-box); Phase 21b in progress; Phases 22–26 planned.**
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
    machinery (Proposition 6) is deferred.
* **Phase 16 (complete)** — the **body-hinge / panel-hinge
  Tay–Whiteley theorem** (`Graph.BodyHingeFramework.body_hinge_tay`;
  Tay 1989, Whiteley 1988), existence-of-realization form, **via the
  matroid-union reduction to Phase 15**. A hinge in `ℝⁿ` is an
  `(n−2)`-dimensional affine subspace (a pin-joint in 2-space, a
  line-hinge in 3-space) that constrains all but one of the
  `δ = n(n+1)/2` relative screw freedoms of the two bodies it joins, so
  it behaves like a bundle of `δ−1` coincident body-bars. A body-hinge
  framework on `G` is defined as the induced body-bar framework on
  `(δ−1)·G` (each hinge replaced by `δ−1` parallel bars); `G` carries
  an independent (resp. isostatic) body-hinge framework in `ℝⁿ` iff
  `(δ−1)·G` is `(δ,δ)`-sparse (resp. tight) — equivalently the
  edge-disjoint union of `δ` forests — reducing node-for-node to
  Phase 15's `tay_witness` on `(δ−1)·G`. The `(δ−1)·G` device is
  exactly the multiplied graph in Katoh–Tanigawa 2011's
  molecular-conjecture statement, the longer-horizon target beyond.
  Forward-mode phase; the chapter `body-hinge.tex` is the authoritative
  dep-graph. `BodyBar/BodyHinge.lean`. See `notes/Phase16.md`.
* **Phase 17 (complete)** — opens the longer-horizon **molecular
  conjecture program** (Phases 17–26; Tay–Whiteley, proved by
  Katoh–Tanigawa 2011), the project's largest single undertaking. Phase
  17 formalizes the **Grassmann–Cayley / extensor-algebra** layer
  (Katoh–Tanigawa §2.1): homogeneous coordinates `p ↦ (p,1)`, extensors
  as decomposable elements of `⋀ʲ ℝ^(d+1)`, the join `∨`, Plücker
  coordinates with Katoh–Tanigawa's sign convention, and the
  affine-subspace extensor `C(·)` — culminating in **Lemma 2.1**: the
  `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely
  independent points are linearly independent, the linear-algebra
  foundation the conjecture's hardest case (Case III) bottoms out on.
  Forward-mode phase; the chapter `extensor.tex` is the authoritative
  dep-graph. `Molecular/Extensor.lean`. See `notes/Phase17.md` and
  the program-level plan in `notes/MolecularConjecture.md`.
* **Phase 18 (complete)** — stratum 2 of the molecular program: the
  **genuine panel-hinge rigidity matrix** `R(G,p)` (Katoh–Tanigawa
  §2.2–2.4, §5 prep). A body-hinge framework assigns a `(d−2)`-affine
  hinge to each edge; its supporting `(d−1)`-extensor `C(p(e))` (Phase
  17) constrains the `D`-dimensional screw centers by
  `S(u) − S(v) ∈ span C(p(e))`. The phase builds the null space
  `Z(G,p)` of `R(G,p)` (basis-free, on the degree-`k` graded screw
  space `⋀^k ℝ^(k+2)`, `finrank = D`), the `D` trivial motions and the
  codimension form of `rank ≤ D(|V|−1)`, and the three rank Lemmas
  5.1–5.3 (pin-a-body, parallel-hinges-full, rotation semicontinuity),
  all green — the full rank-form substrate the algebraic induction runs
  on. The reconciliation with Phase 16's reduction-form Prop 1.1 is a
  top-of-DAG corollary depending on the analytic generic-rank theorem;
  it is presented with the algebraic induction (Phase 21+).
  `Molecular/RigidityMatrix.lean`.
  See `notes/Phase18.md` and `notes/MolecularConjecture.md`.
* **Phase 19 (complete)** — stratum 3 of the molecular program: the
  matroidal substrate of the conjecture's algebraic induction
  (Katoh–Tanigawa §2.5, §3). Builds the matroid `M(G̃)` — the
  `(D,D)`-count matroid of the multiplied graph `G̃ = (D−1)·G` at the
  boundary regime `ℓ = 2k = D` (the `D`-fold graphic-matroid union of
  Phases 13/14 + Tutte–Nash-Williams, not the `ℓ<2k` count matroid of
  Phase 7) — the `D`-deficiency `def(G̃)`, the `k`-dof / minimal-`k`-dof
  hierarchy, rigid subgraphs (KT Lemmas 3.1/3.3/3.4), and the
  `def(G̃) = corank M(G̃)` bridge (Jackson–Jordán 2009 Thm 6.1 / Cor 6.2,
  proved in-repo axiom-free) — the matroidal half of the Phase 16
  reconciliation. `Molecular/Deficiency.lean`. See `notes/Phase19.md` and
  `notes/MolecularConjecture.md`.
* **Phase 20 (complete)** — stratum 4 of the molecular program: the
  **combinatorial induction** of Katoh–Tanigawa's proof (§3.4–3.5, §4).
  Develops the graph operations on `Graph α β` (vertex removal,
  splitting-off `G_v^{ab}` at a degree-2 vertex, its inverse
  edge-splitting, and rigid-subgraph contraction), the degree-of-freedom
  tracking lemmas (4.3–4.8), and the capstone **Theorem 4.9**: every
  minimal `0`-dof-graph reduces to the two-vertex double edge by
  splitting-off and rigid-subgraph contraction — the combinatorial
  skeleton the algebraic induction of Phases 21–23 realizes at the
  rigidity-matrix rank. The formalization surfaced two route findings:
  KT Lemma 4.1 (the forest surgery) is over-quantified with a
  balanced-packing gloss in its proof, routed around via a
  deficiency-count argument; and KT's iterated fundamental-circuit swaps
  are bypassed by partition-count / rank-count comparisons through the
  Phase 19 `def(G̃) = corank M(G̃)` bridge. The forest-surgery core
  (KT 4.1/4.2) is off the Theorem-4.9 critical path. `Molecular/Induction.lean`;
  chapter `molecular-induction.tex`. See `notes/Phase20.md` and
  `notes/MolecularConjecture.md`.
* **Phase 21 (complete, GREEN-modulo-21b)** — stratum 5 of the molecular
  program: the **algebraic induction** (Katoh–Tanigawa §5, §6.1–6.3),
  which realizes the Phase 20 combinatorial reduction at the
  rigidity-matrix rank. The phase lands KT **Theorem 5.5** (every minimal
  `k`-dof-graph `G` with `|V| ≥ 2` has a panel-hinge realization with
  `rank R(G,p) = D(|V|−1) − k`) and discharges its base case (`|V|=2`, via
  the Phase 18 parallel-hinges Lemma 5.3), **Case I** (a proper rigid
  subgraph — rigid-subgraph contraction + block-triangular gluing through
  the Phase 18 pin-a-body Lemma 5.1), **Case II** (`k>0`, splitting off a
  reducible degree-2 vertex — the panel-hinge analogue of Whiteley's
  bar-joint 1-extension), and the analytic half of KT **Proposition 1.1**
  (`rank R(G,p) = D(|V|−1) − def(G̃)`, the rank/deficiency reconciliation;
  matroidal half green from Phase 19). The induction is driven by the same
  reduction dichotomy as Theorem 4.9 (`Graph.minimal_kdof_reduction`). The
  shared analytic device — the genericity argument (Claim 6.4/6.9) — is
  scoped out into its own focused sub-phase **21b** and enters each
  consuming node as an explicit hypothesis, so the surrounding reductions
  are fully formal modulo that one device. The panel layer
  (`PanelHingeFramework`, hinge-coplanarity) is green, as are all four
  Lean pieces of the cycle-realization Lemma 5.4 (Crapo–Whiteley 1982).
  The crux **Case III** (`k=0`, no proper rigid subgraph) is deferred to
  Phases 22–23. Forward-mode; the chapter `algebraic-induction.tex` is the
  authoritative dep-graph. `Molecular/AlgebraicInduction.lean`. See
  `notes/Phase21.md` and `notes/MolecularConjecture.md`.
* **Phase 21b (in progress)** — the genericity device (Claim 6.4/6.9): the
  panel-coordinate parametrization of `R(G,p)` plus the generic-max-rank
  argument, the shared analytic crux of Cases I/II, Theorem 5.5,
  Proposition 1.1, and the cycle assembly. Discharges the black-box left
  cited by Phase 21; also consumed by Phases 22–23. The analytic sibling
  of the Phase-21a meet sub-phase. See `notes/Phase21b.md` and
  `notes/MolecularConjecture.md`.

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
