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

Phases 1–22a and the Grassmann–Cayley meet sub-phase 21a are complete and
carry no `sorry`s; **Phase 21** settled the algebraic induction's accounting
layer, and **Phase 21b (complete)** delivered the shared **genericity device**
(Claim 6.4/6.9) — green and axiom-clean — together with the genericity-free
accounting and the `V(G)`-relative count bridges; a math-first feasibility pass
then **re-scoped the realization *producers* of Theorem 5.5 to Phases 22–23**,
where the reducible-vertex split is recognised as Katoh–Tanigawa's Case III and
joins the deferred crux. **Phase 22 (the realization layer) is sub-lettered** —
**22a (Case I realization) complete green-modulo KT Claim 6.4**, delivered via the
**block-triangular reframe** (KT eq. 6.3's rank-addition over one common framework,
routed through the genericity device's independent-row count, not a common-seed
splice) with the single deferred obligation — KT Claim 6.4, the surviving block's
exterior-projected rank at the generic placement — handed to **22b**; **22b+ (Case III
at d=3 + d=3 assembly) parked in planning**. **The body-bar
program (Phases 12–15) lands Tay's theorem**, and **Phase 16
(complete)** extends it to the body-hinge / panel-hinge Tay–Whiteley
theorem — see below. **Phase 17 (complete)** opens the
longer-horizon **molecular-conjecture program** (Phases 17–26;
Katoh–Tanigawa 2011) with its Grassmann–Cayley extensor-algebra layer,
**Phase 18 (complete)** builds the genuine panel-hinge rigidity
matrix `R(G,p)` on top of it, **Phase 19 (complete)** builds the
matroid `M(G̃)`, the `D`-deficiency, and the `k`-dof combinatorics,
**Phase 20 (complete)** develops the combinatorial induction —
graph operations and Katoh–Tanigawa's Theorem 4.9 — and **Phase 21
(complete)** lands the algebraic induction, realizing that reduction
at the rigidity-matrix rank (Theorem 5.5 base, Cases I & II, and the
analytic half of Proposition 1.1).
The main theorem
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

**Phase 16 (complete)** extends this to the **body-hinge /
panel-hinge Tay–Whiteley theorem** (`Graph.BodyHingeFramework.body_hinge_tay`;
Tay 1989, Whiteley 1988), existence-of-realization form, **via the
matroid-union reduction to Phase 15**. A hinge in `ℝⁿ` is an
`(n−2)`-dimensional affine subspace (a pin-joint in 2-space, a
line-hinge in 3-space) that constrains all but one of the
`δ = n(n+1)/2` relative screw freedoms of the two bodies it joins, so
it behaves like a bundle of `δ−1` coincident body-bars. A body-hinge
framework on `G` is therefore the induced body-bar framework on
`(δ−1)·G` (each hinge replaced by `δ−1` parallel bars), and the target
— `G` carries an independent (resp. isostatic) body-hinge framework iff
`(δ−1)·G` is `(δ,δ)`-sparse (resp. tight), equivalently the
edge-disjoint union of `δ` forests — reduces node-for-node to Phase
15's `tay_witness` on `(δ−1)·G`. The `(δ−1)·G` device is the multiplied
graph of the longer-horizon **molecular conjecture** (Katoh–Tanigawa
2011).

**Phase 17 (complete)** opens that longer-horizon target: the
**molecular-conjecture program** (Phases 17–26; Tay–Whiteley, proved by
Katoh–Tanigawa 2011), the project's largest single undertaking. Phase
17 formalizes the **Grassmann–Cayley / extensor-algebra** layer
(Katoh–Tanigawa §2.1) — homogeneous coordinates `p ↦ (p,1)`, extensors
as decomposable elements of `⋀ʲ ℝ^(d+1)`, the join `∨`, Plücker
coordinates, and the affine-subspace extensor `C(·)` — culminating in
**Lemma 2.1**: the `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1`
affinely independent points are linearly independent, the
linear-algebra foundation the conjecture's hardest case bottoms out on.
**Phase 18 (complete)** builds stratum 2: the genuine panel-hinge
rigidity matrix `R(G,p)` (hinge constraints via the supporting
extensors `C(p(e))`, the null space `Z(G,p)` on the degree-`k` graded
screw space `⋀^k ℝ^(k+2)` of dimension `D`, the `D` trivial motions and
the codimension form of `rank ≤ D(|V|−1)`, and the three rank Lemmas
5.1–5.3) — the full rank-form substrate the algebraic induction runs
on. Its reconciliation with Phase 16's reduction-form Prop 1.1 is a
top-of-DAG corollary depending on the analytic generic-rank theorem,
presented with the algebraic induction (Phase 21+). Forward-mode
program, one chapter per phase: `extensor.tex` (Phase 17) and
`rigidity-matrix.tex` (Phase 18) are the authoritative dep-graphs (all
nodes green). See the program-level plan in `notes/MolecularConjecture.md`.

**Phase 19 (complete)** builds stratum 3: the matroidal substrate of
the conjecture's algebraic induction (Katoh–Tanigawa §2.5, §3). The
matroid `M(G̃)` is the `(D,D)`-count matroid of the multiplied graph
`G̃ = (D−1)·G` at the boundary regime `ℓ = 2k = D` — the `D`-fold
graphic-matroid union of Phases 13/14 with Tutte–Nash-Williams, not the
`ℓ<2k` count matroid of Phase 7. The phase builds the `D`-deficiency
`def(G̃)`, the `k`-dof / minimal-`k`-dof hierarchy, rigid subgraphs
(KT Lemmas 3.1/3.3/3.4), and the `def(G̃) = corank M(G̃)` bridge
(Jackson–Jordán 2009 Thm 6.1 / Cor 6.2, proved in-repo axiom-free) —
the matroidal half of the Phase 16 reconciliation. Forward-mode; the
chapter `deficiency.tex` is the authoritative dep-graph (all nodes
green). See `notes/Phase19.md` and `notes/MolecularConjecture.md`.

**Phase 20 (complete)** builds stratum 4: the **combinatorial
induction** of Katoh–Tanigawa's proof (§3.4–3.5, §4). It develops the
graph operations on `Graph α β` — vertex removal, splitting-off
`G_v^{ab}` at a degree-2 vertex, its inverse edge-splitting, and
rigid-subgraph contraction — the degree-of-freedom tracking lemmas
(4.3–4.8), and the capstone **Theorem 4.9**: every minimal `0`-dof-graph
reduces to the two-vertex double edge by splitting-off and rigid-subgraph
contraction, the combinatorial skeleton the algebraic induction of
Phases 21–23 realizes at the rigidity-matrix rank. The formalization
surfaced two route findings — KT Lemma 4.1 (the forest surgery) is
over-quantified with a balanced-packing gloss in its proof (routed
around via a deficiency-count argument), and KT's iterated
fundamental-circuit swaps are bypassed by partition-count / rank-count
comparisons through the `def(G̃) = corank M(G̃)` bridge. The
forest-surgery core (KT 4.1/4.2) is off the Theorem-4.9 critical path.
`Molecular/Induction.lean`; chapter `molecular-induction.tex`. See
`notes/Phase20.md` and `notes/MolecularConjecture.md`.

**Phase 21 (complete — GREEN-modulo-21b)** lands stratum 5: the **algebraic
induction** of Katoh–Tanigawa's proof (§5, §6.1–6.3), which realizes the
Phase 20 combinatorial reduction at the rigidity-matrix rank. The phase
lands KT **Theorem 5.5** — every minimal `k`-dof-graph `G` with
`|V| ≥ 2` has a panel-hinge realization with `rank R(G,p) = D(|V|−1) − k`
— and discharges its base case (`|V|=2`, via the Phase 18 parallel-hinges
Lemma 5.3), **Case I** (a proper rigid subgraph — rigid-subgraph
contraction + block-triangular gluing through the Phase 18 pin-a-body
Lemma 5.1), **Case II** (`k>0`, splitting off a reducible degree-2
vertex — the panel-hinge analogue of Whiteley's bar-joint 1-extension),
and the analytic half of KT **Proposition 1.1**
(`rank R(G,p) = D(|V|−1) − def(G̃)`, the rank/deficiency reconciliation;
matroidal half green from Phase 19). The induction is driven by the same
reduction dichotomy as Theorem 4.9
(`Graph.minimal_kdof_reduction`). The shared analytic device — the
genericity argument (Claim 6.4/6.9) — is scoped out into its own focused
sub-phase **21b** and enters each consuming node as an explicit
hypothesis, so the surrounding reductions are fully formal modulo that one
device. The panel layer and all four Lean pieces of the cycle-realization
Lemma 5.4 (Crapo–Whiteley 1982) are green. The crux **Case III** (`k=0`,
no proper rigid subgraph) is deferred to Phases 22–23. Forward-mode; the
chapter `algebraic-induction.tex` is the authoritative dep-graph.
`Molecular/AlgebraicInduction/`. See `notes/Phase21.md` and
`notes/MolecularConjecture.md`.

**Phase 21b (complete)** delivers the **genericity device** (Claim 6.4/6.9) —
the panel-coordinate generic-max-rank argument that lifts a rank attained at one
realization to a generic one, the shared analytic crux of Cases I/II, Theorem
5.5, Proposition 1.1, and the cycle assembly. It is **green and axiom-clean**,
applied to the varying panel family (the B0 keystone), with the genericity-free
accounting iffs, the `V(G)`-relative count bridges, and the reusable row + glue
infrastructure. A math-first feasibility pass against Katoh–Tanigawa §6.2–6.3
then **re-scoped the realization *producers* of Theorem 5.5 to Phases 22–23**:
the reducible-vertex split producer is KT's Case III (one row short of full rank
for `k=0`, needing the redundant-edge row of Lemma 6.10/6.13), and the rigid-
subgraph splice producer (full-rank but research-shaped boundary-panel geometry)
joins the realization layer.

**Phase 22 (the realization layer) is sub-lettered** — the Theorem-5.5 case
*producers* the genericity device feeds, split into sub-phases because it
over-broadly bundled three independent bodies of work (sub-lettering 22a, 22b, …
keeps the integer phase numbers 23–26 stable). **Phase 22a (complete,
green-modulo-22b)** is the Case I realization — the full-rank rigid-subgraph splice
(Katoh–Tanigawa §6.2); the composer is green-modulo a single dischargeable
hypothesis, KT Claim 6.4, delivered via the block-triangular reframe. **Phase 22b
(planning)** discharges that obligation: KT Claim 6.4 (the surviving block's
exterior-projected rank at the generic placement, §6.2/§5.1), flipping the Case-I
producer fully green. **Phase 22b+ (planning)** parks the rest behind 22b (Claim 6.4
now precedes it; may renumber to 22c+): Case III at `d=3` (the crux Lemma 6.10,
§6.3 + §6.4.1) plus the `d=3` assembly, expected to split into multiple sub-phases
once its shape is clearer. A structural-edit phase extending the algebraic-induction
chapter rather than opening a new one.

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
|    16 | Body-hinge Tay–Whiteley theorem | `BodyBar/BodyHinge.lean` | ✓ |
|    17 | Grassmann–Cayley extensor algebra | `Molecular/Extensor.lean` | ✓ |
|    18 | Panel-hinge rigidity matrix `R(G,p)` | `Molecular/RigidityMatrix.lean` | ✓ |
|    19 | `M(G̃)`, deficiency, `k`-dof graphs | `Molecular/Deficiency.lean` | ✓ |
|    20 | Combinatorial induction → Theorem 4.9 | `Molecular/Induction.lean` | ✓ |
|    21 | Algebraic induction: Thm 5.5 base + Cases I & II (genericity-free core; device cited to 21b) | `Molecular/AlgebraicInduction/` | ✓ |
|   21a | Grassmann–Cayley meet / projective-duality foundations | `Molecular/Meet.lean` | ✓ |
|   21b | Genericity device (Claim 6.4/6.9) + accounting/bridges; realization producers re-scoped to 22–23 | `Molecular/AlgebraicInduction/` (+ `lem:genericity-device`) | ✓ |
|   22a | Case I realization (full-rank rigid-subgraph splice; block-triangular reframe) | `Molecular/Induction.lean` + `AlgebraicInduction/` | ✓ (green-modulo-22b) |
|   22b | KT Claim 6.4 (discharge the Case-I green-modulo obligation; `lem:claim-6-4`) | `Molecular/AlgebraicInduction/CaseI.lean` | ◷ |
|  22b+ | (parked) Case III at `d=3` + `d=3` assembly (Claim 6.4 / 22b precedes it; may renumber to 22c+) | `Molecular/AlgebraicInduction/` | ◷ |

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
