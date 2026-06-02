# Combinatorial Rigidity — Roadmap

This directory aims to formalize a slice of **combinatorial rigidity theory**
in mathlib style, culminating in **Laman's theorem** (1970): a graph on
`n ≥ 2` vertices is generically rigid in the plane iff it contains a
spanning subgraph with `2n − 3` edges in which every subgraph on `k ≥ 2`
vertices has at most `2k − 3` edges. Such graphs are called *Laman graphs*
or *minimally rigid* graphs in the plane.

The work is expected to span multiple sessions. This file is the canonical
hand-off document: it carries the directory layout, status, mathematical
plan, and engineering conventions. Read it after `CLAUDE.md`.

> **Agents:** start with `CLAUDE.md` (the agent operating manual covering
> reading order, per-session workflow, friction review, and the
> `notes/PhaseN.md` template). This file is the *what*; CLAUDE.md is the
> *how*.
>
> Design rationale (why these choices and not others) lives in
> `DESIGN.md`. Open it only when you actually need to question a
> decision; otherwise this file is sufficient.

## Directory layout

```
<repo root>/
├── CLAUDE.md            agent operating manual — must-read first every session
├── ROADMAP.md           this file — directory layout, status, plan, conventions
├── DESIGN.md            rationale for cross-cutting design choices
├── TACTICS-GOLF.md      golf reference: grind, ncard, mirror rule, fun_prop
├── TACTICS-QUIRKS.md    rescue reference: subst, simp residuals, dot notation
├── notes/               per-phase work logs + cross-cutting logs
│   ├── PhaseN.md        lemma checklist + decisions + hand-off for Phase N
│   ├── FRICTION.md      long-running API/tactic friction log
│   └── PERFORMANCE.md   build-time + profiling notes — read before a perf pass
├── CombinatorialRigidity.lean   top-level entry point (imports LamanTheorem)
├── CombinatorialRigidity/       all Lean sources live here
│   ├── Mathlib/         mirror for upstream-eligible lemmas (see DESIGN.md)
│   │   └── …/           each file mirrors its eventual upstream path
│   ├── Search/
│   │   └── DFS.lean    Phase 9 — verified-iterative DFS warmup (`reachableFinding`); Phase 11 extension — computable reachability closure (`reachClosureComputable`)
│   ├── EdgesIn.lean     Phase 1 — `edgesIn` selector
│   ├── Sparsity.lean    Phase 1 — `IsSparse`, `IsTight`
│   ├── SparsityIComponents.lean  Phase 7 — matroidal-regime maximal I-blocks (split off Sparsity in Phase 8-perf)
│   ├── Laman.lean       Phase 1+2 — `IsLaman` and downstream
│   ├── Henneberg.lean   Phase 3 — `typeI`, `typeII` and forward Laman preservation
│   ├── HennebergReverse.lean  Phase 3+7 — iso constructors + flat-form reverse decomposition (split off Henneberg in Phase 8-perf)
│   ├── Framework.lean   Phase 4 — frameworks, rigidity map
│   ├── TrivialMotions.lean  Phase 6 — d-general translations + infinitesimal rotations
│   ├── HennebergRigidity.lean  Phase 5 milestone 2 — per-move rigidity preservation
│   ├── RigidityMatroid.lean  Phase 6 — row-independence, basis-pick, sparsity bridge
│   ├── LamanTheorem.lean  Phase 5+6 — Laman's theorem (both directions)
│   ├── CountMatroid.lean  Phase 7 — abstract (k, ℓ)-count matroid (ℓ < 2k)
│   ├── MatroidIdentification.lean  Phase 7 — Lovász–Yemini hard direction + rigidity matroid
│   ├── LinearRigidityMatroid.lean  Phase 8 — linear-matroid framing via `Matroid.ofFun`
│   ├── PebbleGame/
│       ├── Basic.lean       Phase 9 — `PartialOrientation` state + invariants
│       ├── Algorithm.lean   Phase 9 — `tryReachPebble` / `tryAddEdge` / `runPebbleGame` chain
│       ├── Correctness.lean Phase 9 — soundness + completeness + matroidal corollary
│       ├── Exec.lean        Phase 10 (planning) — `runPebbleGameExec` + `Decidable` instances
│       └── Examples.lean    Phase 10 (planning) — `#eval` examples on `Fin n` graphs
│   ├── Matroid/         Phase 12 — local mirror of `apnelson1/Matroid` submodular + union (ported, Apache-2.0)
│   └── BodyBar/         Phases 13–15 (planning) — Graph-native sparsity, k-frame matroid, body-bar frameworks + Tay
├── Main.lean            Phase 10 (planning) — `lake exe pebble-game` CLI entry point
├── lakefile.toml        Lake build config; depends on mathlib4
├── lean-toolchain       pinned Lean version (matches mathlib4)
└── lake-manifest.json   resolved dependency revisions
```

The project was previously developed at `Archive/CombinatorialRigidity/` inside
the mathlib4 tree and lifted to this standalone repository; references to
`Archive/CombinatorialRigidity/<path>` in older commit messages and docs map
to `<path>` here (with Lean sources rehomed under `CombinatorialRigidity/`).

## Status

| Phase | File(s) | Status |
|---|---|---|
| 1. Sparsity | `EdgesIn.lean`, `Sparsity.lean`, `Laman.lean` | ✓ Complete (see `notes/Phase1.md`) |
| 2. Laman graphs | `Laman.lean` | ✓ Complete (see `notes/Phase2.md`) |
| 3. Henneberg moves | `Henneberg.lean` | ✓ Complete (see `notes/Phase3.md`) |
| 4. Frameworks | `Framework.lean` | ✓ Complete (see `notes/Phase4.md`) |
| 5. Laman's theorem (⇐) | `LamanTheorem.lean`, `HennebergRigidity.lean` | ✓ Complete (see `notes/Phase5.md`) |
| 6. Laman's theorem (⇒) | `LamanTheorem.lean`, `RigidityMatroid.lean` | ✓ Complete (see `notes/Phase6.md`) |
| 7. Lovász–Yemini matroid identification | `CountMatroid.lean`, `MatroidIdentification.lean` | ✓ Complete (see `notes/Phase7.md`) |
| ⋮ Cleanup round (pre-Phase-8) | project-wide | ✓ Complete (see `notes/Phase7-cleanup.md`; round manual: `CLEANUP.md`) |
| 8. Linear-matroid framing | `LinearRigidityMatroid.lean` | ✓ Complete (see `notes/Phase8.md`) |
| ⋮ Cleanup round (post-Phase-8) | project-wide (light scope) + import-structure audit | ✓ Complete (see `notes/Phase8-cleanup.md`; round manual: `CLEANUP.md`) |
| ⋮ Perf pass (post-Phase-8) | `Sparsity` / `Henneberg` splits + module-system conversion | ✓ Complete (see `notes/Phase8-perf.md`; protocol: `notes/PERFORMANCE.md`) |
| ⋮ Pre-Phase-9 DFS warmup | `Search/DFS.lean` | ✓ Complete (see `notes/Phase9.md` §"DFS warmup (pre-Phase-9)") |
| 9. Pebble game | `PebbleGame/{Basic, Algorithm, Correctness}.lean` | ✓ Complete (see `notes/Phase9.md`) |
| ⋮ Cleanup round (post-Phase-9) | project-wide (Phase 9 surface) | ✓ Complete (see `notes/Phase9-cleanup.md`; round manual: `CLEANUP.md`) |
| ⋮ Perf pass (post-Phase-9) | `Search/DFS.lean` + `PebbleGame.lean` per-decl `@[expose]` audit | ✓ Complete (see `notes/Phase9-perf.md`; protocol: `notes/PERFORMANCE.md`) |
| 10. Executable pebble game | `PebbleGame/{Exec, Examples}.lean`, `Main.lean` | ✓ Complete (see `notes/Phase10.md`) |
| 11. Witness extraction | `Search/DFS.lean`, `PebbleGame/{Basic,Algorithm,Correctness,Exec}.lean`, `Main.lean` | ✓ Complete (see `notes/Phase11.md`) |
| ⋮ Cleanup round (post-Phase-10+11) | Phase 10+11 surface (`PebbleGame/`, `Search/DFS.lean`, `Main.lean`, three blueprint chapters) | ✓ Complete (see `notes/Phase11-cleanup.md`; round manual: `CLEANUP.md`) |
| ⋮ Perf pass (post-Phase-10+11) | Phase 10+11 surface — per-decl `@[expose]` audit on the four new/reshaped files + Phase-11-reshape re-audit on `Basic`/`DFS` + baseline | ✓ Complete (see `notes/Phase11-perf.md`; protocol: `notes/PERFORMANCE.md`) |
| 12. Matroid foundations (submodular + union) | `CombinatorialRigidity/Matroid/` | ✓ Complete (see `notes/Phase12.md`) |
| ⋮ Cleanup round (post-Phase-12) | Phase 12 surface (`Matroid/Constructions/{Submodular,Union}.lean`, `matroid-union.tex`) | ✓ Complete (see `notes/Phase12-cleanup.md`; round manual: `CLEANUP.md`) |
| 13. Tutte–Nash-Williams tree-packing | `BodyBar/TreePacking.lean` | in progress (see `notes/Phase13.md`) |
| 14. k-frame matroid = k-fold cycle union | `BodyBar/KFrame.lean` | planning (scoped in `body-bar.tex`) |
| 15. Body-bar Tay theorem | `BodyBar/{Framework,TayTheorem}.lean` | planning (was Phase 12; see `notes/Phase12.md`) |

Phase-level details (per-phase lemma checklists, decisions made during
that phase, hand-off notes) live under `notes/PhaseN.md`. Read those
when picking up a phase or reviewing how an earlier phase was finished.

**Cleanup rounds** between phases get their own work log under
`notes/PhaseN-cleanup.md` (named to sort next to the prior phase's
notes) and a row in this table for visibility. Round-level discipline
lives in `CLEANUP.md` at the repo root.

Add lemmas in the file that introduces the relevant definition; a
lemma about `IsSparse` belongs in `Sparsity.lean`, not in `Laman.lean`,
even if it is first used there. When starting a new phase, create the
corresponding `notes/PhaseN.md` file in your first commit.

## Mathematical roadmap

We follow the **Henneberg construction** route, which is elementary and
matches mathlib's combinatorics style. The matroid-theoretic route via
`Mathlib.Combinatorics.Matroid` is left as a future alternative framing.

### Phase 1 — Sparsity (`EdgesIn.lean`, `Sparsity.lean`, `Laman.lean`)

Complete. Defines `edgesIn`, `IsSparse`, `IsTight`, `IsLaman` and the
basic API (monotonicity, subgraph preservation, global edge bound,
vertex partition). See `notes/Phase1.md` for the full lemma list and
phase-specific decisions.

### Phase 2 — Laman graphs (`Laman.lean`)

Complete. Builds the Laman API on top of the Phase 1 `IsLaman`
definition: the `(2, 3)`-tightness `iff` unfolding, the K₂ base case
(promoted to a named theorem), and the degree results that feed into
the Henneberg induction (minimum degree ≥ 2 for `n ≥ 3`; existence of
a degree-2-or-3 vertex). See `notes/Phase2.md` for the full lemma list
and phase-specific decisions.

### Phase 3 — Henneberg moves (`Henneberg.lean`)

Complete. Type I and Type II moves on simple graphs (fresh vertex as
`none : Option V`, old vertices via `some`). Both moves preserve the
Laman property (`typeI_isLaman`, `typeII_isLaman`); both edge-set
decompositions land (`typeI_edgeSet[_ncard]`, `typeII_edgeSet[_ncard]`).
Iso transport (`IsSparse.iso`, `IsTight.iso`, `IsLaman.iso`, plus
`Iso.image_edgesIn`) lifts Laman across graph isomorphisms. The
`K₄ \ e` worked example (`top_fin_four_minus_edge_isLaman`) ties
these together. The canonical iso constructors
`typeI_iso_of_two_neighbors` and `typeII_iso_of_three_neighbors`
package the iso `G ≃g typeI G' a b` (resp. `…typeII…`) from
neighborhood data at a chosen vertex; downstream phases consume these
to bridge flat-form reverse decompositions with operation-form forward
preservation theorems.

The structural decomposition theorem
(`IsLaman.exists_typeI_or_typeII_reverse`, now in flat form per Phase 7
Commit 6) lives in `Henneberg.lean`. Phase 3 originally shipped only
the iso-only half (no `G'.IsLaman` claim) because the typeII reverse
can fail for an arbitrary non-adjacent pair (concrete 6-vertex
counter-example in `notes/Phase3.md`); the strengthened claim with
`G'.IsLaman` was deferred to Phase 5 — see §5 below — and re-presented
in flat form in Phase 7.

See `notes/Phase3.md` for the full lemma list and phase-specific
decisions.

Both moves additionally preserve generic rigidity (TODO in Phase 5,
because the proof needs the typeII reverse blocker argument).

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Complete. Defines `Framework V d` as `V → EuclideanSpace ℝ (Fin d)`,
the `RigidityMap G p` as an `ℝ`-linear map (the matrix view via
`LinearMap.toMatrix` is deferred until needed), `IsInfinitesimallyRigid
G p` as the kernel-dimension bound `dim ker ≤ d(d+1)/2`, and
`IsGenericallyRigid G d` as existence of an infinitesimally rigid
placement. Ships the basic `RigidityMap` API (`Framework.finrank`,
`rigidityMap_apply`, `rigidityMap_ker_mono`,
`rigidityMap_finrank_range_le`), the graph-monotonicity corollaries
(`IsInfinitesimallyRigid.mono`, `IsGenericallyRigid.mono`), the main
edge-count theorem `IsGenericallyRigid.card_mul_le` (`d * #V ≤ #E +
d(d+1)/2` for any generically rigid graph), and the K₂ worked example
`top_fin_two_isGenericallyRigid`. The `TrivialMotions` API (textbook
identification of kernel with rigid motions) and the
`finrank_trivialMotions_eq_of_affinelySpanning` lemma were deferred
in Phase 4 (neither was on the critical path for Phase 5) and landed
in Phase 6's `TrivialMotions.lean`. See `notes/Phase4.md` for the full
lemma list and phase-specific decisions.

### Phase 5 — Laman's theorem, (⇐) direction (`LamanTheorem.lean`, `HennebergRigidity.lean`)

Complete. The main iff statement lives in `LamanTheorem.lean`:
```
theorem SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```
*composed* from two named directional theorems —
`IsLaman.isGenericallyRigid_two` for (⇐), proved in Phase 5, and
`IsGenericallyRigid.exists_isLaman_le` for (⇒), `sorry`-blocked and
resolved in **Phase 6** (see §6 below).

**(⇐) recap.** Henneberg induction on `Fintype.card V`. K₂ base case
via `top_fin_two_isGenericallyRigidInj 1` + iso transport. Inductive
step via `IsLaman.exists_typeI_or_typeII_reverse` (strengthened
decomposition with `G'.IsLaman`, proved via the Henneberg blocker
argument) plus per-move rigidity preservation
(`typeI_isGenericallyRigidInj_two` /
`typeII_isGenericallyRigidInj_two`, both unconditional). The Type II
move's collinearity gap is discharged by `IsInfinitesimallyRigid.
eventually` (openness of IR via `LinearIndependent.eventually`) plus
a perpendicular perturbation packaged in
`exists_nonCollinear_rigid_placement_dim_two`. See `notes/Phase5.md`
for the full lemma list and proof techniques.

**Open refactor proposal** (not a blocker): the three contradiction
templates in the milestone-1 blocker argument
(`IsLaman.contradiction_{one,two,three}_pair`) plus the degree-3
dispatcher can be unified through two reusable `(k, ℓ)`-shaped
primitives, saving ~210 LoC. Full plan in `notes/Phase5.md`'s
appendix.

### Phase 6 — Laman's theorem, (⇒) direction (`LamanTheorem.lean`, `RigidityMatroid.lean`)

Complete. Builds the rigidity-matroid scaffolding in `RigidityMatroid.lean`
(row-independence, dual-module bridge, rank lower bound at generic
placement, rank upper bound at affinely-spanning placement, basis-pick),
then ships Lovász–Yemini's easy direction in dim 2:
`isSparse_of_edgeSetRowIndependent_dim_two` (row-independent edge sets
yield `(2, 3)`-sparse spanning subgraphs) and the assembly
`IsGenericallyRigid.exists_isLaman_le` (combine the affinely-spanning
rigid placement, basis-pick, and sparsity). The iff
`isGenericallyRigid_two_iff_exists_isLaman_le` in `LamanTheorem.lean`
now closes both directions. Phase 4 deliberately kept `Framework.lean`
matroid-agnostic (see DESIGN.md *Notion- and matroid-agnostic core*);
Phase 6 stood up `RigidityMatroid.lean` on top without packaging the
abstract `Matroid` instance, since the easy direction needs only the
row-independence relation and two linear-algebra facts.

The chapter ran in **forward blueprint mode** per `blueprint/DESIGN.md`
*Recommendation for Phase 6*: the blueprint chapter
`blueprint/src/chapter/laman-theorem.tex` (its $\Rightarrow$ subsection)
served as the authoritative dep-graph and lemma index throughout. See
`notes/Phase6.md` for the full lemma list and phase-specific decisions.

### Phase 7 — Lovász–Yemini matroid identification (`CountMatroid.lean`, `MatroidIdentification.lean`)

Complete. Phase 6 shipped the easy direction of Lovász–Yemini in dim 2
(row-independent $\Rightarrow$ $(2, 3)$-sparse). Phase 7 shipped the
converse, the general $(k, \ell)$-count matroid in the matroidal regime
$\ell < 2k$ (Whiteley 1996, Lee--Streinu 2008), and the planar
rigidity-matroid specialisation. Hard-direction induction lives in
`MatroidIdentification.lean` and routes through the matroidal-regime
$I$-component scaffolding in `Sparsity.lean` (`IsSparse.maxBlock` and
edge-disjointness); the abstract `(k, \ell)`-count matroid sits in its
own file `CountMatroid.lean` via `IndepMatroid.ofFinite`. The phase ran
in **forward blueprint mode** with `blueprint/src/chapter/count-matroid.tex`
and `blueprint/src/chapter/rigidity-matroid.tex` as the authoritative
dep-graphs and lemma indices. See `notes/Phase7.md` for the full lemma
list and phase-specific decisions.

The **linear-matroid framing** of the rigidity matroid (the
generic-placement matroid $M_p$ on $E(K_V)$ via `Matroid.ofFun` for
some generic $p$, with Lovász--Yemini stated as a matroid iso
$M_{p_{\text{gen}}} \cong \mathrm{rigidityMatroid}\,V$) is deferred to
**Phase 8**, which will add `apnelson1/Matroid` as a dependency.

### Phase 8 — Linear-matroid framing (`LinearRigidityMatroid.lean`)

Complete. Packages the planar rigidity matroid in its linear-algebra
form via `Matroid.ofFun` (from the `apnelson1/Matroid` library) of
the rigidity-row function at a uniformly-generic placement, and
identifies it with the combinatorial $(2, 3)$-count matroid of
Phase 7 (Lovász--Yemini, linear-matroid form). The target
`linearRigidityMatroid_eq_rigidityMatroid` is package equality on
`Matroid (Sym2 V)`, since both matroids share ground set
$E(K_V)$; the content is uniform genericity
(`exists_uniform_rowIndependent_placement_dim_two`), proved by
linear-interpolation perturbation on the finite family of
$(2, 3)$-sparse subsets routed through two new mirror lemmas under
`Mathlib/LinearAlgebra/Matrix/Rank.lean` (rectangular Gram-det
characterization of LI; cofiniteness of LI along an affine line via
a one-variable real polynomial Gram determinant). The chapter ran in **forward
blueprint mode** with `blueprint/src/chapter/rigidity-matroid.tex`'s
*Linear-matroid framing* subsection as the authoritative dep-graph.
See `notes/Phase8.md` for the full lemma list, decisions, and
hand-off.

### Phase 9 — Pebble game (`PebbleGame/{Basic, Algorithm, Correctness}.lean`)

Complete. Formalizes the basic $(k, \ell)$-pebble game of
Lee--Streinu 2008 (generalising the original $(2, 3)$ algorithm of
Jacobs--Hendrickson 1997) end-to-end in the matroidal regime
$\ell < 2k$ matching Phase 7. The pebble game lives in a
`PebbleGame/` subdirectory split three ways post-Phase-9-perf
(see `notes/PERFORMANCE.md` *Split candidates ranked by leverage*
item 5 for the file-size-driven split rationale):
`PebbleGame/Basic.lean` carries state + invariants;
`PebbleGame/Algorithm.lean` the three-layer algorithm chain;
`PebbleGame/Correctness.lean` the correctness theorems and the
matroidal-independence corollary. The chapter ships the
`PartialOrientation V` state (bundled `Finset (V × V)` with
`no_loops` + `no_antiparallel`), the path-reversal and arc-insertion
moves with per-vertex and subset-level accounting lemmas, the
`Reachable k ℓ` inductive predicate packaging the algorithmic
state space, the four pebble-game invariants of L-S Lemma 10
(`Reachable.{out_le, peb_add_out_eq, pebOn_add_span_add_outOn,
pebOn_add_outOn_ge, span_add_le}`), and the three-layer algorithm
chain `tryReachPebbleWith → tryAddEdgeWith → runPebbleGameWith`
(each as a fully-computable workhorse with a thin noncomputable
math-layer wrapper specialising to `D.outList` / `G.edgeFinset`
enumeration). The certificate-form correctness theorem
`runPebbleGame_correct` (`G.IsSparse k ℓ ↔ ∃ D, runPebbleGame G k ℓ
= some D`) combines soundness `runPebbleGame_sound` (via the
`span_eq_ncard_edgesIn` bridge identity under
`runPebbleGame_underline_eq_edgeFinset`) with completeness
`runPebbleGame_eq_none_imp_exists_witness` (per-edge failure-witness
extraction routed through Lemma 13 algebraic core
`Reachable.independent_brings_pebble` and its SimpleGraph-form
wrapper). The matroidal-independence corollary
`SimpleGraph.countMatroid_indep_iff_runPebbleGame` follows as a
three-`rw` composition with Phase 7's `countMatroid_indep_iff`. A
pre-phase **DFS warmup** under `Search/DFS.lean` (modelled on
`Batteries.UnionFind`'s `termination_by` pattern) exercised the
verified-iterative-graph-search idiom in isolation; it ships the
`DirectedWalk` inductive, the `reachableFinding` primitive with
correctness theorem (soundness + completeness via
`DirectedWalk.dropUntilBundle` truncation), and the abstract
`reachClosure` over `Relation.ReflTransGen`. The chapter ran in
**forward blueprint mode** with
`blueprint/src/chapter/pebble-game.tex` as the authoritative
dep-graph. See `notes/Phase9.md` for the full lemma list,
decisions, and hand-off; the *component pebble game* (L-S §5,
$O(n^2)$ speedup via union pair-find) and the Henneberg-sequence
application (L-S §6) are deferred to potential follow-up phases.

### Phase 10 — Executable pebble game (`PebbleGame/{Exec, Examples}.lean`, `Main.lean`)

Complete. Bridges Phase 9's `noncomputable` `runPebbleGame` to an
actually-runnable decision procedure: the computable wrapper
`runPebbleGameExec` plugs `Finset.sort`-based list views (via
`outListSorted` for out-neighbour lists and `edgeListSorted` for
edges via the `Lex (V × V)` projection of `Sym2`) under
`[LinearOrder V]` into Phase 9's `-With` workhorses, lifts the
certificate-form correctness theorem to a workhorse-level
restatement that both the math-layer `runPebbleGame` and the new
`runPebbleGameExec` derive from as one-line corollaries, registers
the canonical `Decidable` instances for `IsSparse k ℓ` / `IsTight`
/ `IsLaman` (in the matroidal regime $\ell < 2k$, with a top-level
`Fact (3 < 2 * 2)` making the Laman case zero-hypothesis), and
ships a `lake exe pebble-game` CLI binary that reads an edge-list
file and prints `LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`. Both
`#eval (decide G.IsLaman)` and the CLI reduce through the same
compiled `runPebbleGameExec` body. Chapter ran in **forward
blueprint mode** with `blueprint/src/chapter/executable.tex` as
the authoritative dep-graph. See `notes/Phase10.md` for the full
layer-by-layer summary and the architectural-choice list. The
blocking-witness extraction at the CLI's failure branch (which
also blocks an analogous orientation-witness extraction on the
success branch) was deferred during Layer 5 and is the focus of
**Phase 11** below.

### Phase 11 — Witness extraction (`Search/DFS.lean`, `PebbleGame/{Basic,Algorithm,Correctness,Exec}.lean`, `Main.lean`)

Complete. **Structural-edit phase** that maximally reshaped Phase
9/10's $\mathrm{Option}$-shaped pebble-game algorithms into the
verdict-bearing inductive `PebbleGameResult G k ℓ`, whose `.accept`
constructor carries the partial orientation $D$ and whose `.reject`
constructor carries the blocking subset $V'$. The workhorse-level
`tryAddEdgeWith` / `runPebbleGameWith` mirror-reshaped to
`Sum (WorkhorseWitness k ℓ V) (PartialOrientation V)`, with the
`independent_brings_pebble`-driven failure witness constructed
inline at case5 of `tryAddEdgeWith`'s recursion; Phase 9's
existence chain (`_isSome` / `_eq_none_imp_exists_witness`) is
absorbed and the certificate-form correctness theorems collapse
into the verdict's type. Phase 10's three `Decidable` instances
re-route through `.isAccept`; Phase 7's
`countMatroid_indep_iff_runPebbleGame` restates against the verdict.
The substantive prerequisite — a verified-iterative *computable*
`reachClosureComputable` in `Search/DFS.lean` — lands as Layer 1
and replaces the previous `Classical.decPred`-mediated reach
closure on `PartialOrientation`. Layer 5 bumps the CLI surface to
pattern-match on the verdict and emit `ARCS u v` / `BLOCKING n` +
`VERTEX w` lines alongside the trichotomy label, making the
classification externally checkable. The chapter ran in
**structural-edit mode** per `blueprint/DESIGN.md`: no new
blueprint chapter, with reshape lands distributed across
`chapter/{dfs,pebble-game,executable}.tex` alongside each Layer's
Lean. See `notes/Phase11.md` for the five-layer plan, the Layer 0
audit outcomes, architectural-choice list, and per-layer decision
records.

The body-bar program (Tay's theorem and beyond) was re-scoped from a
single blocked "Phase 12" into a dependency-ordered chain of four
phases (12–15) after a 2026-06 re-investigation. The matroid-union
machinery the original plan intended to *vendor* from `apnelson1/Matroid`
turned out to be already fully formalized there (zero-sorry) but
bit-rotted onto a superseded circuit-axiom constructor — so it is
promoted from an assumed-vendored "Layer 1" into a real local
formalization phase. See `notes/Phase12.md` *Prerequisites audit* for
the corrected analysis.

### Phase 12 — Matroid foundations: submodular functions & matroid union

Complete. Formalizes the abstract-matroid prerequisites of the body-bar
route, **locally** under `CombinatorialRigidity/Matroid/`: the
matroid-from-submodular-function construction and polymatroid rank formula
(Edmonds 1970), the matroid-union theorem (Nash-Williams 1966 / Edmonds)
with its independence characterization, Rado's theorem (Rado 1942), and
Edmonds' matroid-partition rank formula (Edmonds 1965). The Lean is
**ported from Peter Nelson's `apnelson1/Matroid`** (Apache-2.0), whose
shelved `WIP/{Submodular,Union}.lean` carry complete proofs, rebased onto
the package's live `FiniteCircuitMatroid` constructor — an explicit
exception to the "small upstream-eligible lemmas only" mirror convention
(see `DESIGN.md` *Local mirror of the matroid-union subsystem*). The phase
ran route (a), submodular-repair, chosen by the Layer-1 spike, in **forward
blueprint mode** with `blueprint/src/chapter/matroid-union.tex` as the
authoritative dep-graph. See `notes/Phase12.md` for the Layer plan, the
prerequisites audit, the per-layer decision records, and the attribution
discipline.

### Phase 13 — Tutte–Nash-Williams tree-packing

**Status (in progress; see `notes/Phase13.md`).** Specializes the
matroid-partition theorem to `k` copies of `Graph.cycleMatroid`,
recovering Tutte–Nash-Williams tree-packing (Tutte 1961, Nash-Williams
1961): a multigraph is the edge-disjoint union of `k` forests iff it is
`(k,k)`-sparse, with the spanning-tree refinement under tightness.
Introduces a `Graph`-native `(k,ℓ)`-sparsity/tightness predicate (fresh,
**not** migrated from the Phase 9/10 `SimpleGraph` sparsity — see
`DESIGN.md` *Migrating Phases 1–11 …*). Carrier: mathlib core `Graph α β`.

Define that sparsity predicate **`Set`-side** (`Set.ncard` of edge sets,
`ℕ`, `[Finite]`) so it lines up with both the Phases-1–11 convention and
the Phase-12 matroid layer in one conversion step, and **open the phase
with a thin rank adapter** restating Phase 12's partition theorem in
`Set`-`Y`/`ℕ`/`ncard` idiom for the `k`-fold `cycleMatroid` case — the
exported `matroid_partition'` is `Finset`/`ℕ`/`[Fintype]`-flavored and
`matroid_partition_eRk'` is `Set`/`ℕ∞`/`[Finite]`, so the adapter
absorbs the `rk`/`eRk`/`ncard` + typeclass plumbing once. Full rationale:
`DESIGN.md` *Set/Finset and rank-flavor boundary at the matroid layer
(Phases 13–15)*.

### Phase 14 — k-frame matroid = k-fold cycle-matroid union

**Status (planning; scoped in `body-bar.tex`).** Whiteley 1988
Theorem 1: the generic `k`-frame matroid `F(G,X)` on a multigraph (a
linear matroid via `Matroid.ofFun` over indeterminate coefficients)
equals the `k`-fold union of `Graph.cycleMatroid`. Column-reorder /
monomial argument from Whiteley §2.1. Bridges Phase 12's abstract union
to the body-bar realizations of Phase 15.

### Phase 15 — Body-bar Tay theorem (existence form)

**Status (planning; scoped in `body-bar.tex`).** The original Phase-12
target. For `n ≥ 2` and `d = n(n+1)/2`, a multigraph `G` on `b` bodies
admits an infinitesimally rigid independent body-bar framework in `Rⁿ`
iff `|E| = d(b−1)` with `|E'| ≤ d|V'| − d` on every sub-multigraph;
equivalently (Phase 13) iff `G` is the edge-disjoint union of `d`
spanning trees. Whiteley's matroid-union route (Whiteley 1988):
specialize the indeterminate row coefficients to standard-basis Plücker
coordinates of two-extensors.

Architectural decisions (migrated from the old Phase-12 notes):
- **Carrier = mathlib's core `Graph α β`** (`Mathlib/Combinatorics/
  Graph/Basic.lean`), on which `apnelson1/Matroid`'s `cycleMatroid`
  sits; Phases 1–11 stay on `SimpleGraph` (the correct carrier for
  bar-joint rigidity). See `DESIGN.md` *Migrating Phases 1–11 …* for
  the refactor-risk assessment.
- **Plücker / two-extensor coordinates handled inline**, standard-basis
  specialization only — no separate phase, no irreducible-variety
  infrastructure.
- **Existence-of-realization form only.** Whiteley's "almost all
  realizations are rigid" lift (Proposition 6, irreducible-variety
  machinery) is **deferred**, re-assessed when the body-hinge phase
  opens.
- **Graph-level defs under `namespace Graph`** (dot-notation on
  `G : Graph α β`, beside `Graph.cycleMatroid`); framework defs under
  `CombinatorialRigidity` / `BodyBar`. Departs from the "everything
  under `SimpleGraph`/`CombinatorialRigidity`" convention (Phases
  13–15).

The natural follow-on is **Phase 16** (body-hinge / panel-hinge
Tay–Whiteley) en route to a longer-horizon **Phase 17** target — the
**molecular conjecture** (Katoh–Tanigawa 2011).

## Engineering conventions

- **Namespace.** Everything sits inside `SimpleGraph` or
  `CombinatorialRigidity`. No top-level identifiers. **Exception
  (Phases 12–15):** the body-bar program adds `Matroid`-namespace defs
  (the ported submodular/union machinery, beside `Matroid.cycleMatroid`)
  and `Graph`-namespace defs (graph-level `kFrameMatroid` / sparsity, for
  dot-notation on `G : Graph α β`); framework defs stay under
  `CombinatorialRigidity`/`BodyBar`. See `notes/Phase12.md` and
  ROADMAP §15.
- **Vertex types.** Use `V : Type*` and `[Finite V]` (the weakest
  reasonable typeclass) in signatures whenever the *statement* works
  at that strength — this is the strongest mathematical claim, the
  one that applies most generally. When a proof body needs
  `Fintype V`-strength data (e.g. `Finset.univ`, `Fintype.card V`),
  bridge inline with `haveI : Fintype V := Fintype.ofFinite V`; for
  `Finset V` operations needing `DecidableEq V`, follow with
  `classical`. This is the mathlib idiom (enforced by the
  `unusedFintypeInType` env linter). Use `[Fintype V]` in the
  signature only when the *type* itself mentions `Fintype.card V`,
  `Finset.univ : Finset V`, or similar `Fintype`-flavored objects.
  Edge counts use `Set.ncard` so we don't force decidability of edge
  predicates. See `DESIGN.md` *Typeclass shape for finiteness on `V`*
  for the rationale (Phase 7 cleanup round resolution; two earlier
  iterations were considered and reversed). Algorithm-bearing files
  (`Search/DFS.lean`, `PebbleGame/`) deliberately depart from this
  rule and take `[Fintype V] [DecidableEq V]` end-to-end as a
  localized style island — the state machines iterate over
  `Finset V` / `Finset (V × V)` directly, and `#eval` / `decide`
  must fire on extracted certificates. See `DESIGN.md`
  *Pebble-game style island: `[Fintype V] [DecidableEq V]`* for the
  rationale + the math-layer / exec-layer (`-With`) split that keeps
  the island from contaminating the rest of the project's API.
- **Cardinalities.** Use `Set.ncard` for sets and `Finset.card` for finsets.
  Avoid `ℕ`-subtraction; rephrase `a ≤ b − c` as `a + c ≤ b`.
- **Style.** Module docstrings at the top of each file (`/-! # Title -/`).
  One declaration ↔ one purpose. Comments only when *why* is non-obvious.
- **Imports.** Each file imports the minimum it needs. `Sparsity.lean`
  should import only `SimpleGraph.Basic` + `Set.Card` + minor friends.
- **Decidability.** Add `[DecidableEq V]` / `[DecidableRel G.Adj]` only
  when a body genuinely builds specific `Finset V` / `Adj`-iterating
  objects. `classical` at the proof top is the acceptable alternative
  when adding the typeclass to the signature isn't worth the API
  noise. Many definitions can stay noncomputable via `Set.ncard`.
- **Predicates are `def`s, not `abbrev`s.** `IsSparse`, `IsTight`,
  `IsLaman`, and `edgesIn` are non-reducible. `grind` will not unfold
  them on its own. To break an `IsTight`/`IsLaman` goal into parts use
  `refine ⟨?_, ?_⟩`; for an `edgesIn` membership use the corresponding
  `mem_*` simp lemma. See `TACTICS-GOLF.md` § 4 for the full discussion.
- **Missing mathlib lemmas.** If you need a lemma that genuinely
  belongs upstream, put it under `Mathlib/<exact mathlib path>` so
  promotion is later a copy-paste. The directory is created lazily;
  don't pre-populate. See `DESIGN.md` "Mirror directory".
- **Tactic notes.** Practical guidance on `grind` (preferred closing
  tactic in this directory), the `Set.ncard` autoparam pattern, the
  mirror-first rule, and other cross-cutting idioms all live in
  `TACTICS-GOLF.md`. When in doubt, read it — the section TL;DRs are
  short and save iteration time.
- **No prose counts in shared docs.** Don't write "Phase X surfaced
  N upstream candidates" or similar in `ROADMAP.md`, `DESIGN.md`, or
  `TACTICS-GOLF.md` — counts drift the moment a new phase mirrors more
  lemmas. Link to `notes/FRICTION.md` "Mirrored" (or the mirror
  directory listing) as the source of truth instead.

## Working on the project

The per-session workflow (starting / working / friction review at
end-of-session / leave-it-ready-for-the-next-agent), and the
`notes/PhaseN.md` template, live in `CLAUDE.md`. Agents: read that
first.

## References

- G. Laman, *On graphs and rigidity of plane skeletal structures*, J. Engrg.
  Math. **4** (1970), 331–340.
- L. Lovász and Y. Yemini, *On generic rigidity in the plane*, SIAM J.
  Algebraic Discrete Methods **3** (1982), 91–98.
- J. Graver, B. Servatius, H. Servatius, *Combinatorial Rigidity*, AMS GSM 2,
  1993. — main textbook reference.
- T. Jordán, *Combinatorial rigidity: graphs and matroids in the theory of
  rigid frameworks*, MSJ Memoirs, 2016. — modern survey.
- A. Nixon, B. Schulze, W. Whiteley, surveys on rigidity matroids.
- T.-S. Tay, *Rigidity of multi-graphs. I. Linking rigid bodies in n-space*,
  J. Combin. Theory Ser. B **36** (1984), 95–112. — original body-bar
  theorem; Phase 12 target.
- W. Whiteley, *The union of matroids and the rigidity of frameworks*,
  SIAM J. Disc. Math. **1** (1988), 237–255. — matroid-union proof of
  Tay's theorem; the route Phase 12 follows.
