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
│   └── BodyBar/         Phase 13 (✓, `TreePacking.lean`) — Graph-native sparsity + Tutte–Nash-Williams; Phase 14 (✓, `KFrame.lean`) — k-frame matroid; Phase 15 (✓, `{Framework,TayTheorem}.lean`) — body-bar frameworks + Tay; Phase 16 (✓, `BodyHinge.lean`) — body-hinge Tay–Whiteley
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
| 13. Tutte–Nash-Williams tree-packing | `BodyBar/TreePacking.lean` | ✓ Complete (see `notes/Phase13.md`) |
| ⋮ Cleanup round (post-Phase-13) | Phase 13 surface (`BodyBar/TreePacking.lean`, Phase-13 `Matroid/Constructions/Union.lean` adders, `body-bar.tex` tree-packing nodes) | ✓ Complete (see `notes/Phase13-cleanup.md`; round manual: `CLEANUP.md`) |
| 14. k-frame matroid = k-fold cycle union | `BodyBar/KFrame.lean` | ✓ Complete (see `notes/Phase14.md`) |
| ⋮ Cleanup round (post-Phase-14) | Phase 14 surface (`BodyBar/KFrame.lean`, Phase-14 `Mathlib/LinearAlgebra/Matrix/Rank.lean` adders, `body-bar.tex` `sec:body-bar-k-frame` nodes) | ✓ Complete (see `notes/Phase14-cleanup.md`; round manual: `CLEANUP.md`) |
| 15. Body-bar Tay theorem | `BodyBar/{Framework,TayTheorem}.lean` | ✓ Complete (was Phase 12; see `notes/Phase15.md`) |
| ⋮ Cleanup round (post-Phase-15) | Phase 15 surface (`BodyBar/{Framework,TayTheorem}.lean`, `body-bar.tex` `sec:body-bar-framework` + `sec:body-bar-tay` nodes) | ✓ Complete (see `notes/Phase15-cleanup.md`; round manual: `CLEANUP.md`) |
| 16. Body-hinge Tay–Whiteley theorem | `BodyBar/BodyHinge.lean` | ✓ Complete (see `notes/Phase16.md`) |
| ⋮ Cleanup round (post-Phase-16) | Phase 16 surface (`BodyBar/BodyHinge.lean`, `body-hinge.tex` `sec:body-hinge` nodes) | ✓ Complete (see `notes/Phase16-cleanup.md`; round manual: `CLEANUP.md`) |
| 17. Grassmann–Cayley extensor algebra | `Molecular/Extensor.lean` (full §2.1) | ✓ Complete (see `notes/Phase17.md`; opens the 10-phase molecular-conjecture program, `notes/MolecularConjecture.md` + §17 below) |
| ⋮ Cleanup round (post-Phase-17) | Phase 17 surface (`Molecular/Extensor.lean`, `molecular.tex` `sec:molecular` nodes) | ✓ Complete (see `notes/Phase17-cleanup.md`; round manual: `CLEANUP.md`) |
| 18. Panel-hinge rigidity matrix `R(G,p)` | `Molecular/RigidityMatrix.lean` (KT §2.2–2.4 + Lemmas 5.1–5.3) | ✓ Complete (see `notes/Phase18.md`; `molecular.tex` `sec:molecular-rigidity-matrix`) |
| ⋮ Cleanup round (post-Phase-18) | Phase 18 surface (`Molecular/RigidityMatrix.lean`, `molecular.tex` → split into `extensor.tex` + `rigidity-matrix.tex`) + readability/citation/instruction items | ✓ Complete (see `notes/Phase18-cleanup.md`; round manual: `CLEANUP.md`) |
| 19. `M(G̃)`, deficiency, `k`-dof graphs | `Molecular/Deficiency.lean` (KT §2.5, §3) | ✓ Complete (see `notes/Phase19.md`; `deficiency.tex` `sec:molecular-deficiency`) |
| ⋮ Cleanup round (post-Phase-19) | Phase 19 surface (`Molecular/Deficiency.lean`, `deficiency.tex` `sec:molecular-deficiency` nodes) | ✓ Complete (all A–D audits no-op; see `notes/Phase19-cleanup.md`; round manual: `CLEANUP.md`) |
| 20. Combinatorial induction → Theorem 4.9 | `Molecular/Induction/` (KT §3.4–3.5, §4) | ✓ Complete (`thm:minimal-kdof-reduction` green; see `notes/Phase20.md`; `molecular-induction.tex` `sec:molecular-induction`) |
| ⋮ Cleanup round (post-Phase-20) | Phase 20 surface (`Molecular/Induction/`, `molecular-induction.tex` `sec:molecular-induction` nodes) | ✓ Complete (A3 + B3 the two real fixes; A1/A2/B1/B2/B4/C1/D2 no-op; D1 compressed `notes/Phase20.md` 1089→434; see `notes/Phase20-cleanup.md`; round manual: `CLEANUP.md`) |
| 21. Algebraic induction: Thm 5.5 base + Cases I & II | `Molecular/AlgebraicInduction/` (KT §5, §6.1–6.3) | ✓ Complete (green-modulo-21b; see `notes/Phase21.md`) |
| 21a. Grassmann–Cayley meet / projective-duality foundations | `Molecular/Meet.lean` (KT §2.1 dual half) + mirror lemmas | ✓ Complete (see `notes/Phase21a.md`) |
| 21b. Genericity device (Claim 6.4/6.9) | `Molecular/AlgebraicInduction/` + `Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/` (+ `algebraic-induction.tex`) | ✓ Complete (closed 2026-06-04; see `notes/Phase21b.md`) |
| 22a. Case I realization | `Molecular/Deficiency.lean` + `Induction/` + `AlgebraicInduction/` (extends `algebraic-induction.tex`) | ✓ Complete (green-modulo-22b; see `notes/Phase22a.md`) |
| ⋮ Structure pass (pre-Phase-22b) | `Molecular/{AlgebraicInduction,Induction}/` splits + `algebraic-induction.tex` split | ✓ Complete (see `notes/Phase22-structure.md`) |
| 22b. KT Claim 6.4 (discharge the Case-I green-modulo obligation) | `Molecular/AlgebraicInduction/CaseI.lean` (extends `algebraic-induction.tex`) | ✓ Complete (closed 2026-06-05; see `notes/Phase22b.md`) |
| 22c. Case III at `d=3`, stratum 1 (KT Lemma 6.10, the eq. (6.12) `+(D−1)` placement) | `Molecular/AlgebraicInduction/` (extends `algebraic-induction.tex`) | ✓ Stratum-1 complete (crux split to 22d; see `notes/Phase22c.md`) |
| 22d. KT Claim 6.11 (eq. (6.23), the redundant `ab`-row) + its green-machinery prerequisites | `Molecular/Induction/ForestSurgery.lean` + `AlgebraicInduction/{CaseI,PanelLayer,PanelHinge}.lean` (extends `algebraic-induction.tex`) | ✓ Complete (see `notes/Phase22d.md`) |
| 22e. candidate-completion (eqs. (6.24)–(6.29)) + KT Claim 6.12 (Case III at `d=3`) | `Molecular/AlgebraicInduction/` + `Molecular/RigidityMatrix.lean` | ✓ Complete (N3b discharged in 22f; see `notes/Phase22e.md`) |
| 22f. N3b: point-join↔panel-meet duality (the exterior-algebra assembly completing Claim 6.12 / Lemma 6.10) | `Molecular/Meet.lean` | ✓ Complete — discharged 22e's green-modulo-N3b (see `notes/Phase22f.md`) |
| 22g. `d=3` realization assembly: design program + leaf infrastructure | `Molecular/AlgebraicInduction/` | ✓ Complete — banner flips moved to 22h (see `notes/Phase22g.md`) |
| 22h. the corrected `d=3` assembly (Theorem 5.5 at `d=3`, green-modulo the named carry family) | `Molecular/{Induction,AlgebraicInduction}/` | ✓ Complete (closed 2026-06-11; see `notes/Phase22h.md`) |
| 22i. all-`k` genuine-hinge motive + reduction-case producers (L0–L6) | `Molecular/` | ✓ Complete (closed 2026-06-14, re-scoped at a phase split; see `notes/Phase22i.md`) |
| 22j. shared eq.-(6.12) placement abstraction + Case-II/split refactor + cleanup | `Molecular/{RigidityMatrix,AlgebraicInduction}/` | ✓ Complete (see `notes/Phase22j.md`) |
| ⋮ Perf pass (post-Phase-22j) | `Molecular/AlgebraicInduction/CaseI.lean` (10,346-line) file split into a 5-file chain | ✓ Complete (the pre-22k internal step; see `notes/Phase22j-perf.md`; plan: `notes/PERFORMANCE.md`) |
| 22k. completing the honest all-`k` Theorem 5.5 (Case III, spine) + Thm 5.6 `d=3` | `Molecular/` | ✓ Complete (see `notes/Phase22k.md`) |
| 22l. ScrewSpace carrier opacity — d=3 API + migration | `Molecular/{RigidityMatrix, AlgebraicInduction/}` | ✓ Complete — build-time refactor, d=3 scope (see `notes/Phase22l.md`) |
| ⋮ Perf pass (post-Phase-22l) | molecular file splits — `RigidityMatrix/` (3 files) + `CaseIII/` (4 files) + `ForestSurgery/` (2 files) subdirectories | ✓ Complete (see `notes/Phase22l-perf.md`; protocol: `notes/PERFORMANCE.md`) |
| 23. Case III general `d` (Lemma 6.13) → Thm 5.5/5.6 → Conjecture 1.2 | `Molecular/` (sub-lettered; codes-until-open) | ◐ In progress — 23a/CARRIER + 23b/CHAIN closed (CHAIN bricks landed; the `hρGv`-seam characterized as a hard core — the member-mapping wall, intrinsic to KT); 23c open on the option-(A) rank-cert re-architecture (de-risk spike landed: basis-free block-rank-additivity, no carrier friction) + chain-dispatch completion; ENTRY/ASSEMBLY code-only (see `notes/Phase23c.md`) |
| 24–26. Molecular conjecture program (rest) | (none yet — planned) | ◷ Planning (see `notes/MolecularConjecture.md` + §"Phase 17+" below) |

The Status table is a **thin index**: each cell is a status marker plus
at most one short scope clause and a `(see notes/PhaseN.md)` pointer —
**never** a phase summary. The one-paragraph summary lives in the
per-phase prose under *Mathematical roadmap* (§N) below; the lemma list
and decisions live in `notes/PhaseN.md`. A cell that grows past a clause
or two has absorbed content that belongs in §N — re-thin it.

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
`none : Option V`); both preserve the Laman property, both edge-set
decompositions land, and iso transport (`IsSparse/IsTight/IsLaman.iso`)
lifts Laman across isomorphisms, with canonical iso constructors
(`typeI_iso_of_two_neighbors`, `typeII_iso_of_three_neighbors`)
downstream phases consume. The structural decomposition theorem
`IsLaman.exists_typeI_or_typeII_reverse` lives here (flat form, per
Phase 7). Phase 3 shipped only its iso-only half: the typeII reverse
can fail for an arbitrary non-adjacent pair (6-vertex counter-example
in `notes/Phase3.md`), so the strengthened `G'.IsLaman` claim and
generic-rigidity preservation were deferred to Phase 5 (§5). Full
lemma list and decisions → `notes/Phase3.md`.

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Complete. Defines `Framework V d`, `RigidityMap G p` (the `ℝ`-linear
map; matrix view deferred), `IsInfinitesimallyRigid` (kernel-dimension
bound `dim ker ≤ d(d+1)/2`), and `IsGenericallyRigid` (existence of an
IR placement), with the basic `RigidityMap` API, the graph-monotonicity
corollaries, the main edge-count theorem `IsGenericallyRigid.card_mul_le`
(`d·#V ≤ #E + d(d+1)/2`), and the K₂ worked example. The `TrivialMotions`
API was deferred (off the Phase-5 critical path) and landed in Phase 6.
Full lemma list and decisions → `notes/Phase4.md`.

### Phase 5 — Laman's theorem, (⇐) direction (`LamanTheorem.lean`, `HennebergRigidity.lean`)

Complete. The Laman-theorem iff
`isGenericallyRigid_two_iff_exists_isLaman_le` (`LamanTheorem.lean`,
`G.IsGenericallyRigid 2 ↔ ∃ H ≤ G, H.IsLaman`) is composed from
`IsLaman.isGenericallyRigid_two` (⇐, this phase) and
`IsGenericallyRigid.exists_isLaman_le` (⇒, `sorry`-blocked here,
resolved in Phase 6, §6). The (⇐) half: Henneberg induction on
`card V` — K₂ base + iso transport, inductive step via the
strengthened `exists_typeI_or_typeII_reverse` (resolving Phase 3's
deferred blocker) plus unconditional per-move rigidity preservation,
with the Type II collinearity gap discharged by openness of IR + a
perpendicular perturbation. A non-blocking refactor unifying the
blocker-argument contradiction templates (~210 LoC) is noted in
`notes/Phase5.md`, alongside the full lemma list and techniques.

### Phase 6 — Laman's theorem, (⇒) direction (`LamanTheorem.lean`, `RigidityMatroid.lean`)

Complete. Builds the rigidity-matroid scaffolding in
`RigidityMatroid.lean` (row-independence, dual-module bridge, generic
rank lower bound, affinely-spanning rank upper bound, basis-pick),
then ships Lovász–Yemini's easy direction in dim 2 and the assembly
`IsGenericallyRigid.exists_isLaman_le`, closing both directions of the
Phase-5 iff. Phase 6 stood up the matroid scaffolding without
packaging the abstract `Matroid` instance — the easy direction needs
only the row-independence relation + two LA facts (cf. DESIGN.md
*Notion- and matroid-agnostic core*). Ran in forward blueprint mode.
Full lemma list and decisions → `notes/Phase6.md`.

### Phase 7 — Lovász–Yemini matroid identification (`CountMatroid.lean`, `MatroidIdentification.lean`)

Complete. Ships the hard direction of Lovász–Yemini in dim 2
(converse of Phase 6's easy direction), the general $(k, \ell)$-count
matroid in the matroidal regime $\ell < 2k$ (Whiteley 1996,
Lee–Streinu 2008), and the planar rigidity-matroid specialisation.
The hard-direction induction (`MatroidIdentification.lean`) routes
through matroidal-regime $I$-component scaffolding in `Sparsity.lean`;
the abstract count matroid sits in `CountMatroid.lean` via
`IndepMatroid.ofFinite`. Ran in forward blueprint mode. The
linear-matroid framing of the rigidity matroid is deferred to Phase 8
(which adds `apnelson1/Matroid` as a dependency). Full lemma list and
decisions → `notes/Phase7.md`.

### Phase 8 — Linear-matroid framing (`LinearRigidityMatroid.lean`)

Complete. Packages the planar rigidity matroid in linear-algebra form
via `Matroid.ofFun` (from `apnelson1/Matroid`) of the rigidity-row
function at a uniformly-generic placement, and identifies it with
Phase 7's combinatorial $(2,3)$-count matroid
(`linearRigidityMatroid_eq_rigidityMatroid`, package equality on
`Matroid (Sym2 V)`). The content is uniform genericity, proved by
linear-interpolation perturbation on the finite family of
$(2,3)$-sparse subsets, routed through two new mirror lemmas under
`Mathlib/LinearAlgebra/Matrix/Rank.lean`. Ran in forward blueprint
mode. Full lemma list, decisions, and hand-off → `notes/Phase8.md`.

### Phase 9 — Pebble game (`PebbleGame/{Basic, Algorithm, Correctness}.lean`)

Complete. Formalizes the $(k, \ell)$-pebble game of Lee--Streinu
2008 (generalising the $(2, 3)$ algorithm of Jacobs--Hendrickson
1997) end-to-end in the matroidal regime $\ell < 2k$ matching
Phase 7: the computable three-layer algorithm chain, the four
L-S Lemma 10 invariants, the certificate-form correctness theorem,
and the matroidal-independence corollary composing onto Phase 7's
`countMatroid_indep_iff`. Three-way file split under `PebbleGame/`
post-Phase-9-perf; ran in forward blueprint mode
(`blueprint/src/chapter/pebble-game.tex`). The full lemma list, the
pre-phase DFS warmup (`Search/DFS.lean`), decisions/hand-off, and the
deferred L-S §5/§6 follow-ups → `notes/Phase9.md`.

### Phase 10 — Executable pebble game (`PebbleGame/{Exec, Examples}.lean`, `Main.lean`)

Complete. Bridges Phase 9's `noncomputable` `runPebbleGame` to a
runnable decision procedure: the computable `runPebbleGameExec` (via
`Finset.sort` list views under `[LinearOrder V]`) plugged into Phase
9's `-With` workhorses, a workhorse-level correctness restatement both
layers derive from, the canonical `Decidable` instances for
`IsSparse/IsTight/IsLaman` (matroidal regime $\ell < 2k$), and a
`lake exe pebble-game` CLI printing `LAMAN`/`SPARSE_NOT_TIGHT`/
`NOT_SPARSE`. Ran in forward blueprint mode. The blocking/orientation
witness extraction at the CLI branches was deferred to Phase 11. Full
layer-by-layer summary and architectural choices → `notes/Phase10.md`.

### Phase 11 — Witness extraction (`Search/DFS.lean`, `PebbleGame/{Basic,Algorithm,Correctness,Exec}.lean`, `Main.lean`)

Complete. **Structural-edit phase** reshaping Phase 9/10's
$\mathrm{Option}$-shaped algorithms into the verdict-bearing inductive
`PebbleGameResult G k ℓ` (`.accept` carries the orientation $D$,
`.reject` the blocking subset $V'$), with the workhorses reshaped to a
`Sum` of witness/orientation and the failure witness built inline; the
Phase 9 existence chain is absorbed and the certificate-form theorems
collapse into the verdict's type. The substantive prerequisite — a
verified-iterative *computable* `reachClosureComputable`
(`Search/DFS.lean`) — replaces the `Classical.decPred` reach closure,
and the CLI emits `ARCS`/`BLOCKING`/`VERTEX` lines. Ran in
structural-edit mode (no new chapter; reshape distributed across
`chapter/{dfs,pebble-game,executable}.tex`). Full five-layer plan and
decisions → `notes/Phase11.md`.

The body-bar program was re-scoped from a single blocked "Phase 12"
into the dependency-ordered chain 12–15 (2026-06): the matroid-union
machinery intended for vendoring from `apnelson1/Matroid` was already
fully formalized there but bit-rotted onto a superseded circuit-axiom
constructor, so it became a real local formalization phase (12). See
`notes/Phase12.md` *Prerequisites audit*.

### Phase 12 — Matroid foundations: submodular functions & matroid union

Complete. Formalizes the abstract-matroid prerequisites of the body-bar
route, **locally** under `CombinatorialRigidity/Matroid/`: matroid-from-
submodular-function + polymatroid rank (Edmonds 1970), matroid union
(Nash-Williams 1966 / Edmonds), Rado's theorem (Rado 1942), and Edmonds'
matroid-partition rank formula (Edmonds 1965). The Lean is **ported from
Peter Nelson's `apnelson1/Matroid`** (Apache-2.0), rebased onto its live
`FiniteCircuitMatroid` constructor — an explicit exception to the
small-mirror convention (`DESIGN.md` *Local mirror of the matroid-union
subsystem*). Ran route (a) (submodular-repair) in forward blueprint mode.
Full Layer plan, prerequisites audit, and attribution discipline →
`notes/Phase12.md`.

### Phase 13 — Tutte–Nash-Williams tree-packing

**✓ Complete** (`notes/Phase13.md`). Specialized Phase 12's
matroid-partition theorem to `k` copies of `Graph.cycleMatroid`,
recovering Tutte–Nash-Williams tree-packing (Tutte 1961, Nash-Williams
1961): `Graph.tutte_nash_williams` (a multigraph is the edge-disjoint
union of `k` forests iff `(k,k)`-sparse) + the connected-tight
spanning-tree refinement (Whiteley Thm 13). Introduced a `Graph`-native
`Set`-side `(k,ℓ)`-sparsity predicate (`Graph.IsSparse/IsTight`, fresh,
**not** migrated from the `SimpleGraph` one; see `DESIGN.md`
*Set/Finset … boundary at the matroid layer*) + a thin rank adapter
bridging the partition formula to the `k`-fold `cycleMatroid` case.
Carrier: mathlib `Graph α β`. Unblocks Phase 14. Per-node map →
`notes/Phase13.md` + `body-bar.tex`.

### Phase 14 — k-frame matroid = k-fold cycle-matroid union

**✓ Complete** (`notes/Phase14.md`). Whiteley 1988 Theorem 1: the
generic `k`-frame matroid `F(G,X)` (a linear matroid via `Matroid.ofFun`
over `KFrameField β k`) equals the `k`-fold union of
`Graph.cycleMatroid` restricted to `E(G)`
(`Graph.kFrameMatroid_eq_unionPow_cycleMatroid`). Whiteley §2.1's
genericity runs as a forward rank count + a forest-packing
block-diagonal reverse, packaged into a count bridge matching Phase
13's by `Matroid.ext_indep`. The `↾ E(G)` is forced — the vendored
`Matroid.Union` has ground `univ`, so the bare equality is unprovable
(non-edges become loops). Carrier: mathlib `Graph α β`. Unblocks Phase
15. Per-node map (incl. coefficient encoding + restriction) →
`notes/Phase14.md` + `body-bar.tex`.

### Phase 15 — Body-bar Tay theorem (existence form)

**✓ Complete** (`notes/Phase15.md`). The original Phase-12 target,
unblocked by the 12–14 chain: Tay's theorem in existence-of-realization
form (Whiteley 1988 Thm 8, Tay 1984) — for `d = bodyBarDim n =
n(n+1)/2`, a multigraph carries an independent (resp. isostatic)
body-bar framework in `ℝⁿ` iff `(d,d)`-sparse (resp. tight):
`BodyBarFramework.tay_witness`, the standard-basis-witness iff (via
`tutte_nash_williams` + a block-diagonal rank count) with the converse
`isSparse_of_isIndependent` (the body-bar analogue of Phase 6's
easy-direction converse, via the block-diagonal rank upper bound + the
cycle-matroid bound `r(E')+1 ≤ |V'|`). Architectural decisions: carrier
mathlib `Graph α β`, Plücker/two-extensor coordinates handled **inline**
(degenerate permitted, standard-basis witness only); Whiteley's "almost
all realizations rigid" lift deferred to Phase 16. Forward-mode;
per-node map → `notes/Phase15.md` + `body-bar.tex`.

### Phase 16 — Body-hinge Tay–Whiteley theorem (existence form)

**✓ Complete** (`notes/Phase16.md`). The body-hinge / panel-hinge
Tay–Whiteley theorem in `n`-space (Tay 1989, Whiteley 1988),
existence-of-realization form, **via matroid-union reduction to Phase
15**: a hinge constrains all but one of the `δ = bodyBarDim n` relative
screw freedoms, so it behaves like `δ−1` coincident body-bars. The
chapter adds *no new linear algebra* — parallel-edge multiplication
`(δ−1)·G` (`Graph.edgeMultiply`, KT 2011's molecular device) + a
body-hinge framework *defined* as the induced body-bar framework on
`(δ−1)·G`, inheriting independence/rigidity verbatim. Target
`body_hinge_tay`: `G` carries an independent (resp. isostatic)
body-hinge framework iff `(δ−1)·G` is `(δ,δ)`-sparse (resp. tight),
via `tay_witness` transported across the body-hinge ⇔ body-bar
bijection + `tutte_nash_williams`. Carrier mathlib `Graph α β`,
standard-basis witness only; the "almost all rigid" lift remains
deferred. Forward-mode; per-node map → `notes/Phase16.md` +
`body-hinge.tex`.

### Phase 17+ — The Molecular Conjecture program

**Status: Phases 17–22l (+ 21a/21b) complete** — Katoh–Tanigawa's
Theorems 5.5 and 5.6 are formalized at `d = 3` at full KT strength (22l
was a build-time carrier-opacity refactor, no math change); **Phase 23
(general `d`) is active**; Phases 24–26 planned.

The longer-horizon target is the **molecular conjecture** (panel-and-hinge
with hinges at each body forced concurrent/coplanar; Tay–Whiteley 1984,
proved by Katoh–Tanigawa 2011, Discrete Comput. Geom. **45**, 647–700)
plus its molecule/`G²` application — the project's largest single
undertaking (≈ Phases 1–16 combined), scoped as a **10-phase program
(17–26)**. KT's proof splits into a **combinatorial step** (graph
induction generating minimal `k`-dof-graphs via splitting-off +
rigid-subgraph contraction; §3–4, Thm 4.9) and an **algebraic step**
(geometric induction realizing each move at the target rigidity-matrix
rank; §5–6, Thm 5.5 → 5.6). Unlike Phases 15–16 (body-hinge rigidity *by
reduction*, standard-basis witness only), the conjecture forces the
**genuine panel-hinge rigidity matrix `R(G,p)`** with real extensor
geometry and honest rank computations on *specific, non-generic*
realizations. The full phase table (the 17–26 breakdown), reuse map,
citations, and risk register live in **`notes/MolecularConjecture.md`**;
per-phase summaries are the §§ below (18–23). The planned phases — **24**
(3-D generic bar-joint matroid, dim-3 specialization of Phase 4/8; *not*
a 3-D Laman characterization, KT §7), **25** (Crapo–Whiteley projective
invariance + the molecule ↔ body-hinge ↔ panel-hinge modelling
equivalence, §1.2), **26** (Corollary 5.7 `r(G²) = 3|V| − 6 − def(G̃)`,
the protein-flexibility capstone) — are detailed there.

**Phase 17** (`Molecular/Extensor.lean`; `notes/Phase17.md`; forward-mode
chapter `blueprint/src/chapter/molecular.tex`) formalized the
Grassmann–Cayley / extensor-algebra layer (KT §2.1) end to end:
homogeneous coordinatization, the affine-independence ↔ top-extensor
bridge, the symbolic extensor/join on `ExteriorAlgebra ℝ (Fin (d+1) →
ℝ)`, the coordinatized Plücker bridge, the affine-subspace extensor
`C(·)`, and **Lemma 2.1** — independence of the `D = (d+1 choose 2)`
many `(d−1)`-extensors of `d+1` affinely independent points
(`omitTwoExtensor_linearIndependent`), on which Case III (Phases 22–23)
bottoms out.

### Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (KT §2.2–2.4, §5 prep)

**✓ Complete** (`notes/Phase18.md`). Stratum 2: the **genuine**
panel-hinge rigidity matrix `R(G,p)` (`Molecular/RigidityMatrix.lean`),
building on Phase 17's extensors and superseding Phase 16's
reduction-only form as the rank form. A body-hinge framework assigns a
`(d−2)`-affine hinge per edge; its supporting `(d−1)`-extensor `C(p(e))`
constrains the screw centers (`S(u) − S(v) ∈ span C(p(e))`). Landed
basis-free: the hinge constraint + dual-annihilator row block + null
space `Z(G,p)`, the trivial-motion layer with the `rank R ≤ D(|V|−1)`
codimension counts, and the three rank lemmas 5.1/5.2/5.3 (pin-a-body,
rotation semicontinuity, parallel-hinges base). The KT Prop 1.1
reconciliation was relocated forward to Phase 21+ — its matroidal half
(`def = corank`) landed in Phase 19, its analytic half (`rank R =
D(|V|−1) − def(G̃)`) with the algebraic induction. Forward-mode
(`rigidity-matrix.tex`). Per-lemma detail → `notes/Phase18.md`.

### Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (KT §2.5, §3)

**✓ Complete** (`notes/Phase19.md`). Stratum 3: the combinatorial /
matroidal substrate the algebraic induction (21–23) runs against, in
`Molecular/Deficiency.lean` — the matroid `M(G̃)` (the `(D,D)`-count
matroid of `G̃ = (D−1)·G` at the **boundary regime `ℓ = 2k = D`**, the
`D`-fold graphic union of Phases 13/14 + Tutte–Nash-Williams, **not**
the `ℓ<2k` `CountMatroid.lean`), the `D`-deficiency `def(G̃)`, the
`k`-dof / minimal-`k`-dof hierarchy, rigid + proper rigid subgraphs (KT
Lemmas 3.1/3.3/3.4), and the **def = corank bridge** `|B| + def(G̃) =
D(|V|−1)` (project framing of Jackson–Jordán 2009 Thm 6.1/Cor 6.2,
proved axiom-free). The bridge is the matroidal half of KT Prop 1.1; the
analytic half relocated to Phases 21+. Forward-mode. Unblocks Phase 20.
Per-node map → `notes/Phase19.md`.

### Phase 20 — Combinatorial induction → Theorem 4.9 (KT §3.4–3.5, §4)

**✓ Complete** (`notes/Phase20.md`). Stratum 4: the **combinatorial**
half of KT's proof, in `Molecular/Induction/` — the graph operations on
`Graph α β` (vertex removal, splitting-off, edge-splitting,
rigid-subgraph contraction), the KT 3.4/3.5 contraction-minimality chain
(the Case I engine), the dof bounds + reducible-vertex lemmas (KT
4.3–4.8), and the capstone **Theorem 4.9** `Graph.minimal_kdof_reduction`
(green, axiom-free): every minimal `0`-dof-graph with `|V| ≥ 2` reduces
to the two-vertex double edge. Two route findings — KT Lemma 4.1 is
over-quantified (formalized counterexample, routed around via a
deficiency-count argument), and KT's iterated fundamental-circuit swaps
are bypassed via partition-/rank-count comparisons through the green
`def = corank` bridge — plus the forest-surgery (KT 4.1, landed) status
and the deferred KT 4.2 TODO are in `notes/Phase20.md`. Unblocks Phase 21.

### Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (KT §5, §6.1–6.3)

**✓ Complete (GREEN-modulo-21b)** (`notes/Phase21.md`). Stratum 5: the
*algebraic* half of KT's proof, in `Molecular/AlgebraicInduction/` —
realizing Phase 20's combinatorial reduction at the rigidity-matrix
rank: KT **Theorem 5.5** (`theorem_55`), its base case, **Case I**
(rigid-subgraph contraction + block-triangular gluing) and **Case II**
(`k>0` splitting = panel-hinge 1-extension), plus the relocated analytic
half of KT Prop 1.1 (`rigidityMatrix_prop11`, `rank R = D(|V|−1) −
def(G̃)`, JJ 2009 Thm 6.1; matroidal half green from Phase 19). The
induction runs against the same `minimal_kdof_reduction` dichotomy. Two
re-scopes: a **panel layer** (hinge-coplanar body-hinge, gated on
sub-phase **21a** Grassmann–Cayley meet), and the **genericity
scope-out** — the shared analytic crux Claim 6.4/6.9 is sub-phase
**21b**, entering each consumer as an explicit hypothesis. Case III
(`k=0`, no proper rigid subgraph) is deferred to Phases 22–23.
Forward-mode. Detail → `notes/Phase21.md`, `notes/Phase21a.md`,
`DESIGN.md`.

### Phase 22 — Realization layer (sub-lettered: 22a + 22b + 22c + 22d + …)

The realization layer (the Theorem-5.5 case *producers* the genericity
device feeds) opened as a single Phase 22 on 2026-06-04 and was **split
into sub-phases the same day** — it bundled three independent bodies of
work (Case I; Case III at `d=3`; the `d=3` assembly). Sub-lettering
(22a, 22b, …) keeps integer phases 23–26 stable; sub-letters name one
distinct chunk each, minted only when its turn comes (Case III at `d=3`
split: stratum 1 = 22c, the `D`-candidate crux = 22d; the assembly's
design stratum = 22g, corrected build = 22h). **Structural-edit phase:**
no new chapter — the producer nodes extend `algebraic-induction.tex`; the
KT math is worked out in `notes/Phase21b.md` *Finding A/B*.

#### Phase 22a — Case I realization (KT §6.2) — ✓ Complete (green-modulo-22b)

**✓ Complete (green-modulo-22b)** (`notes/Phase22a.md`). Track A: the
full-rank Case I realization producer. The composer
`PanelHingeFramework.case_I_realization` (`lem:case-I-realization`)
discharges `theorem_55`'s Case-I branch green-modulo a single hypothesis
= KT Claim 6.4 (red node `lem:claim-6-4`, deferred to 22b), via the
**block-triangular reframe** of KT eq. (6.3)'s rank-addition over one
common framework, routed through the genericity device's independent-row
count (not a common-seed splice). The phase's cross-cutting lesson —
reproduce the source's argument **structure**, not just its conclusion —
is promoted to `DESIGN.md` *Match the source's argument structure …*.
Brick inventory, decision history, and hand-off → `notes/Phase22a.md`.

#### Phase 22b — KT Claim 6.4 (Case-I green-modulo discharge, KT §6.2/§5.1) — ✓ Complete

**✓ Complete** (opened + closed 2026-06-05; `notes/Phase22b.md`). Scope:
*just* KT Claim 6.4 — the hypothesis 22a left green-modulo (the surviving
block of `G ＼ E(H)`, exterior-projected to `V(G)∖V(H)`, attains
independent rank `≥ D(|sc|−1)` at a generic locus; KT eqs. (6.5)/(6.9),
§5.1). Discharged via the recon's node cut (the bounded rank-polynomial
variant → the rank-transport across the collapse map via algebraic
independence → the wire-up), flipping `lem:claim-6-4` and
`lem:case-I-realization` fully green. Renumbered the parked
Case-III/assembly territory `22b+` → `22c+`. Full record →
`notes/Phase22b.md`; design §1.13–§1.16.

#### Phase 22c — Case III at `d=3`, stratum 1 (KT §6.4.1, Lemma 6.10, the eq. (6.12) `+(D−1)` placement) — ✓ Stratum-1 complete

**✓ Stratum-1 complete** (opened 2026-06-05 design-pass-first; crux split
to 22d; `notes/Phase22c.md`). Track B at `d=3`, the conjecture's crux —
KT §6.4.1, Lemma 6.10 (KT's single largest proof, ~12 pages):
`theorem_55.hsplit` at `k=0`, target full rank `D(|V|−1)`. 22c claimed
only **stratum 1** — the eq. (6.12) degenerate placement giving a
block-triangular `R(G,p₁)` with `rank ≥ D(|V|−1)−1`, **one row short**
(`case_II_placement_eq612`, green + axiom-clean). The missing `+1` row
(Lemma 6.10's `D`-candidate argument, Claims 6.11/6.12) is Phase 22d;
target nodes `lem:case-II-realization`/`lem:case-III` stay red. Opened on
a five-pass layer design recon before any Lean (per `DESIGN.md`
*Scale-up: design the LAYER, not just the node*). Record →
`notes/Phase22c.md`; design §1.25–§1.29.

#### Phase 22d — KT Claim 6.11 (the redundant `ab`-row) + its green-machinery prerequisites — ✓ Complete

**✓ Complete** (opened 2026-06-05 design-pass-first; `notes/Phase22d.md`).
Attacked the conjecture's hardest single argument — the *missing `+1`
row* lifting 22c's `D(|V|−1)−1` brick toward full rank — and delivered,
green + axiom-clean, KT **Claim 6.11 / eq. (6.23)**
(`lem:case-III-claim-6-11`, the redundant `ab`-row) with its supporting
chain (the matroid-base form of KT 4.3(ii) at `k=0`, the nested-IH shell
`G−v`, the analytic seed-rank kernel + its `def>0` rank bounds, the `hub`
codimension bound, the redundant-row pigeonhole). The kernel forced the
project's first **algebraic-independence** use (KT footnote 6 needs *this*
seed attains the rank, not *∃* a seed; tracked in
`notes/AlgebraicIndependence.md`). The successor candidate-completion
(eqs. (6.24)–(6.29)) / Claim 6.12 / `d=3` assembly is the deferred cut
(→ 22e+); general `d` stays Phase 23. Lemma map + Gap-2→3→1 story →
`notes/Phase22d.md`.

#### Phase 22e — candidate-completion + KT Claim 6.12 (Case III at `d=3`), green-modulo-N3b — ✓ Complete

**✓ Complete (green-modulo-N3b)** (closed 2026-06-07; `notes/Phase22e.md`).
Successor to 22d: completed the `d=3` Case III algebra (KT §6.4.1, Lemma
6.10) green-modulo-N3b. Converted 22d's redundant `ab`-row into the
missing `+1` row via the eqs. (6.24)→(6.29) row-op construction
(`lem:case-III-candidate-row`) and discharged the top-left full-rank
conditional with KT's **Claim 6.12** `D`-candidate disjunction
(`lem:case-III-claim612`: the degree-2 eq. (6.44) forces all candidates
to test the same `r ∈ ℝ⁶`, which the green Phase-17 Lemma 2.1 forces to
zero). The four affinely-independent points (N3a) took the
existence/Zariski route. Green modulo the single point-join↔panel-meet
duality leaf (N3b → Phase 22f); the producer nodes
`lem:case-II-realization`/`lem:case-III` stay red pending the `d=3`
realization assembly. Plan + decisions → `notes/Phase22e.md`.

#### Phase 22f — N3b: point-join ↔ panel-meet duality assembly (KT §6.4.1) — ✓ Complete

**✓ Complete** (closed 2026-06-07; `notes/Phase22f.md`). Discharged 22e's
green-modulo-N3b leaf `lem:case-III-claim612-line-in-panel-union` — the
point-join ↔ panel-meet duality at `d=3` (`ScrewSpace 2 = ⋀²ℝ⁴`): a
line's point-join `p̄ᵢ ∨ p̄ⱼ` and its panel-meet supporting extensor
`C(L)` are scalar multiples (both the line's Plücker vector), so an `r`
annihilating every `C(L)` annihilates each spanning join (KT's implicit
eq. (6.45) Grassmann–Cayley duality). The proof places both in the 1-dim
dual-annihilator line (concrete at `⋀²ℝ⁴`, not general Hodge theory;
`Molecular/Meet.lean`). Took Claim 6.12 + the candidate-completion fully
green; the producer nodes await only the `d=3` assembly (22g). Detail →
`notes/Phase22f.md`.

#### Phase 22g — the `d=3` realization assembly: design program + leaf infrastructure (KT §6.4.1) — ✓ Complete

**✓ Complete** (closed 2026-06-09; `notes/Phase22g.md`). The
design-program + leaf-infrastructure stratum of the `d=3` assembly (the
22c→22d precedent; the banner flips moved to 22h). Pinned the `d=3`
Case-III crux architecture — `case_III_claim612` restated to a
premise-free **existential** over the six point-joins (the three-fixed
disjunction is undischargeable, dim 3 < 6; the producer builds its
candidate at the witness join's line) — landed ~15 axiom-clean leaves,
and produced the recon (design §1.44–§1.49) scoping the remaining work as
GAPs 1–5 (the `|V|=3` triangle base T1–T4, the `M₃` third-panel dispatch
G4a–G4e with branch-interface verdict (β), the bounded good-`t`, the
bare→generic upgrade, the proper-rigid-subgraph predicate repair G5), all
handed to 22h with signatures (§1.48–§1.49). Ledger → `notes/Phase22g.md`.

#### Phase 22h — the corrected `d=3` assembly (KT §6.4.1, §5.2) — ✓ Complete

**✓ Complete** (closed 2026-06-11; `notes/Phase22h.md`). Built the GAPs
1–5 picture 22g scoped (signatures canonical in
`notes/Phase22-realization-design.md` §1.48–§1.55) and took
`lem:case-II-realization`/`lem:case-III` green at `d = 3` (both pinned to
`case_III_realization`): the G5 predicate repair, the
full-conditioned-IH (β) restate, the `|V|=3` triangle floor (T1–T4), the
(β)-shaped `hsplit` producer with the full candidate-placement discharge
(W1–W10b, the KT-Lemma-5.2 rank-transfer assembly for the `M₁/M₂/M₃`
arms), the `theorem_55_d3` instance, and the Thm 5.5→5.6 deficiency
stratum. **Closed green-modulo a named carry family** {`h622`, `h65`,
`hbase`/`hsplit`/`hcontract`} — user-adjudicated close shape — all
discharged across **22i** (motive + reduction producers) and **22k**
(Case III/`h622`, Lemma 6.5/`h65`, spine/`hsplit`), with **22j** between.
Postmortem of the two divergences → `DESIGN.md` *Statement faithfulness
to the source*. General `d` is Phase 23.

#### Phase 22i — all-`k` genuine-hinge motive + reduction-case producers (KT §3, §5.2, §6.1–6.4) — ✓ Complete

**✓ Complete** (closed 2026-06-14; `notes/Phase22i.md`). "The honest
all-`k` Theorem 5.5": discharge the 22h carries by restating the
realization motive at KT's strength and re-running the spine. Delivered
**L0–L6**: the **genuine-hinge all-`k` motive** (the bare motive on the
free-hinge `BodyHingeFramework` carrier with extensor-in-panel
containment — KT's coincident-panel Lemmas 5.3/6.2 are inexpressible with
a derived hinge-as-meet — plus the generic motive; design §1.56), the
combinatorial bricks, the four-case `|V|`-recursion
`minimal_kdof_reduction_all_k` (adding the Lemma-6.1 not-2EC and Lemma-6.8
`k>0` cases), and the reduction-case producers (`hbase`/`hcontract`
discharged). **Re-scoped at close** (user-adjudicated): the shared
placement abstraction is **22j**, the Theorem-5.5 completion (Case
III/`h622`, Lemma 6.5/`h65`, spine/`hsplit`) + Thm 5.6 `d=3` is **22k**.
So all-`k` Thm 5.5→5.6 spans 22i+22k. Carries table + layer plan →
`notes/Phase22i.md`.

#### Phase 22j — the shared eq.-(6.12) placement abstraction (KT §6.3, §6.4.1) — ✓ Complete

**✓ Complete** (`notes/Phase22j.md`). A refactor sub-phase between 22i
and 22k: introduced the span-transport **pinned-placement rank brick**
`le_finrank_span_rigidityRows_of_pinned_placement` (+ its `+1` augment)
the Case-II / Lemma-6.8 producers should have shared (the pin-a-body
analogue of the Case-I splice brick), consolidated the L6b producer onto
it, and landed producer cleanup (dead-code deletion + dropping both
stopgap suppressions: heartbeats 3.2M → 600000 via two extracted
helpers). Folded in a dedicated `CaseI.lean` file-split perf round — the
10,346-line monolith is now the 5-file chain `GenericityDevice ←
Coupling ← CaseI ← CaseII ← CaseIII ← Theorem55` (rename-free, all 50
pins intact). Rationale + decisions → `notes/Phase22j.md`; design §1.68.

#### Phase 22k — completing the honest all-`k` Theorem 5.5 (Case III, spine) + Thm 5.6 `d=3` (KT §5.2, §6.1–6.4) — ✓ Complete

**✓ Complete** (closed 2026-06-16; `notes/Phase22k.md`). Completed the
honest all-`k` Theorem 5.5 (the 22i→22j→22k arc) and pushed through to
Theorem 5.6 at `d = 3`. The three remaining 22h carries (`h622`, `h65`,
`hsplit`) were discharged (Case-III rewire deriving the nested rank bound
from the all-`k` IH; the KT Lemma-6.5 vertex-removal arm via Claim 6.6 +
a vacuity argument forcing `def = 0`; the no-rigid-subgraph branch wired
through Case III), leaving a zero-carry spine `theorem_55_all_k` + its
`d = 3` instance, both green. Theorem 5.6 at `d = 3`
(`rankHypothesis_of_theorem_55_d3`) then lifts to arbitrary deficiency
(strip to a minimal `k`-dof subgraph, realize, re-add edges), completing
the analytic half of KT Prop 1.1 (`rigidityMatrix_prop11`) at `d = 3`.
Unblocks Phase 23. Map → `notes/Phase22k.md`.

#### Phase 22l — ScrewSpace carrier opacity: the d=3 API + migration — ✓ Complete

**✓ Complete** (opened + closed 2026-06-16; `notes/Phase22l.md`). A
**structural-edit refactor** (no new math, no blueprint change)
addressing the build-time cost behind the surviving `maxHeartbeats`
overrides: `ScrewSpace k` was a reducible `abbrev` for `↥(⋀^k ℝ^(k+2))`,
so every defeq / `simp` / `Module.Dual` motive re-unfolded the heavy
exterior-power expression. It is now an **opaque `def`** with a
`mk`/`val`/`≃ₗ` API; the `d = 3` tree was migrated onto it bottom-up and
the flip landed in one mechanical commit, dropping the molecular
`maxHeartbeats` count 3 → 1. Scope was `d = 3` only; the general-`d` API
+ "part 2" migration is deferred to the Phase-23 boundary. The math
frontier is unchanged. Recon/spike → `notes/ScrewSpaceCarrier-design.md`;
plan → `notes/Phase22l.md`.

#### Phase 23 — Case III general `d` (KT Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 (§6.4.2, §5.2)

**Status (◐ In progress; opened 2026-06-17 on a general design recon — docs
only; see `notes/Phase23a.md`).** The conjecture's crux generalization: lift
the `d = 3` Case III (Lemma 6.10) to general `d` (Lemma 6.13 — a length-`d`
chain `v₀…v_d` with `d` candidate frameworks and isomorphisms `ρᵢ`, eqs.
6.46–6.67), complete Theorem 5.5, derive Theorem 5.6, and state Conjecture
1.2 as a theorem. The recon's load-bearing finding: the realization **spine**
(`theorem_55_*`, `case_III_realization*`, `case_III_candidate_dispatch`) is
`screwDim 2`/`ScrewSpace 2`/`Fin 4`-**pinned** at `d = 3`, not "`k`-free" — so
the work splits along that fault line into a *mechanical carrier lift* and a
*genuinely new chain argument*. **Sub-lettered, codes-until-open** (a letter +
`notes/Phase23X.md` minted only when a layer opens, keeping the integer phases
24–26 stable, as Phase 22 did): **`CARRIER`** (= the minted **23a**) = the
general-`d` carrier lift of the spine to symbolic `screwDim k` (folding in the
deferred ScrewSpaceCarrier §6 "part 2" migration — the first sub-phase);
**`CHAIN`** = the general-`d` Case-III chain dispatch (eqs. 6.49–6.64) + the
`⋀^{d−1}(ℝ^{d+1})` duality finish (eq. 6.67, replacing the bespoke `⋀²ℝ⁴`
route); **`ENTRY`** = the chain-entry ingredients (Lemma 4.6 chain-or-cycle
dichotomy, Lemma 5.4 short-cycle base, Lemma 4.8 split-off — standalone-vs-
folded is an open decision); **`ASSEMBLY`** = assembly (Theorem 5.5 → re-green
`prop:rigidity-matrix-prop11` → Theorem 5.6 → Conjecture 1.2). Reuse verbatim
(source-verified general & green): Lemma 2.1, Claim 6.11
(`exists_redundant_panelRow_ab_of_finrank_eq`),
`linearIndependent_sum_augment_candidateRow`, the `complementIso` meet API.
The authoritative recon — sub-phase scope/hard-core/sequence, the corrected
reuse/replace/add map, the per-file reach-in map + 23a 6-leaf plan, and the
open decisions — is `notes/Phase23-design.md` (the general §1–§5 plus the
detailed §"23a"). The 23a recon settled OD-5 (the symbolic-`k` coordinate
transport **ports verbatim** — already general in HEAD — so no carrier-API
addition and no build-spike) and OD-2/OD-3 (Lemmas 4.6/4.8 exist only in
fixed-tuple `d=3` form; the length-`d` chain producer is a new `ENTRY` leaf).
**`CARRIER`/23a is complete** (closed 2026-06-17, Leaves 0–5; the general-`k`
Theorem 5.5 spine `theorem_55_minimalKDof_k_all_k` is green-modulo the
CHAIN+ENTRY boundary, with the `d=3` line fully green via a zero-carry `k=2`
wrapper). A Leaf-5 build-contact finding **expanded that boundary** beyond the
recon: besides the chain dispatch (→ `CHAIN`) and the `6 ≤ bodyBarDim n`
chain-extraction floor (→ `ENTRY`), the base / cut / Case-I / M4-forgetful-map
realization producers are **also** `d=3`-pinned — they bottom out in the
`⋀²ℝ⁴` duality `exists_extensor_eq_panelSupportExtensor` (CHAIN-grade), not
liftable by the numeral pass — so the spine carries them as four further
explicit hypotheses; `CHAIN`'s `⋀^{d−1}` duality finish is the prerequisite to
lift them. **`CHAIN`/23b is now closed** (2026-06-21): it landed the CHAIN
bricks (CHAIN-1/3/4, OD-7, CHAIN-2a, the CHAIN-2c foundation + the full `hρGv`
algebraic machinery, all axiom-clean) but did **not** reach the chain dispatch —
the `hρGv` arm slot ran into a **hard core**, the *member-mapping wall*, now
source-verified as **intrinsic to KT's argument** (KT eq. 6.62 carries a
*moving* redundant row; the four candidate route families — seed-advancing
fold, base→candidate transport, re-firing the existential `A-1`, and the
column-op/whole-matrix submatrix-containment — are all dead, adversarially
verified; design §(o‴)(I.8.15)–(I.8.20)). The unfinished CHAIN tail (the
`hρGv` chain arm + the chain dispatch + CHAIN-5) **+ the redundancy-carry
re-architecture decision it requires** are carried to **23c**
(`notes/Phase23c.md`); 23c's first commit is a feasibility recon on the
KT-faithful matrix / abstract-`r` shape vs. an ENTRY-carry. `ENTRY`/`ASSEMBLY`
remain later sub-phases (code-only); the `d=3` line stays fully green
(zero-regression). Next concrete commit: the **23c architectural-decision
recon** (see `notes/Phase23c.md` *Hand-off*).

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
- T.-S. Tay, *Linking (n−2)-dimensional panels in n-space II:
  (n−2,2)-frameworks and body and hinge structures*, Graphs Combin.
  **5** (1989), 245–273. — body-and-hinge characterization; Phase 16
  target.
- N. Katoh, S. Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011), 647–700. — molecular conjecture; the
  `(δ−1)·G` device and the Phase 17–26 program (see
  `notes/MolecularConjecture.md`).
- H. Crapo, W. Whiteley, *Statics of frameworks and motions of panel
  structures: a projective geometric introduction*, Structural Topology
  **6** (1982), 43–82. — projective invariance of infinitesimal
  rigidity; Phase 25.
- N. White, W. Whiteley, *The algebraic geometry of motions of
  bar-and-body frameworks*, SIAM J. Algebraic Discrete Methods **8**
  (1987), 1–32. — pin-a-body motion-space fact behind Lemma 5.1.
- B. Jackson, T. Jordán, *On the rigidity of molecular graphs*,
  Combinatorica **28** (2008), 645–658. — citable primary source for the
  molecule-graph rigidity rank (Corollary 5.7, Phase 26).
- W. Whiteley, *Counting out to the flexibility of molecules*, Physical
  Biology **2** (2005), S116–S126. — molecule ↔ body-hinge modelling
  survey; Phase 25.
