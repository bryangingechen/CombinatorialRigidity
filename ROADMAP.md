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
| 21. Algebraic induction: Thm 5.5 base + Cases I & II | `Molecular/AlgebraicInduction/` (KT §5, §6.1–6.3) | ✓ Complete (GREEN-modulo-21b; see `notes/Phase21.md`) — all genericity-free content green: the panel layer + regime-agnostic rank nodes, the four Lean pieces of `lem:cycle-realization`, Case I (`lem:case-I`) + Case II (`lem:case-II`) iff-realizations, the capstone induction `thm:theorem-55`, and the analytic half of KT Prop 1.1 `prop:rigidity-matrix-prop11`. Each node that needs the shared analytic crux Claim 6.4/6.9 takes it as an explicit hypothesis (`hglue`/`hspan`/`hub`/`hgen`), so the device is scoped into sub-phase **21b** and the surrounding reductions are fully formal modulo it. Case III deferred to 22–23. |
| 21a. Grassmann–Cayley meet / projective-duality foundations | `Molecular/Meet.lean` (KT §2.1 dual half) + mirror lemmas | ✓ Complete — all four deliverables green (`screwAlgebraTopEquiv`, `screwAlgebraPairingDualEquiv`, `complementIso`, `meet`); the meet is the Grassmann–Cayley dual of the Phase-17 join, `*(*A ∨ₑ *B)` over the general-grade product `gradedMul`, with `* = complementIso` (closed via the signed-permutation pairing matrix ⇒ `wedgePairing_injective` + equal finrank). `meet_ne_zero_iff` / geometric reading deferred to the Phase-21 consumers. Mirrors under `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean` + `Mathlib/Data/Finset/Card.lean`. See `notes/Phase21a.md`; dep-graph `meet.tex` `sec:molecular-meet`. |
| 21b. Genericity device (Claim 6.4/6.9) | `Molecular/AlgebraicInduction/` + `Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/` (+ `algebraic-induction.tex`) | ✓ Complete (closed 2026-06-04; see `notes/Phase21b.md`) — the analytic sibling of 21a, scoped out of Phase 21 (risk #4/#7). **Delivered green + axiom-clean:** the **genericity device** `lem:genericity-device` (multivariate Claim 6.4/6.9, route (a) on the `exists_…_polynomial` engine) applied to the varying panel family via the **B0 keystone** `lem:rows-polynomial-in-normals`; the genericity-free accounting iffs `lem:case-I`/`lem:case-II`; the **`V(G)`-relative count bridge N1–N3** + device-to-motive glue N7a; the Case-I splice glue `lem:case-I-splice-seed`; and the reusable Case-II row sub-nodes N7b-0/1/2/3. **The realization producers were re-scoped to Phases 22–23** after a math-first feasibility pass (vs. KT §6.2–6.3): the project's `hsplit` (k=0 degree-2 split, full rank) is **KT Case III** — eq. (6.12) is one row short for k=0 and needs the Lemma 6.10/6.13 redundant-edge row (the blueprint `lem:case-II` "k>0" prose was a conflation, now corrected); and the Case-I splice producer (KT §6.2, full-rank/tractable but research-shaped geometry: the panel-transversality + block-triangular splice) belongs with the realization layer. `thm:theorem-55` / `prop:rigidity-matrix-prop11` / `lem:case-III` flip in 22–23. The green infra (esp. N7b row sub-nodes + N7a + the device) feeds those producers. See `notes/MolecularConjecture.md` *Phase 21b*; `DESIGN.md` *Realization motive must be V(G)-relative* + *Forward-mode reduction chains* + *Genericity device …* + *Constructibility recon before a producer build* + *Phase Case-naming vs. KT's k-bookkeeping*. |
| 22a. Case I realization | `Molecular/Deficiency.lean` + `Induction/` + `AlgebraicInduction/` (extends `algebraic-induction.tex`) | ✓ Complete (green-modulo-22b; see `notes/Phase22a.md`) — Track A only: the Theorem-5.5 **Case I** realization producer the Phase-21b genericity device feeds. The composer `lem:case-I-realization` (`PanelHingeFramework.case_I_realization`) is **green-modulo a single dischargeable hypothesis = KT Claim 6.4** (the new red node `lem:claim-6-4`, deferred to Phase 22b), delivered via the **block-triangular reframe** (KT eq. 6.3 rank-addition over one common framework `ofNormals G ends q₀`, routed through the device's independent-row count — H-block edges ⊔ surviving edges made independent by the exterior-column projection; no common-seed splice). The single deferred obligation is Claim 6.4 (`lem:claim-6-4` = the surviving block's exterior-projected rank at the generic placement). Cross-cutting lesson: a formalization must reproduce the source's argument **structure**, not just its conclusion (`DESIGN.md` *Match the source's argument structure …*). Per-node detail + the superseded hpinc→asymmetric→block-triangular→Qc-non-root design arc: `notes/Phase22a.md`. |
| ⋮ Structure pass (pre-Phase-22b) | `Molecular/{AlgebraicInduction,Induction}/` splits + `algebraic-induction.tex` split | ✓ Complete (see `notes/Phase22-structure.md`) — split the two over-cap Molecular giants into subdirectories (no-hub; the aggregator imports the terminal leaf) and split the large algebraic-induction blueprint chapter, before opening 22b. Pure semantics-preserving moves (`\lean{…}` pins are by-name, so `checkdecls` is unaffected). Done: `AlgebraicInduction/` → 5 files (`PanelLayer`/`Pinning`/`PanelHinge`/`GenericityDevice`/`CaseI`); `algebraic-induction.tex` → thin parent + 5 `\input`s; `Induction/` → 5 files (`Operations`/`SplitOffDeficiency`/`ReducibleVertex`/`Contraction`/`ForestSurgery`). `PERFORMANCE.md` *Post-Phase-8 file-structure audit* records both executed splits; doc/reference surfaces swept to the subdir form. |
| 22b. KT Claim 6.4 (discharge the Case-I green-modulo obligation) | `Molecular/AlgebraicInduction/CaseI.lean` (extends `algebraic-induction.tex`) | ◷ In progress — **paused at the reduction checkpoint** (opened 2026-06-05; reduction N-22b-1/2/3 landed 2026-06-05; see `notes/Phase22b.md`) — KT **Claim 6.4** (`lem:claim-6-4`) is reduced to its single analytic core. The surviving block of `G ＼ E(H)` projected to the surviving columns `V(G)∖V(H)` (via `(extProj V(H)).dualMap`) attaining independent rank `≥ D(|sc|−1)` at the generic locus (KT eqs. (6.5)/(6.9), §5.1) is delivered by two landed bricks — N-22b-2 (bounded `D∘panelRow` packaging `exists_rankPolynomial_of_rigidOn_linking_set_proj`) + N-22b-1 (rank-transport `rigidContract_exterior_rank_transport`, carrying the irreducible algebraic-independence content as the explicit hypothesis `htransport`) — composed by N-22b-3 (the wire-up: `case_I_realization`'s third `hbundle` conjunct reshaped from the packaged `hclaim64` to the narrower `htransport`, the `Qc`-non-root packaging reconstructed in-proof; graph-arg mismatch closes by `panelRow`'s graph-independence). **The reduction does NOT close the phase:** the honesty gate keeps `lem:claim-6-4` red (the `\lean{…}`-pinned but undischarged `htransport` has no node) and `lem:case-I-realization` green-modulo `htransport` (case-(b) pattern). A 2026-06-05 validation pass (design doc §1.18) found discharging `htransport` is tractable and **stays Phase 22b**; the follow-up **T2b math-first re-recon** (design doc §1.19) designed the layer — finding §1.18's planned lower-semicontinuity crux is already green inside N-22b-2, shrinking the cut to a **4-node cut (U1→U2→U3→U4)** with the one research-shaped node re-localized to **U2** (the collapse-relabel projected-row reproduction, KT eq. (6.7)/§1.7). **U1 + U2 are now landed** (the degenerate placement `degeneratePlacement` + the per-edge *row* reconciliation `panelRow_collapseTo_comp_extProj_dualMap`, building on the U2-opening column core `hingeRow_collapseTo_comp_extProj_eq`) — **sound, but a 2026-06-05 course-correction (design doc §1.20, after the U2-opening session forked under backgrounding) found the research-shaped crux was NOT retired by U2, only relocated to U3**: KT Claim 6.4 proper — that the exterior-column projection (dropping the `r`-column) preserves rank `D(|sc|−1)` — is a pin-a-body fact needing a MISSING brick (**U3b**). Corrected cut: **U3a** (alignment transport via the `ends`-swap brick; bricked) + **U3b** (the pin-the-`r`-column projected-rank brick; the genuine Claim 6.4 crux, research-shaped) + **U4** (assemble + flip + phase-close). Next: a math-first U3b recon before building. |
| 22c+. (parked) Case III at `d=3` + `d=3` assembly | `Molecular/AlgebraicInduction/` (extends `algebraic-induction.tex`) | ◷ Planning (renumbered `22b+`→`22c+` in the 22b opening recon, so each sub-letter names one distinct sub-phase; expected to split — 22c = Case III at `d=3` / Track B, the `d=3` assembly its likely further cut, deferred until 22c opens) — the rest of the over-broad Phase-22 territory parked behind 22a/22b: Track B (the Case II/III reducible-vertex producer at `d=3`, KT §6.3 + §6.4.1 — eq. (6.12) degenerate placement, one row short, + Lemma 6.10 Claims 6.11/6.12; nodes `lem:case-II-realization`, `lem:case-III`) and the `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip). Design-pass-first per `notes/Phase22a.md` *Deferred to 22b+ (Case III + assembly)* + `notes/MolecularConjecture.md` *Phase 22* / *Phase 23*. |
| 23–26. Molecular conjecture program (rest) | (none yet — planned) | ◷ Planning (see `notes/MolecularConjecture.md` + §"Phase 17+" below) |

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

**Status (✓ Complete; see `notes/Phase13.md`).** Specialized Phase 12's
matroid-partition theorem to `k` copies of `Graph.cycleMatroid`,
recovering Tutte–Nash-Williams tree-packing (Tutte 1961, Nash-Williams
1961): `Graph.tutte_nash_williams` (a multigraph is the edge-disjoint
union of `k` forests iff it is `(k,k)`-sparse) and the connected-tight
spanning-tree refinement `Graph.isSpanningTreePacking_of_isTight`
(`cor:k-spanning-trees`, Whiteley Thm 13). Introduced a `Graph`-native
`Set`-side `(k,ℓ)`-sparsity/tightness predicate (`Graph.IsSparse` /
`Graph.IsTight`, fresh — **not** migrated from the Phase 9/10
`SimpleGraph` sparsity; see `DESIGN.md` *Migrating Phases 1–11 …* and
*Set/Finset and rank-flavor boundary at the matroid layer (Phases
13–15)*) and a thin rank adapter (`Matroid.Union_pow_rank_eq`,
`Union_pow_indep_iff_count`) bridging the partition formula to the
`k`-fold `cycleMatroid` case. Carrier: mathlib core `Graph α β`.
Per-node lemma map + decisions: `notes/Phase13.md` and the
*Tree-packing as a corollary* subsection of `body-bar.tex`. Unblocks
Phase 14 (`k`-frame matroid = `k`-fold cycle-matroid union).

### Phase 14 — k-frame matroid = k-fold cycle-matroid union

**Status (✓ Complete; see `notes/Phase14.md`).** Whiteley 1988 Theorem 1:
the generic `k`-frame matroid `F(G,X)` on a multigraph (a linear matroid
via `Matroid.ofFun` over indeterminate coefficients
`KFrameField β k = FractionRing (MvPolynomial (β × Fin k) ℚ)`) equals the
`k`-fold union of `Graph.cycleMatroid`, restricted to `E(G)`:
`Graph.kFrameMatroid_eq_unionPow_cycleMatroid`. Whiteley §2.1's genericity
argument runs as a rank count forward (`Graph.forest_count_of_linearIndepOn_kFrameRow`)
and a forest-packing block-diagonal specialization reverse
(`Graph.linearIndepOn_kFrameRow_of_isSparse_restrict`); the two halves package
into the count bridge `Graph.kFrameMatroid_indep_iff_isSparse_restrict`, which
matches Phase 13's `unionPow_cycleMatroid_indep_iff_isSparse_restrict` by
`Matroid.ext_indep`. The `↾ E(G)` is forced: the vendored `Matroid.Union` has
ground `univ : Set β`, so the bare equality is unprovable (the matroids agree on
independent sets but the union carries every non-edge as a loop). Carrier:
mathlib core `Graph α β`. Bridges Phase 12's abstract union to the body-bar
realizations of Phase 15. Per-node lemma map + decisions (incl. the coefficient
encoding and the ground-set restriction): `notes/Phase14.md` and the
`sec:body-bar-k-frame` dep-graph of `body-bar.tex`. Unblocks Phase 15.

### Phase 15 — Body-bar Tay theorem (existence form)

**Status (✓ Complete; see `notes/Phase15.md`).** The original Phase-12
target, unblocked by the Phase 12–14 chain. Tay's theorem in the
existence-of-realization form (Whiteley 1988 Theorem 8, Tay 1984): for
`d = bodyBarDim n = n(n+1)/2`, a multigraph `G` carries an independent
body-bar framework in `ℝⁿ` iff `G` is `(d,d)`-sparse, and an isostatic
one iff `(d,d)`-tight — `Graph.BodyBarFramework.tay_witness`, the iff of
the standard-basis witness (`exists_isIndependent_of_isSparse` /
`exists_isIsostatic_of_isTight`, via `tutte_nash_williams` +
block-diagonal rank count `stdFramework_finrank_range`) with the
converse (`isSparse_of_isIndependent`). The converse is the body-bar
analogue of Phase 6's `isSparse_of_edgeSetRowIndependent_dim_two`: the
block-diagonal rank upper bound `finrank_rigidityRow_span_le`
(`finrank (span (rows on E')) ≤ d·r(E')`, the real specialization of
Phase 14's `forest_count_of_linearIndepOn_kFrameRow`, via a general-
placement row identity `rigidityRow_eq` factoring each row through
`blockPairing`) plus the cycle-matroid bound `r(E')+1 ≤ |V'|`. Carrier:
mathlib core `Graph α β`; Plücker/two-extensor coordinates handled
inline (degenerate permitted, standard-basis witness only). Whiteley's
"almost all realizations are rigid" irreducible-variety lift is
**deferred** to the body-hinge phase. Forward-mode phase: per-node lemma
map + decisions in `notes/Phase15.md` and the `sec:body-bar-framework` +
`sec:body-bar-tay` dep-graph of `body-bar.tex`.

### Phase 16 — Body-hinge Tay–Whiteley theorem (existence form)

**Status (✓ Complete; see `notes/Phase16.md`).** The natural follow-on
to Phase 15's body-bar Tay theorem. The **body-hinge / panel-hinge
Tay–Whiteley theorem** in `n`-space (Tay 1989, Whiteley 1988),
existence-of-realization form, **via the matroid-union reduction to
Phase 15**: a *hinge* in `ℝⁿ` constrains all but one of the
`δ = bodyBarDim n = n(n+1)/2` relative screw freedoms of the two bodies
it joins, so it behaves like a bundle of `δ−1` coincident body-bars.
The chapter adds *no new linear algebra* — parallel-edge multiplication
`(δ−1)·G` (`Graph.edgeMultiply`, the multiplied graph of Katoh–Tanigawa
2011's molecular conjecture) plus its three transport facts is the only
device; a body-hinge framework on `G` (`Graph.BodyHingeFramework`) is
*defined* as the induced body-bar framework on `(δ−1)·G`
(`toBodyBar`), with independence / infinitesimal rigidity inherited
verbatim. The target `Graph.BodyHingeFramework.body_hinge_tay`: `G`
carries an independent (resp. isostatic) body-hinge framework in `ℝⁿ`
iff `(δ−1)·G` is `(δ,δ)`-sparse (resp. tight), equivalently the
edge-disjoint union of `δ` forests — `edgeMultiply_isSparse_iff`
(`tay_witness` on `(δ−1)·G` transported across the body-hinge ⇔
body-bar bijection `exists_toBodyBar_iff`) composed with
`tutte_nash_williams`. Carrier: mathlib core `Graph α β`;
standard-basis witness only (degenerate permitted), matching Phase 15;
Whiteley's "almost all realizations are rigid" lift remains deferred.
Forward-mode phase. Per-node lemma map + decisions: `notes/Phase16.md`
and the `sec:body-hinge` dep-graph of `body-hinge.tex`.

### Phase 17+ — The Molecular Conjecture program

**Status: Phases 17–19 complete; Phases 20–26 planned.** The
longer-horizon target is the
**molecular conjecture** (panel-and-hinge with hinges at each body
forced concurrent/coplanar; Tay–Whiteley 1984, proved by Katoh–Tanigawa
2011, Discrete Comput. Geom. **45**, 647–700). It is the project's
largest single undertaking — comparable in effort to Phases 1–16
combined — and is scoped as a **10-phase program (17–26)** delivering
the full conjecture *and* its molecule/`G²` application. The
lemma-level breakdown, reuse map, citations, and risk register live in
`notes/MolecularConjecture.md`; this section is the one-paragraph-each
summary.

The proof (KT) splits into a **combinatorial step** (a graph-induction
generating minimal `k`-dof-graphs via splitting-off and rigid-subgraph
contraction; §3–4, Thm 4.9) and an **algebraic step** (a geometric
induction realizing each move at the target rigidity-matrix rank; §5–6,
Thm 5.5 → 5.6). Unlike Phases 15–16 (which defined body-hinge rigidity
*by reduction* to body-bar, standard-basis witness only), the conjecture
forces the **genuine panel-hinge rigidity matrix `R(G,p)`** with real
extensor geometry and honest rank computations on *specific,
non-generic* (coplanar/concurrent) realizations.

Phase map (floor; 18/21/22-23 may each split on contact):

1. **17** — Grassmann–Cayley extensor algebra + the load-bearing
   independence Lemma 2.1 (§2.1). All new linear algebra.
2. **18** — the genuine panel-hinge rigidity matrix `R(G,p)`, rank
   Lemmas 5.1–5.3, and reconciliation with Phase 16's reduction-form
   Prop 1.1 (§2.2–2.4).
3. **19** — `M(G̃)`, `D`-deficiency, `k`-dof / minimal `k`-dof-graphs,
   rigid subgraphs, the def=corank bridge (§2.5, §3). `M(G̃)` is the
   `ℓ=2k=D` boundary regime — the Phase 13/14 `D`-fold graphic union +
   Tutte–Nash-Williams, **not** the `ℓ<2k` `CountMatroid.lean`.
4. **20** — the combinatorial induction: graph operations + forest
   surgery (4.1/4.2) + Theorem 4.9 (§4).
5. **21** — Theorem 5.5 base + Case I (proper rigid subgraph) + Case II
   (`k>0` splitting = Whiteley 1-extension) (§5, §6.1–6.3).
6. **22** — sub-lettered. **22a** = Case I realization (full-rank
   rigid-subgraph splice, §6.2: `lem:case-I-realization`, green-modulo KT
   Claim 6.4). **22b** = KT Claim 6.4 (`lem:claim-6-4`, the discharge of
   22a's green-modulo obligation, §6.2/§5.1). **22c+** = Case III at
   `d=3` (Lemma 6.10: the `D`-candidate-frameworks argument, Claims
   6.11/6.12, the crux, §6.4.1) + the `d=3` assembly
   (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55` flip), parked
   as a single planning placeholder behind 22a/22b (cut into sub-phases
   deferred until 22c opens; renumbered from `22b+` in the 22b opening
   recon).
7. **23** — Case III general `d` (Lemma 6.13) → Thm 5.5 → Thm 5.6 →
   Conjecture 1.2 (§6.4.2, §5.2).
8. **24** — the 3-D generic bar-joint rigidity matroid (linear-matroid
   form; dim-3 specialization of Phase 4/8). *Not* a Laman-3D
   characterization — general 3-D rigidity is open (KT §7).
9. **25** — Crapo–Whiteley projective invariance + the molecule ↔
   hinge-concurrent body-hinge ↔ panel-hinge modelling equivalence
   (§1.2).
10. **26** — Corollary 5.7 (`r(G²) = 3|V| − 6 − def(G̃)`), the
    protein-flexibility / pebble-game-validity capstone.

**Phase 17 is complete** (work log: `notes/Phase17.md`; forward-mode
chapter: `blueprint/src/chapter/molecular.tex`). It formalized the
Grassmann–Cayley / extensor-algebra layer (KT §2.1) in
`Molecular/Extensor.lean` end to end: homogeneous coordinatization, the
affine-independence ↔ top-extensor bridge, the symbolic extensor/join on
mathlib's `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)` (`ExteriorAlgebra.ιMulti` +
exterior product), the coordinatized Plücker bridge (`pluckerCoord` /
`pluckerVector`, signed `j×j`-minor vectors with KT's sign), the
affine-subspace extensor `C(·)`, and **Lemma 2.1** — the independence of
the `D = (d+1 choose 2)` many `(d−1)`-extensors of `d+1` affinely
independent points (`omitTwoExtensor_linearIndependent`), on which the
conjecture's hardest case (Case III, Phases 22–23) bottoms out. Phases
20–26 remain planned — see `notes/MolecularConjecture.md` for the
per-phase detail and the reuse map.

### Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (KT §2.2–2.4, §5 prep)

**Status (✓ Complete; see `notes/Phase18.md`).** Stratum 2 of the
molecular-conjecture program: the **genuine** panel-hinge / body-hinge
rigidity matrix `R(G,p)` (`Molecular/RigidityMatrix.lean`), building on
Phase 17's extensors and superseding Phase 16's reduction-only
`BodyHingeFramework` as the rank form. A body-hinge framework `(G,p)`
assigns a `(d−2)`-affine hinge to each edge; its supporting
`(d−1)`-extensor `C(p(e))` constrains the screw centers (carried as the
degree-`k` graded piece `⋀^k ℝ^(k+2)`, `finrank = D` via
`screwSpace_finrank`) by `S(u) − S(v) ∈ span C(p(e))`. Landed basis-free:
the hinge constraint + dual-annihilator row block + null space
`Z(G,p) = infinitesimalMotions`; the trivial-motion layer with the
`D`-dimensional + `D·|V|` numeric counts (the codimension form of
`rank R ≤ D(|V|−1)`); and the three rank lemmas — 5.1 pin-a-body
(`finrank_pinnedMotions_add_screwDim`, the [29] fact *proved* via the
relative-screw normalization), 5.3 parallel-hinges-full
(`eq_of_hingeConstraint_two_parallel`, the `|V|=2` base case), 5.2
rotation semicontinuity (`finrank_infinitesimalMotions_le_of_span_le`,
span-refinement monotonicity, genericity over analytic perturbation). The
KT Prop 1.1 reconciliation (`prop:rigidity-matrix-prop11`, reconcile the
rank form with Phase 16's `thm:body-hinge-tay`) was originally deferred to
Phase 19; at Phase-19 close it was **relocated forward to Phase 21+** — its
matroidal half (`def(G̃) = corank M(G̃)`) landed green in Phase 19, but its
analytic half (`rank R(G,p) = D(|V|−1) − def(G̃)`) depends on the Claim 6.4
generic-rank argument and lands with the algebraic induction. Forward-mode
(the dep-graph is `rigidity-matrix.tex`'s `sec:molecular-rigidity-matrix`;
the post-Phase-18 cleanup round split the former `molecular.tex` into
`extensor.tex` (Phase 17) + `rigidity-matrix.tex` (Phase 18), one `.tex` per
molecular phase). Per-lemma detail + decisions: `notes/Phase18.md`; the
relocated node is a Phase-21+ deliverable in `notes/MolecularConjecture.md`.

### Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (KT §2.5, §3)

**Status (✓ Complete; see `notes/Phase19.md`).** Stratum 3 of the
molecular-conjecture program: the combinatorial / matroidal substrate
the algebraic induction (Phases 21–23) runs against. In a new file
`Molecular/Deficiency.lean`, the matroid `M(G̃)` (the `(D,D)`-count
matroid of `G̃ = (D−1)·G` at the **boundary regime `ℓ = 2k = D`** — the
`D`-fold graphic-matroid union of Phases 13/14 + Tutte–Nash-Williams,
**not** the `ℓ<2k` `CountMatroid.lean`), the `D`-deficiency
`def(G̃) = maxₚ [D(|P|−1) − (D−1)·d_G(P)]`, the `k`-dof / minimal-`k`-dof
hierarchy, rigid + proper rigid subgraphs (KT Lemmas 3.1/3.3/3.4), and
the **def = corank bridge** `|B| + def(G̃) = D(|V|−1)` (project framing
of Jackson–Jordán 2009 Thm 6.1 / Cor 6.2, proved in-repo axiom-free via
weak duality + the Edmonds-optimal-`Y₀` reverse). The bridge is the
matroidal half of KT Prop 1.1 (reconciling the honest rank form with
Phase 16's reduction form); the analytic half (`rank R(G,p) = D(|V|−1) −
def(G̃)`) relocated forward to the algebraic-induction phases (21+).
Forward-mode; dep-graph `deficiency.tex` `sec:molecular-deficiency`.
Per-node lemma map + decisions: `notes/Phase19.md`. Unblocks Phase 20
(combinatorial induction → Theorem 4.9).

### Phase 20 — Combinatorial induction → Theorem 4.9 (KT §3.4–3.5, §4)

**Status (✓ Complete; see `notes/Phase20.md`).** Stratum 4 of the
molecular-conjecture program: the **combinatorial** half of
Katoh–Tanigawa's proof, landed in `Molecular/Induction/`. The
graph operations on `Graph α β` (vertex removal, splitting-off at a
degree-2 vertex, edge-splitting, rigid-subgraph contraction), the
KT 3.4/3.5 chain (rigid-subgraph form of circuits; contraction
preserves minimality — the Case I engine), the dof-tracking bounds
(KT 4.3–4.5) and the reducible-vertex / reduction-step lemmas (KT
4.6–4.8), and the capstone **Theorem 4.9** `Graph.minimal_kdof_reduction`
(green, axiom-free): every minimal `0`-dof-graph with `|V| ≥ 2` reduces
to the two-vertex double edge, stated as the well-founded induction
principle the reduction dichotomy + vertex-count measure drive. Two
route findings recorded in `notes/Phase20.md`: KT Lemma 4.1 is
over-quantified with a balanced-packing gloss in its proof (formalized
counterexample; routed around via a deficiency-count argument), and KT's
iterated fundamental-circuit swaps for the dof bounds and the
minimality transport are bypassed by partition-count / rank-count
comparisons through the green `def = corank` bridge. The forest-surgery
core (KT 4.1) is off the Theorem-4.9 critical path but fully landed (the
`-split` direction green, balanced-packing gloss discharged as a GAP not
an error); only the edge-splitting inverse KT 4.2 stays a deferred TODO.
Per-node lemma map + decisions + findings:
`notes/Phase20.md`. Unblocks Phase 21 (algebraic induction base +
Cases I & II).

### Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (KT §5, §6.1–6.3)

**Status (✓ Complete, GREEN-modulo-21b; see `notes/Phase21.md`).** Stratum 5
of the molecular-conjecture program: the *algebraic* half of Katoh–Tanigawa's
proof, in a new file `Molecular/AlgebraicInduction/`. Where Phase 20
reduced every minimal `0`-dof-graph to the two-vertex double edge
combinatorially (Theorem 4.9), this phase realizes that reduction at the
rigidity-matrix rank: KT **Theorem 5.5** (`theorem_55`), its base case, **Case
I** (rigid-subgraph contraction + block-triangular gluing, `lem:case-I`),
**Case II** (`k>0` splitting = panel-hinge 1-extension, `lem:case-II`), and the
relocated **analytic half of KT Prop 1.1** (`rigidityMatrix_prop11`,
`rank R(G,p) = D(|V|−1) − def(G̃)`, JJ 2009 Thm 6.1 geometric side; matroidal
half `def = corank` green from Phase 19). The induction runs against the
*same* reduction dichotomy `minimal_kdof_reduction` exposes. Two re-scopes
landed at open (2026-06-03): a **panel layer** (hinge-coplanar body-hinge,
gated on the complete sub-phase **21a** Grassmann–Cayley meet), and the
**genericity scope-out** — the shared analytic crux Claim 6.4/6.9 is its own
sub-phase **21b**, entering each consuming node as an explicit hypothesis
(`hglue`/`hspan`/`hub`/`hgen`) so the surrounding reductions are fully formal
modulo it. The crux **Case III** (`k=0`, no proper rigid subgraph) is deferred
to Phases 22–23. Forward-mode; dep-graph `algebraic-induction.tex`
`sec:molecular-algebraic-induction`. Per-node lemma map + decisions:
`notes/Phase21.md`; `notes/Phase21a.md`; `DESIGN.md` *Panel-hinge =
hinge-coplanar body-hinge* + *Genericity device (Claim 6.4/6.9) is its own
sub-phase (Phase 21b)*; program-level plan in `notes/MolecularConjecture.md`
*Phase 21* / *Phase 21b*.

### Phase 22 — Realization layer (sub-lettered: 22a + 22b + 22c+)

The realization layer re-scoped out of Phase 21b — the Theorem-5.5 case
*producers* the genericity device feeds — was opened as a single Phase 22 on
2026-06-04 and **split into sub-phases the same day** because it over-broadly
bundled three independent bodies of work (Case I; Case III at `d=3`; the `d=3`
assembly). Sub-lettering (22a, 22b, …) keeps the integer phase numbers 23–26
stable. **Structural-edit phase:** no new blueprint chapter; the producer nodes
extend `algebraic-induction.tex`, where they are already stubbed red. The KT math
is worked out in `notes/Phase21b.md` *Finding A/B* — 22a/22b/22c+ formalize it.

#### Phase 22a — Case I realization (KT §6.2) — ✓ Complete (green-modulo-22b)

**Status (✓ Complete, green-modulo-22b; see `notes/Phase22a.md`).** Track A only:
the full-rank Case I realization producer. The composer
`PanelHingeFramework.case_I_realization` (`lem:case-I-realization`) discharges
`theorem_55`'s Case-I branch **green-modulo a single dischargeable hypothesis = KT
Claim 6.4** (the new red blueprint node `lem:claim-6-4`, deferred to Phase 22b) —
the same green-modulo pattern as Phase 21 → 21b. It is delivered via the
**block-triangular reframe**: KT eq. (6.3)'s rank-addition over one common
framework `ofNormals G ends q₀`, routed through the genericity device's
independent-row count (the H-block edges ⊔ the surviving edges made independent by
the exterior-column projection), not a common-seed splice. The one deferred
obligation is Claim 6.4 itself (the surviving block's exterior-projected rank at
the generic placement, KT eqs. (6.5)/(6.9)). The phase's cross-cutting lesson — a
formalization must reproduce the source's argument **structure**, not just its
conclusion — surfaced from the hpinc→asymmetric→block-triangular→Qc-non-root design
arc and is promoted to `DESIGN.md` *Match the source's argument structure, not just
its conclusion*. The full Case-I brick inventory (N4 contraction-minimality bridge,
the N5 splice/seed/rank-polynomial bricks, N6a/N6b/N6c, the two-motive split, the
generic-motive induction G2a–c / G3a–c), the decision history, and the hand-off
(next is the coordinator's Close C — open 22b — and the 22b discharge of Claim 6.4)
live in `notes/Phase22a.md`; dep-graph `algebraic-induction.tex`
`sec:molecular-algebraic-induction`.

#### Phase 22b — KT Claim 6.4 (Case-I green-modulo discharge, KT §6.2/§5.1) — ◷ In progress

**Status (◷ In progress; opened 2026-06-05, opening recon landed 2026-06-05; see
`notes/Phase22b.md`).** Scope: *just* KT Claim 6.4 — the single dischargeable
hypothesis Phase 22a left green-modulo. 22a's composer `case_I_realization` /
`lem:case-I-realization` carries it as `hclaim64`, tracked by the red node
`lem:claim-6-4`. The target is the `Qc`-non-root / exterior-projected-rank form (the
surviving block of `G ＼ E(H)`, projected to the surviving columns `V(G)∖V(H)` via
`(extProj V(H)).dualMap`, attains independent rank `≥ D(|sc|−1)` at a generic locus;
KT eqs. (6.5)/(6.9), §5.1). The **opening recon (landed)** decomposed the verified
discharge path (design doc §1.16) into the node cut: **N-22b-2** (bounded, the *first
buildable* — a `D∘panelRow` variant of `exists_rankPolynomial_of_rigidOn_linking_set`,
feasibility re-verified against the generic engine
`exists_polynomial_ne_zero_of_linearIndependent_at`) → **N-22b-1** (research-shaped —
the rank-transport across the collapse map from the contraction's generic IH via
algebraic independence) → **N-22b-3** (the wire-up that discharges `hclaim64` + the
flip). Same green-modulo → discharge pattern as Phase 21 → 21b; flips `lem:claim-6-4`
green and `lem:case-I-realization` to fully green. The recon also settled the
renumber of the parked Case-III/assembly territory from `22b+` to `22c+` (so each
sub-letter names one distinct sub-phase). Full target + path + KT grounding:
`notes/Phase22b.md`; design doc §1.13–§1.16.

#### Phase 22c+ — (parked) Case III at `d=3` + `d=3` assembly (KT §6.3, §6.4.1) — ◷ Planning

The rest of the over-broad Phase-22 territory, parked behind 22a/22b as a single
light placeholder (renumbered `22b+`→`22c+` in the 22b opening recon, so each
sub-letter names one distinct sub-phase; expected to split into multiple sub-phases
once its shape is clearer — 22c = Case III at `d=3` / Track B, the `d=3` assembly its
likely further cut, deferred until 22c opens): **Track B** — the Case II/III
reducible-vertex producer at `d=3` (`theorem_55.hsplit`, the crux), KT §6.3 +
§6.4.1: the eq. (6.12) degenerate placement gives `+(D−1)`, one short, and
**Lemma 6.10** (Claim 6.11 combinatorial↔linear + Claim 6.12 extensor-span
genericity via Phase-17 Lemma 2.1) supplies the missing row (nodes
`lem:case-II-realization`, `lem:case-III`); plus the **`d=3` assembly**
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip).
Design-pass-first per `notes/Phase22a.md` *Deferred to 22b+ (Case III +
assembly)* and `notes/MolecularConjecture.md` *Phase 22* / *Phase 23*.

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
