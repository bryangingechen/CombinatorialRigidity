# Phase 40f — PENCIL-X0 / CONTRACT-R: contraction at a `def₂`-rigid core (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). CONTRACT-R, STEPS'
second group (`notes/Phase40-design.md` §3 STEPS), proved the contraction step at a core of planar
deficiency zero, (MC-59)(d) with (MC-39): if `X₀(G/H)` attains, `X₀(G)` attains, for `H = G[W]`
with `def₂(H) = 0` and `G/H` simple. Phase 40 continued with **CHAIN** (`notes/Phase40g.md`, closed
2026-09-27) and on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP
§40).

## Current state

**Closed.** The build (`e267d5fc`) and the close landed: twelve nodes green in `main-component.tex`,
`rigidity-matrix.tex` and `deficiency.tex`, in `Molecule/Pencil/MainComponent/Contract.lean` (its
general pieces beside their definitions, PI decision 1: `Carrier.lean`, `Deficiency.lean`,
`CaseI.lean`, `Coupling.lean`, and a mirror in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`). Headline axioms were re-verified at the
close on 39 declarations (the eighteen `formalization.yaml` main results, the nineteen pins and two
more), all exactly `[propext, Classical.choice, Quot.sound]`.

**Since superseded:** round 4 (`40-simplify` tasks 10p `993b9e74`, 10q `91755996`) restated
`Graph.X0Attains.of_rigidContract` (`cor:pencil-x0-contract-rigid`) as an 18-line corollary of
CONTRACT-A, merging the contraction section and deleting the flat-core curve proof this phase built
directly; the curve machinery (`weightedLiftingMatrix`, `M(t)`, `contractLimitMap`, …) persists in
`ContractCurve.lean` (split out at 40k), now backing CONTRACT-A instead. Both ~1500-line-tripwire
files this phase's *Hand-off* planned to split did split later (`Carrier.lean` at 40h's B3,
`Contract.lean` at 40k).

## Decisions made during this phase

- **2026-09-26 — the PI's decisions, verbatim `notes/pencil/adjudications.md`** (on the design
  recon's verdict): **PI decision 1** (placement) — convention everywhere, each general piece beside
  its definition; **PI decision 2** (the `G/H`-simple hypothesis shape) — spiked, with a readability
  TODO (closed at 40l's open, 2026-09-28: `hatt` kept, `notes/Phase40-design.md` §3 STEPS); **PI
  decision 3** ((MC-39)'s side claims) — include; **PI decision 4** (CONTRACT-A's shared-assembly
  factoring) — later, at CONTRACT-A. The coordinator's **decision 8**: one build commit by a fresh
  opus builder.
- **The build.** The spike transcribed with the PI's placement; the core helpers folded into
  `Graph.isX0Graph_induce_of_deficiency_two_eq_zero`; one flexible `simp` the spike never showed
  (TACTICS-QUIRKS §55); the `rigidContract` defeq trap is TACTICS-QUIRKS §38.
- **Opened design-first from one opus recon**, whose spike the coordinator re-ran (exit 0, no
  `sorry`/`axiom`/`maxHeartbeats`) and whose satisfiability instance it traced by hand (a triangle
  core with the path `1–3–4–0`).
- **The close.** The end-to-end re-read pinned `Graph.rigidContract_vertexSet_ncard` on the standing
  lemma, named Jackson–Jordán's polynomial at `H` in the theorem's parameter choice, and three other
  proof-level fixes; one exposition-ledger entry. Public surfaces left unchanged (the PI's standing
  call).

## Hand-off / next phase

**40f is closed.** Phase 40 continued with **CHAIN** (`notes/Phase40g.md`, closed 2026-09-27) and on
through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state.
