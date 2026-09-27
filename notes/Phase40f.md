# Phase 40f — PENCIL-X0 / CONTRACT-R: contraction at a `def₂`-rigid core (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). CONTRACT-R, STEPS'
second group (`notes/Phase40-design.md` §3 STEPS), proved the contraction step at a core of planar
deficiency zero, (MC-59)(d) with (MC-39): if `X₀(G/H)` attains, `X₀(G)` attains, for `H = G[W]`
with `def₂(H) = 0` and `G/H` simple. **Next: STEPS' CHAIN group**, not yet opened — see *Hand-off*.

## Current state

**Closed.** The build (`e267d5fc`) and the close landed. The twelve nodes are green: eight in
`main-component.tex` §`sec:main-component-contract`, `def:pencil-weighted-lifting-system` in its
§`sec:main-component-carrier`, `lem:block-rank-contract` and `lem:rank-polynomial-proj-eval` in
`rigidity-matrix.tex`, and `lem:deficiency-zero-connected` in `deficiency.tex`. The close also
pinned the landed `Graph.rigidContract_vertexSet_ncard` on `lem:pencil-contract-standing`, whose
statement carries the body count. The Lean is `Molecule/Pencil/MainComponent/Contract.lean` (its
module docstring lists the statements), with the general pieces in `Carrier.lean`,
`Molecular/Deficiency.lean`, `CaseI.lean`, `Coupling.lean` and the mirror
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`.

**Headline axioms, re-verified at the close** on 39 declarations: the eighteen
`formalization.yaml` main results, the nineteen pins of the twelve nodes at the build, the
sibling's parent and the mirror lemma. All 39 are exactly `[propext, Classical.choice, Quot.sound]`.
*Measured, script not retained*: one `#print axioms` line per declaration under
`import CombinatorialRigidity`, run with `lake env lean` on the fully built tree (~14 s).

## Architectural choices made up front

- **The route** (the design recon's verdict, compiled at `3caa99c8`; now the *CONTRACT-R done*
  paragraph of `notes/Phase40-design.md` §3 STEPS): one picture `q`, the curve on which the core
  shrinks to `r`'s picture point, the rescaled lifting system `M(t)` with no kernel jump at `t = 0`,
  Cramer's section along `t`, the flat core's rank, the collapsed-placement rank, and the block
  coupling, ending at `Graph.x0Attains_of_exists`.
- **The PI's decisions, verbatim** (2026-09-26; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-26, on the CONTRACT-R design recon's verdict (verbatim answers to the coordinator's questions):
  1. Placement — "Where should the new general pieces live? There are four: the projected rank-polynomial sibling, the block coupling, the weighted lifting matrix, and the laws that def₂ = 0 implies connected and degree ≥ 2.": "Convention everywhere (Recommended)" — each goes beside its definition. The sibling becomes an additive successor in CaseI.lean, with its parent re-proved as a 3-line corollary. The coupling goes in Coupling.lean beside extProj, with the pure linear-algebra lemma in the Mathlib mirror. weightedLiftingMatrix goes in Carrier.lean, and the def₂ = 0 laws are general IsKDof laws in Deficiency.lean.
  2. Hypothesis shape — "What shape should the 'G/H is simple' hypothesis have?": "Let's build this as spiked but leave a TODO for readability / understandability later".
  3. Side claims — "Include (MC-39)'s side claims (H and G/H satisfy (H), G/H is 2-edge-connected, and |V(G/H)| = |V| − |W| + 1) in 40f?": "Include (Recommended)".
  4. CONTRACT-A — "When should the shared part of the assembly be factored out?": "Later, at CONTRACT-A (Recommended)".
  ```
- **Decision 8 (the coordinator's):** one build commit by a fresh opus builder (the `CaseI.lean` /
  `Coupling.lean` edits are the fragile zone), not sliced.

## Lemma checklist

All landed with the standard axioms (*Current state*).

- [x] **General pieces, beside their definitions** (PI decision 1): `Graph.weightedLiftingMatrix`
  → `def:pencil-weighted-lifting-system`; `Graph.connected_of_isKDof_zero` (with the landed
  `Graph.two_le_degree_of_isKDof_zero`) → `lem:deficiency-zero-connected`;
  `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj_eval`, its parent now a
  corollary with an unchanged statement → `lem:rank-polynomial-proj-eval`;
  `PanelHingeFramework.finrank_span_rigidityRows_induce_add_map_extProj_le`, with the mirror
  `Submodule.finrank_add_finrank_map_le_of_le_ker` → `lem:block-rank-contract`.
- [x] **`Contract.lean`**: `M(t)`, the curve and the heights → `def:pencil-contract-lifting-system`;
  (K1), (K2) → `lem:pencil-contract-lifting-kernel`; the core plane →
  `lem:pencil-contract-core-plane`; (K3), (K4) → `lem:pencil-contract-limit`; the core's rank →
  `lem:pencil-contract-core-rank`; the collapsed placement → `lem:pencil-contract-degenerate-rank`;
  the standing facts, with the body count pinned at the close → `lem:pencil-contract-standing`;
  `Graph.X0Attains.of_rigidContract` → `thm:pencil-x0-contract-rigid`.
- [x] **The close** (docs and blueprint only): ROADMAP, the design doc's §3 STEPS, CARRIER entry and
  appendix, the end-to-end re-read, the exposition ledger, the headline axioms, the file-size
  plan; the public surfaces left unchanged (the PI's standing call).
- **Not 40f's, tracked elsewhere:** decision 2's `hatt` TODO, an unchecked item of the design doc's
  §3 STEPS carried past this close (also named in `Contract.lean`'s module docstring).

## Blockers / open questions

- None for 40f. Its one carried item, the `hatt` TODO, is tracked in the design doc (above).

## Hand-off / next phase

**40f is closed. The next group is CHAIN**, the next in the design doc's provisional order (§3
STEPS, *The provisional grouping*: (MC-16)–(MC-19), (MC-134)(a)(b), (MC-169), BASE (MC-21)(a),
chains `k ≥ 5` (MC-20)). It is not yet opened: its open mints the next sub-phase letter and work
log, and the design doc's *Tracked for CHAIN's design pass* item is its first input.

**The two files at the ~1500-line tripwire have a plan, not a split** (both 1 496 lines, both
sectioned). `Contract.lean` splits at CONTRACT-A, along PI decision 4's line (the general pieces to
a shared file), recorded in that group's entry. `Carrier.lean` splits first in whichever commit next
grows it, along its C3–C5′ section headers, recorded in the design doc's CARRIER entry.

## Decisions made during this phase

- **2026-09-26 — the close.** The end-to-end re-read of `sec:main-component-contract` pinned
  `Graph.rigidContract_vertexSet_ncard` on the standing lemma (its body count had no pin, and
  `lem:reduction-measure` gives only `≤`), spelled out the distinct attachments at `r`, called the
  `t = 0` plane of a core body's rows the parallel through `(q_r, 0)`, dropped the core-rank lemma's
  `t ≠ 0` (the Lean has none; admissibility excludes `t = 0`), named Jackson–Jordán's polynomial at
  `H` in the theorem's parameter choice, and said there that no attainment at `H` is needed. One
  exposition-ledger entry, done in place. Public surfaces unchanged (the PI's standing call).
- **2026-09-26 — the build:** the spike transcribed with the PI's placement; the core helpers
  folded into `Graph.isX0Graph_induce_of_deficiency_two_eq_zero`; one flexible `simp` the spike never
  showed (TACTICS-QUIRKS §55); the `rigidContract` defeq trap is TACTICS-QUIRKS §38.
- **2026-09-26 — opened design-first from one opus recon**, whose spike the coordinator re-ran (exit
  0, no `sorry`/`axiom`/`maxHeartbeats`) and whose satisfiability instance it traced by hand (a
  triangle core with the path `1–3–4–0`).
