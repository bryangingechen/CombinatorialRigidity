# Phase 40c — PENCIL-X0 / FLAT: the flat rank (work log)

**Status:** ✓ complete (opened design-first and closed 2026-09-26). FLAT proved Step MC4/MC5 of
§(K-main): the flat rank `6|V| − 3 − dim L(q)`, the bound `dim L(q) ≥ 3 + def₂`, `def₃ ≤ def₂`, and
"`X₀` attains at the flat witness", all green, with 40a's pin debt paid. Phase 40 continued with
**BRIDGE** (`notes/Phase40d.md`, closed 2026-09-26) and on through the phase's own close,
2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** `main-component.tex` §`sec:main-component-flat` (eight nodes), `lem:deficiency-antitone`
(`deficiency.tex`) and the pin-debt node `lem:relative-deficiency-rank-bound`
(`rigidity-matrix.tex`) are green, in `Molecule/Pencil/MainComponent/Flat.lean` and
`Molecular/Deficiency.lean`, with `linearIndependent_pencilPicturePoint_pair` in `Carrier.lean`.
Headline axioms were re-verified at the close on 38 declarations (the eighteen
`formalization.yaml` main results and the twenty pins of those ten nodes), each exactly
`[propext, Classical.choice, Quot.sound]`.

## Decisions made during this phase

- **2026-09-26 — the recon's route** (coordinator's adjudication; verdict also
  `notes/Phase40-design.md` §3 FLAT): the flat (primal) side, carried to `Graph.X0Attains`'s
  `ofNormals` framework; the split `Λ²K⁴ = W′ ⊕ W_Π` as the linear equivalence `flatScrewEquiv`;
  `F(q)` is `Graph.liftingPlanes`, free off `V(G)`; (MC-4)(a) exact by linear equivalences,
  (MC-4)(b) the grade-1 relative bound at the normals `(x_v, y_v, 1)`, (MC-5)(i) antitone on a
  connected graph (`Deficiency.lean`).
- Consumer shapes: `Graph.x0Attains_of_finrank_liftingSpace_le` ((MC-89) step 3 and CONTRACT's
  "`X₀(H)` attains by FLAT") and `Graph.x0Attains_of_finrank_liftingSpace_eq_three` (THETA,
  (MC-139)).
- **2026-09-26 — the PI's close adjudication, verbatim**: leave the public surfaces (they update
  when Phase 40 as a whole closes).
- **2026-09-26 — the close.** The end-to-end re-read moved "`q` is a main picture" out of
  `cor:pencil-flat-attains`'s statement into its proof (`Graph.closedNbhd_subset_vertexSet` pins).
- **2026-09-26 — the build** (`598f20ce`, one commit, from the recon's spike).
  `Deficiency.lean`'s private walk helper became the public `Graph.ConnBetween.eq_of_forall_isLink`,
  shared with `rk_cycleMatroid_within_parts_le` via
  `Graph.encard_image_le_numberOfComponents_restrict`; three FRICTION idioms filed.
- **2026-09-26 — opened design-first; the opus/fable A/B.** Opus's route adopted (flat side, exact
  (MC-4)(a), exact grade-1 motion equality, (MC-5)(i) proved); fable's cone-side route was
  inequality-only. Merged from fable: the pin-debt scope and the `Φ` citations (Crapo–Whiteley
  1982 Example 4.4, Whiteley 1996 §8.3; not Whiteley 1984, no identity attributed).

## Hand-off / next phase

**40c is closed.** Phase 40 continued with **BRIDGE** (`notes/Phase40d.md`, closed 2026-09-26) and
on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state.
