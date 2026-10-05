# Phase 40a — PENCIL-X0 / SPINE2: the Katoh–Tanigawa spine at `n = 2` (work log)

**Status:** ✓ complete (opened and closed 2026-09-25). A **structural edit**: the landed Theorem
5.5/5.6 chain, the generic-lift rank theorems and the molecular conjecture (simple and multigraph)
weakened their dimension floor in place, from `6 ≤ Graph.bodyBarDim n` to `3 ≤ Graph.bodyBarDim n`
and from `hd : 3 ≤ n` to `2 ≤ n`; one triangle case was repaired; and the non-spanning row-rank
form of Theorem 5.6 landed. They hold at `n = 2`, the planar case (Jackson–Jordán's pin-collinear
theorem), over every infinite field. Phase 40 continued with **CARRIER** (`notes/Phase40b.md`,
closed 2026-09-26) and on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md`
§3, ROADMAP §40).

## Current state

**Closed.** Slices 1–5 landed: the floor weakening across `AlgebraicInduction/Theorem55.lean` and
`GenericLift/`, the Slice-4 non-spanning row-rank form BRIDGE consumes
(`PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`), and the
close's public-surface update. Headline axioms were re-verified at the close on 25 declarations —
the seventeen `formalization.yaml` main results, the conditional `pencil_conjecture_of_X0`,
`theorem_55_6_multigraph`, `rigidityMatrix_prop11`, the other restated generic-lift rank theorems,
and the two Slice-4 declarations — each exactly `[propext, Classical.choice, Quot.sound]`.

## Decisions made during this phase

- **2026-09-25 — opened** (PI: weaken in place; a weaker hypothesis is a stronger theorem).
  Verbatim `notes/pencil/adjudications.md`.
- **Slice 1** landed the recon's hunks verbatim (one `case-iii.tex` prose reword, since the proof
  no longer invokes `lem:adjacent-degree-two-pair`).
- **Slices 2–3**, one commit: `Theorem55.lean`'s floor weakening (eight named callers repaired)
  plus `GenericLift/`'s six declarations forced by the same dependency; repairs beyond the recon's
  hunks were `Theorem56.lean`'s `hD` line, `lem:cycle-realization`'s bound `m ≤ k+2`, and
  `lem:case-III`'s proof `\uses` gaining `lem:low-degree-vertex`.
- **Slice 4** (the non-spanning row-rank form) was transcribed verbatim from read-only opus/fable
  spikes; its two follow-ups routed to FLAT and BRIDGE (`notes/Phase40-design.md` §3).
- **2026-09-25 — PIN re-scoped** (PI, at the close, verbatim `notes/pencil/adjudications.md`): to
  formalizing Jackson–Jordán's own pin-collinear proof as a second, independent proof of the
  planar theorem — detail in ROADMAP *Queued* `PIN`.
- **2026-09-25 — the close.** Public surfaces (README, home page, `intro.tex`,
  `formalization.yaml`) restated to `d ≥ 2`, naming the JJ citation (verified against Crossref:
  *Discrete Comput. Geom.* 40(2) (2008) 258–278, doi:10.1007/s00454-008-9100-z).

## Hand-off / next phase

**40a is closed.** Phase 40 continued with **CARRIER** (`notes/Phase40b.md`, closed 2026-09-26)
and on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full
layer list and proof map, ROADMAP §40 the final state.
