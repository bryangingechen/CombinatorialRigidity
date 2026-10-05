# Phase 40j — PENCIL-X0 / SPLITOFF: splitting off a body of degree two at non-adjacent neighbours (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). SPLITOFF, STEPS' sixth
group (`notes/Phase40-design.md` §3 STEPS), proved the split-off step at a body `x` of degree two
whose neighbours `a ≁ b`, the one-body ear `a − x − b` on `V₁`: if `X₀` attains at
`G″ = G.splitOff (x 0) a b (e 0)` (`G` with `x` suppressed) and
`deficiencyMerged₃(G[V₁]; a, b) + 5 ≤ def₃(G[V₁])` (Step MC11's `δ ≥ 5`), then `X₀(G)` attains
((MC-31)). No new mathematics. Phase 40 continued with **CONTRACT-A** (`notes/Phase40k.md`,
closed 2026-09-28) and on through the phase's own close, 2026-09-29
(`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Two build commits (B1 `0fdf5d5a`, B2 `2fc2c02c`) and the close landed. The five nodes
of `main-component.tex` §`sec:main-component-splitoff` are green — `lem:pencil-curve-limit`,
`lem:pencil-splitoff-special-rank`, `lem:pencil-splitoff-flexes`, `lem:pencil-splitoff-curve` and
`thm:pencil-x0-splitoff` — with two unpinned remarks (the exposition-ledger entry, and (MC-31)'s
bound within one for `δ ≤ 4`, not formalized). The Lean is
`Molecule/Pencil/MainComponent/SplitOff.lean`, importing `Orbit.lean` only, with the general
pieces in `Bridge.lean`, `Ear.lean`, `Cut.lean`, `Carrier.lean` and the mirror
`MvPolynomial.polynomial_eval_aeval` (`Mathlib/Algebra/MvPolynomial/Polynomial.lean`,
upstream-eligible). Headline axioms were re-verified at the close on 26 declarations (the
eighteen `formalization.yaml` main results and the eight pins of the five nodes), all exactly
`[propext, Classical.choice, Quot.sound]`.

**Satisfiability** (not landed, kernel-checked in the recon's instance spike): `C₇` with ear
`6 − 0 − 1`, `def₃(P₆) = 5` with merged value `0`. **Faithfulness** (against (MC-31)): `hδ` is
literally Step MC11's `δ ≥ 5`; (H) is asked at `G` only, as in 40g–40i.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read added the remark after the theorem: the curve ends at
  the general picture, so no geometry of the main component is used.
- **The route** (the recon's verdict, 2026-09-28, under the PI's session-start "follow
  precedent"): (MC-28) as a count of motion spaces, (MC-29) as two landed deficiency lemmas
  composed, (MC-30)(i) as a dimension count on the lifting system's kernel, then a polynomial line
  of pictures and flexes back to a main picture and the curve-limit lemma. Three carrier-forced
  proof-level deviations (recorded in the blueprint proofs): the flexes of `G′` are the lifting
  system's kernel, not `L_{G′}`; the special point is not admissible, so the curve is necessary;
  the workbook's rational `P(t)` is a polynomial line. No new mathematics, so 40j opened directly
  (the 40f/40g/40i precedent).
- **The cleanup-round item** (call 9; `span_supportExtensor_ofNormals_eq` in place of the
  orientation split inlined in `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr`,
  `Cut.lean`): paid by round 1, task 13 (`a0dda000`).

## Hand-off / next phase

**40j is closed.** Phase 40 continued with **CONTRACT-A** (`notes/Phase40k.md`, closed
2026-09-28) and on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3
carries the full layer list and proof map, ROADMAP §40 the final state.
