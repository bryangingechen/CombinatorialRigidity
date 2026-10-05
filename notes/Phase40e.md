# Phase 40e — PENCIL-X0 / CUT/BRIDGE: cut vertices and bridges (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). CUT/BRIDGE, STEPS' first
group (`notes/Phase40-design.md` §3 STEPS), proved the cut and bridge steps of the `X₀` induction,
the "if" halves of (MC-52) and (MC-53): if `G` satisfies (H) and has a cut vertex or a chain of
bridges of any length, `X₀` attaining at both pieces gives it at `G`. Phase 40 continued with
**CONTRACT-R** (`notes/Phase40f.md`, closed 2026-09-26) and on through the phase's own close,
2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Build 1 (`993ccc41`), build 2 (`c74ea8a1`, then `3d05ecc9` after a recon) and the close
landed. The nine nodes are green, in `Molecule/Pencil/MainComponent/Cut.lean`, with the cut-vertex
laws in `Molecular/Deficiency.lean` and `RigidityMatrix/Bricks.lean`. Headline axioms were
re-verified at the close on 48 declarations (the eighteen `formalization.yaml` main results, the
twenty-eight pins of the nine nodes and two new pins); forty-four are exactly
`[propext, Classical.choice, Quot.sound]`, the other four (`pathVertex` and three basic lemmas) use
a strict subset.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon** (STEPS' pre-build recon, verdicts in
  `notes/Phase40-design.md` §3 STEPS): the step contract (one picture generic for the pieces and
  main for `G`), (H) as `Graph.IsX0Graph`, and BRIDGE for `k ≥ 1` by explicit path hypotheses, not a
  chain structure. The PI's four decisions (2026-09-26, verbatim `notes/pencil/adjudications.md`):
  the ORBIT recon after 40e's build, the provisional grouping, the cut-vertex laws' placement in
  `Deficiency.lean`/`Bricks.lean`, and formalizing only the "if" halves (the "only if" halves an
  unchecked todo, `notes/Phase40-design.md` §3 STEPS).
- **Build 1:** the spike transcribed; the rank identity shortened via two private helpers in
  `Bricks.lean`.
- **Build 2.** The fibre lemma re-derived, not transcribed (one affine extension by `a`'s own
  witness, for every `k`, with no admissibility); then **BRIDGE for every `k`** (`Cut.lean` 411) by
  one cut at the last bridge and a telescope over the prefixes — a recon ruled out an `X0Attains`
  induction (a peeled body has no admissible picture).
- **2026-09-26 — the close.** The end-to-end re-read fixed the body-term count in
  `thm:pencil-x0-bridge`'s proof (`6(k+1)`, not `6k`) and two other proof details; one
  exposition-ledger entry. Public surfaces left unchanged (the PI's standing call).
- **2026-09-26 — the ORBIT recon and its second reading**, both read-only
  (`notes/Phase40-design.md` §4 *ORBIT's dimension counting*): re-proved the cell `k = 2`, `a ≁ b`,
  `δ₂ ≥ 2` without the orbit count, as (MC-173)–(MC-176) in Step MC13; PI D1/D2 accepted it
  (`notes/pencil/adjudications.md`). The second reading found no refutation and no gap, adding
  (MC-177) and (MC-178).

## Hand-off / next phase

**40e is closed.** Phase 40 continued with **CONTRACT-R** (`notes/Phase40f.md`, closed 2026-09-26)
and on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full
layer list and proof map, ROADMAP §40 the final state.
