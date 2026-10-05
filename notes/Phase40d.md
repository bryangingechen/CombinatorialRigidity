# Phase 40d — PENCIL-X0 / BRIDGE: Jackson–Jordán's equality (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). BRIDGE proved
Jackson–Jordán's equality `dim L(q) = 3 + def₂(G)` at the generic picture of every simple graph
with `|N[v]| ≥ 3`, over every infinite field and with no hypothesis on the edge labels, and `X₀`
attaining when `def₂ = def₃`. Phase 40 continued with **STEPS** (`notes/Phase40e.md` onward) and
on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** The five nodes of `main-component.tex` §`sec:main-component-jj` are green, in
`Molecule/Pencil/MainComponent/Bridge.lean`. Headline axioms were re-verified at the close on 39
declarations (the eighteen `formalization.yaml` main results and the twenty-one pins of the five
nodes); thirty-two are exactly `[propext, Classical.choice, Quot.sound]`, the other seven
(`Graph.embedEdges`, five of its basic lemmas, and `Graph.closedNbhd_subset_vertexSet`) use a
strict subset.

## Decisions made during this phase

- **2026-09-26 — the recon's route** (coordinator's adjudication, one opus pass; verdict also
  `notes/Phase40-design.md` §3 BRIDGE): the chart route — a common non-root of SPINE2's
  non-spanning rank polynomial, the general-position polynomial and `∏ n(a, 2)`, rescaled per body
  into the chart `(x_v, y_v, 1)`, where FLAT reads the rank as `3|V| − dim L(q)`; headroom-free by
  relabelling edges into `β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`); no spanning hypothesis, no
  total selector, no `IsGenericNormals`.
- Consumer shapes: the generic, `ℓ₀` and existential forms; `cor:pencil-jj-flat` (JJ at `G` with
  FLAT).
- **2026-09-26 — the build** (`67d0ad91`, one commit), the spike transcribed verbatim; everything
  stays in `Bridge.lean`; `Graph.embedEdges` filed as a mirror candidate (`notes/FRICTION.md`).
- **2026-09-26 — the close.** The end-to-end re-read added one clause to
  `thm:pencil-jj-equality`'s proof: three members in a closed neighbourhood give the chart lemma's
  two bodies (`Graph.closedNbhd_subset_vertexSet` pins). Public surfaces left unchanged, per the
  PI's standing call from 40c's close.
- **2026-09-26 — opened design-first from one opus recon** (exit 0, no warnings, no `sorry`).
  Accepted: the chart route and the `embedEdges` relabelling; the total-selector open point
  dissolved. Instances: `K₄` on `Fin 4`, its triangle as a non-spanning `H`, and `K₄` contracted at
  the triangle (`rigidContract` keeps parallel edges).
- **2026-09-26 — informal repairs** (`notes/Phase40-design.md` §5): (MC-172) minted in
  `K-main-MC11.md`, with dated appends at (MC-141) and at Step MC5's by-product paragraph.

## Hand-off / next phase

**40d is closed.** Phase 40 continued with **STEPS** (`notes/Phase40e.md` onward, seven groups) and
on through the phase's own close, 2026-09-29 — `notes/Phase40-design.md` §3 carries the full layer
list and proof map, ROADMAP §40 the final state.
