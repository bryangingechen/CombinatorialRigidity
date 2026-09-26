# Phase 40d — PENCIL-X0 / BRIDGE: Jackson–Jordán's equality (work log)

**Status:** in progress (opened design-first and built 2026-09-26). BRIDGE proves Jackson–Jordán's
equality `dim L(q) = 3 + def₂(G)` at the generic picture of every simple graph with `|N[v]| ≥ 3`,
over every infinite field and with no hypothesis on the edge labels, and `X₀` attaining when
`def₂ = def₃`. All five nodes are green. **Next: BRIDGE's close** — see *Hand-off*.

## Current state

**Built.** `Molecule/Pencil/MainComponent/Bridge.lean` (root import) landed in one commit from the
recon's spike, and the five nodes of `main-component.tex` §`sec:main-component-jj` are green; the
module docstring lists the statements. Headline axioms, measured on the built tree (one
`#print axioms` line per declaration under `import CombinatorialRigidity`, `lake env lean`; *script
not retained*): each of the seven headlines (`finrank_span_rigidityRows_ofNormals_smul`, the chart
form, `deficiency_embedEdges`, the three equality forms, `x0Attains_of_deficiency_two_eq_three`)
is exactly `[propext, Classical.choice, Quot.sound]`, and the other fourteen pinned declarations
use a subset. **The next concrete commit is the close** (docs only).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the BRIDGE design recon (one opus pass;
`notes/Phase40-design.md` §3 BRIDGE):

- **The chart route.** SPINE2's non-spanning producer at `(n, k) = (2, 1)`, its rank polynomial,
  the general-position polynomial and `∏ n(a, 2)` have a common non-root. Per-body rescaling moves
  it into the chart `(x_v, y_v, 1)` at the same rank with nonzero hinges, and the rank polynomial
  there, pulled back along the chart, meets the main pictures. FLAT's bridge then reads the rank as
  `3|V| − dim L(q)`. There is no spanning hypothesis, no total selector and no `IsGenericNormals`.
- **Headroom-free by relabelling** (`Graph.embedEdges`). The equality relabels the edges into
  `β ⊕ Fin (3|α| + 1)`, where `Graph.freshEdgeSupply_of_card_lt (n := 2)` supplies SPINE2's
  `hfresh`; only the chart-rank form carries `hfresh`.
- **Consumer shapes:** the generic form (one nonzero ambient picture polynomial whose non-roots are
  main pictures at `3 + def₂`), the `ℓ₀` form (every main picture) and the existential form.
  `cor:pencil-jj-flat` (JJ at `G` with FLAT) is BRIDGE's, not STEPS'.
- **Deferred:** the edge-restricted generic-normals row rank goes to the post-Phase-40 cleanup round
  (`notes/Phase40-design.md` §3 BRIDGE); three items go to the STEPS pre-build recon (§3 STEPS);
  MOTIVES records that BRIDGE forces no `β`-headroom (§3 MOTIVES).

## Lemma checklist

- [x] **The build** (one commit): the rescaling, chart, relabelling, equality and FLAT-corollary
  declarations → `lem:pencil-jj-rescale`, `lem:pencil-jj-chart`, `lem:pencil-jj-embed-edges`,
  `thm:pencil-jj-equality`, `cor:pencil-jj-flat` (names: the nodes' `\lean{}` pins).
- [ ] **The close** (docs only): ROADMAP (row cell, §40 layer list, compress the §40d
  subsection), the design doc's status line and §3 BRIDGE, the end-to-end re-read of
  `sec:main-component-jj`, the exposition ledger, the headline axioms. The public surfaces stay
  unchanged until Phase 40 closes (the PI's standing call).
- [ ] **Cleanup-round items, not BRIDGE's:** the edge-restricted generic-normals row rank and the
  re-base (`notes/Phase40-design.md` §3 BRIDGE); mirroring `Graph.embedEdges` and moving
  `Graph.closedNbhd_subset_vertexSet` beside `Graph.closedNbhd` (`notes/FRICTION.md`).

## Blockers / open questions

- None for BRIDGE. The items the recon moved to other layers are in `notes/Phase40-design.md` §3
  (the cleanup-round checkbox under BRIDGE, the STEPS *Tracked* list, the MOTIVES β-headroom
  bullet).

## Hand-off / next phase

**Next: BRIDGE's close**, a docs-only commit per `PHASE-BOUNDARIES.md` (intermediate sub-phase
close): mark 40d done in the ROADMAP cell and layer list, compress §40d and the design doc's §3
BRIDGE to verdicts, re-read `sec:main-component-jj` end to end, write the exposition-ledger
entry if any, and re-verify the headline axioms. STEPS opens after that, starting with its
pre-build recon (§3 STEPS *Tracked*).

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its instance
  file (exit 0, no warnings, no `sorry`, the seven headline axioms standard). Accepted: the chart
  route and the `embedEdges` relabelling (the `hfresh`-carrying variant is not landed). The design
  doc's total-selector open point is dissolved by the chart route. Instances: `K₄` on `Fin 4`,
  and its triangle on `{0, 1, 2}` as a non-spanning `H`; `K₄` contracted at the triangle is the
  witness that `rigidContract` keeps parallel edges.
- **2026-09-26 — informal repairs** (`notes/Phase40-design.md` §5): (MC-172) minted in
  `K-main-MC11.md` (the equality over every infinite field, from Katoh–Tanigawa at `d = 2`), with
  dated appends at (MC-141) and at Step MC5's by-product paragraph.
- **2026-09-26 — the build**, one commit, the spike transcribed verbatim (no `#print axioms`).
  Everything stays in `Bridge.lean`: `Graph.embedEdges` is filed as a mirror candidate rather
  than mirrored, since its `Simple` lemma is about the `Matroid` package's `Graph.Simple`.
