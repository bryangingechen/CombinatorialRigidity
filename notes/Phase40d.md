# Phase 40d — PENCIL-X0 / BRIDGE: Jackson–Jordán's equality (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). BRIDGE proved
Jackson–Jordán's equality `dim L(q) = 3 + def₂(G)` at the generic picture of every simple graph
with `|N[v]| ≥ 3`, over every infinite field and with no hypothesis on the edge labels, and `X₀`
attaining when `def₂ = def₃`. **Next: STEPS**, Phase 40's next layer (`notes/Phase40-design.md`
§3), **not yet opened** — see *Hand-off*.

## Current state

**Closed.** The build (`67d0ad91`) and the close landed. The five nodes of `main-component.tex`
§`sec:main-component-jj` are green, and the Lean is `Molecule/Pencil/MainComponent/Bridge.lean`
(root import; its module docstring lists the statements). Headline axioms were re-verified at the
close on 39 declarations: the eighteen `formalization.yaml` main results and the twenty-one pins
of the five nodes. Thirty-two are exactly `[propext, Classical.choice, Quot.sound]` (the main
results, BRIDGE's seven headlines and seven more pins). The other seven, `Graph.embedEdges`, five
of its basic lemmas and `Graph.closedNbhd_subset_vertexSet`, use a strict subset (*measured, script
not retained*: one `#print axioms` line per declaration under `import CombinatorialRigidity`, run
with `lake env lean` on the built tree).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the BRIDGE design recon (one opus pass; verdict
also in `notes/Phase40-design.md` §3 BRIDGE):

- **The chart route.** A common non-root of SPINE2's non-spanning producer's rank polynomial, the
  general-position polynomial and `∏ n(a, 2)`, rescaled per body into the chart `(x_v, y_v, 1)`,
  where FLAT's bridge reads the rank as `3|V| − dim L(q)`. No spanning hypothesis, no total
  selector, no `IsGenericNormals`.
- **Headroom-free by relabelling** (`Graph.embedEdges` into `β ⊕ Fin (3|α| + 1)`); only the
  chart-rank form carries SPINE2's `hfresh`.
- **Consumer shapes:** the generic form, the `ℓ₀` form and the existential form;
  `cor:pencil-jj-flat` (JJ at `G` with FLAT) is BRIDGE's. The consumer map for STEPS is in
  `notes/Phase40-design.md` §3 BRIDGE.

## Lemma checklist

- [x] **The build** (`67d0ad91`, one commit): the rescaling, chart, relabelling, equality and
  FLAT-corollary declarations. Nodes and names: the five nodes' `\lean{}` pins.
- [x] **The close** (docs only): ROADMAP, the design doc's §3 BRIDGE, the end-to-end re-read, the
  exposition ledger, the headline axioms; the public surfaces left unchanged (the PI's standing
  call).
- [ ] **Cleanup-round items, not BRIDGE's:** the edge-restricted generic-normals row rank and the
  re-base (`notes/Phase40-design.md` §3 BRIDGE); mirroring `Graph.embedEdges` and moving
  `Graph.closedNbhd_subset_vertexSet` beside `Graph.closedNbhd` (`notes/FRICTION.md`).

## Blockers / open questions

- None for BRIDGE. The items the recon moved to other layers are in `notes/Phase40-design.md` §3
  (the STEPS *Tracked* list, the MOTIVES β-headroom bullet).

## Hand-off / next phase

**40d is closed. The next concrete commit opens STEPS design-first** (`notes/Phase40-design.md`
§3 STEPS). It starts from STEPS' pre-build recon over the six §3 STEPS *Tracked* items: from
CARRIER's close, the SPLITOFF curve-limit lemma, the CONTRACT rank-device open point and the
deferred generic-condition API; from BRIDGE's recon, the slice `q′ = (q_O, Q)`, the simplicity of
`G/H` and `h3` from (H). The opening commit mints its letter and its work log (the grouping of
STEPS' steps into sub-phases is decided at the open, §3). BRIDGE's consumer map is in §3 BRIDGE.

## Decisions made during this phase

- **2026-09-26 — the close.** The end-to-end re-read added one clause to `thm:pencil-jj-equality`'s
  proof: three members in a closed neighbourhood give the chart lemma's two bodies (the step
  `Graph.closedNbhd_subset_vertexSet` pins). No new exposition-ledger entries. Public surfaces
  unchanged, per the PI's standing call from 40c's close (they update when Phase 40 closes).
  Project-organization review: no new item; the auto-loaded CLAUDE.md suite is unchanged
  (1 695 lines). `notes/pencil/CLAUDE.md`'s status line still names only `notes/Phase40a.md`
  beside the design doc; left unedited (a CLAUDE.md, and it makes no status claim).
- **2026-09-26 — the build**, one commit, the spike transcribed verbatim. Everything stays in
  `Bridge.lean`; `Graph.embedEdges` is filed as a mirror candidate (`notes/FRICTION.md`).
- **2026-09-26 — opened design-first from one opus recon**, whose instance file the coordinator
  re-ran (exit 0, no warnings, no `sorry`). Accepted: the chart route and the `embedEdges`
  relabelling; the total-selector open point dissolved. Instances: `K₄` on `Fin 4`, its triangle as
  a non-spanning `H`, and `K₄` contracted at the triangle (`rigidContract` keeps parallel edges).
- **2026-09-26 — informal repairs** (`notes/Phase40-design.md` §5): (MC-172) minted in
  `K-main-MC11.md`, with dated appends at (MC-141) and at Step MC5's by-product paragraph.
