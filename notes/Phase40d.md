# Phase 40d — PENCIL-X0 / BRIDGE: Jackson–Jordán's equality (work log)

**Status:** in progress (opened design-first 2026-09-26). BRIDGE proves Jackson–Jordán's equality
`dim L(q) = 3 + def₂(G)` at the generic picture of every simple graph with `|N[v]| ≥ 3`, over
every infinite field and with no hypothesis on the edge labels, and `X₀` attaining when
`def₂ = def₃`. The spike is sorry-free, so the build is transcription. **Next: the build
commit** — see *Hand-off*.

## Current state

**Opened.** `main-component.tex` §`sec:main-component-jj` carries five red nodes and one fmlnote,
with the informal statements from `ledger.py --brief '(MC-4)' '(MC-5)' '(MC-33)'` and the new
(MC-172). No Lean has landed yet. **The next concrete commit is the build**: the recon's spike
becomes `Molecule/Pencil/MainComponent/Bridge.lean` (new, root import), and the five nodes get
their `\lean{}` pins and turn green.

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

Planned names; the spike compiles them all (`lake env lean`, exit 0, standard axioms).

- [ ] **Rescaling**: `panelSupportExtensor_smul_right`,
  `PanelHingeFramework.supportExtensor_ofNormals_smul`,
  `PanelHingeFramework.infinitesimalMotions_ofNormals_smul`,
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul` → `lem:pencil-jj-rescale`.
- [ ] **The chart**: `Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint`
  → `lem:pencil-jj-chart`.
- [ ] **Relabelling**: `Graph.embedEdges` with `vertexSet_`, `edgeSet_`, `closedNbhd_`,
  `liftingSpace_`, `finrank_liftingSpace_`, `deficiency_embedEdges`, `embedEdges_isLink`,
  `Simple.embedEdges`, `isAdmissiblePicture_`/`isMainPicture_embedEdges_iff` →
  `lem:pencil-jj-embed-edges`.
- [ ] **The equality**: `Graph.exists_mvPolynomial_finrank_liftingSpace_eq`,
  `Graph.IsMainPicture.finrank_liftingSpace_eq`,
  `Graph.exists_isMainPicture_finrank_liftingSpace_eq`, with the helper
  `Graph.closedNbhd_subset_vertexSet` → `thm:pencil-jj-equality`.
- [ ] **With FLAT**: `Graph.x0Attains_of_deficiency_two_eq_three` → `cor:pencil-jj-flat`.

## Blockers / open questions

- None for BRIDGE. The items the recon moved to other layers are in `notes/Phase40-design.md` §3
  (the cleanup-round checkbox under BRIDGE, the STEPS *Tracked* list, the MOTIVES β-headroom
  bullet).

## Hand-off / next phase

**Next: the build commit.** Transcribe the spike to a new
`Molecule/Pencil/MainComponent/Bridge.lean` (root import after `Flat`), pin and flip the five
`sec:main-component-jj` nodes, and record the headline axioms here. Gates: `lake build`,
`lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`. After the build, the next step is
BRIDGE's close.

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
