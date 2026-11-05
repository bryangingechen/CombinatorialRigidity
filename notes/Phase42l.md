# Phase 42l — PD-HEAD: nondegenerate realizations and their lifts in every dimension (work log)

**Status:** in progress, opened 2026-11-04 at the PI's word ("Nondegenerate + lift only", design
doc §1), the first sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the ten red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-nondegenerate` (the definition, its agreement at `d = 3`, linear maps, feasibility in
every dimension) and `sec:pencil-d-lift` (a parametrization in dimension three, lifts, lifts are
nondegenerate, the general lift attains, one lift suffices, lifts restrict to a subgraph), as the
chapter states them. The eleven nodes of `sec:pencil-d-generic`, the generic theorem and the
headline among them, stay red for a later sub-phase at the PI's word, so 42l's close does not close
Phase 42. The open's consistency read passed all ten (*Decisions made*); its questions for the
recon are under *Blockers*. Next (*Hand-off*): the pre-build recon of the ten nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The ten targets, leaf-first, with
the nodes outside them that they rest on:
- *Nondegeneracy.* `def:pencil-d-nondegenerate` on `def:pencil-d-realization`,
  `def:pencil-nondegenerate` and `def:pencil-d-rank-hypothesis`;
  `lem:pencil-d-nondegenerate-three` on `def:pencil-generic-motive`, `lem:pencil-d-agrees-three`,
  `lem:pencil-self-dual`, `lem:screw-map-rows` and `lem:pencil-d-rank-agrees-three`;
  `lem:pencil-d-nondegenerate-maps` on `lem:pencil-d-embed-realization`;
  `lem:pencil-d-nondegenerate-feasible` on those two lemmas, the embedded realization and
  `lem:pencil-d-point-configuration`.
- *The parametrization.* `lem:pencil-d-steer` on the definition, `-nondegenerate-three`,
  `lem:pencil-generic-steer` and `lem:pencil-d-point-configuration`.
- *Lifts.* `def:pencil-d-lift` on `def:pencil-d-embedding`, `def:panel-hinge-framework` and
  `def:rigidity-matrix`; `lem:pencil-d-lift-realization` on point-configuration,
  `-nondegenerate-maps` and `lem:pencil-d-rank-collineation`; `def:pencil-d-lift-attains` on
  `def:D-deficiency`; `lem:pencil-d-lift-one-witness` on the steer lemma, lift-realization,
  `lem:relative-deficiency-rank-bound` and `lem:pencil-x0-fibre-intersection`;
  `lem:pencil-d-lift-transfer` on the steer lemma, lift-realization and fibre-intersection.

Every dependency outside the ten is green. Outside them only `sec:pencil-d-generic` uses any: ten of
its eleven nodes (all but `lem:pencil-d-good-ear`). The chapter is the lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the ten nodes of `-nondegenerate` and `-lift` as
  the chapter states them. PD-HEAD stays the layer's code; its halves are named by their sections,
  `-nondegenerate` with `-lift` (42l) and `-generic` (eleven nodes, no letter), as PD-STEPS's were
  across 42f–42i. 42l's close is an intermediate sub-phase close; the `main_results` row is decided
  at Phase 42's close, with `-generic` (design doc §3).
- **Encoding** as 42b–42k: grade `k = d − 1`, Lean's `m = d − 2`, so `d ≥ 3` is `1 ≤ m`, the
  deficiency at `n = m + 2`. The chapter's lift has `d − 3` new coordinates, `m − 1` at the Lean's
  `m`, inserted before the last coordinate as `gradeEmbed` inserts its zeros.
- **What 42k hands on** (`notes/Phase42k.md` *Hand-off*): `Graph.graded_pencil_realization_theorem`,
  the headline's first two conjuncts, which no node of the ten uses.
- **The standing rule** (design doc §3): the recon and every build add a row to `notes/Cleanup42.md`
  §2 where their Lean departs from the chapter's proof, in the same commit.

## Lemma checklist

- [ ] **Pre-build recon**: the ten spiked against the `d = 3` Lean and the landed carrier, exact
  Lean signatures, their files, and the questions under *Blockers*.
- [ ] `def:pencil-d-nondegenerate`, with feasibility and the generic realization in dimension `d`.
- [ ] `lem:pencil-d-nondegenerate-three`.
- [ ] `lem:pencil-d-nondegenerate-maps`, parts (1) and (2).
- [ ] `lem:pencil-d-nondegenerate-feasible`.
- [ ] `lem:pencil-d-steer`.
- [ ] `def:pencil-d-lift`, the lift space, its trivial lifts and `L(b⁰)`.
- [ ] `lem:pencil-d-lift-realization`, parts (1) to (3).
- [ ] `def:pencil-d-lift-attains`.
- [ ] `lem:pencil-d-lift-one-witness`, parts (1) and (2).
- [ ] `lem:pencil-d-lift-transfer`.
- [ ] **Close** 42l, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`); `-generic` opens after
  it at the PI's word.

## Blockers / open questions

- None blocking the recon. Its questions, from the open's read:
  - **The `d = 3` Lean, file by file.** The definitions are `Pencil/Motive.lean`'s
    `IsNondegPencilRealization` (on `BodyHingeFramework K 2` with normals and points `α → Fin 4 →
    K`), `PencilNondegFeasible` and `HasGenericPencilRealization`; beside them the hub bound
    (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`) and `maps` (2) for linear
    equivalences (`IsNondegPencilRealization.mapExtensor_screwEquivOfLinearEquiv`). The
    parametrization is `lem:pencil-generic-steer`'s Lean: `Chart.lean` (the chart), `Engine.lean`
    (its coordinates as polynomials), `Reseed.lean` (the converse), `Steer.lean` (coordinate points,
    a common seed, the chart's rank), `MainComponent/GenericSteer.lean` (parts (a), (b)) and
    `Witness.lean` (part (a)). The
    polarity is `hasPencilPanelRealization_mapExtensor_screwComplementIso` (`Statement.lean`) with
    42b's `hasPencilPlaneRealization_two_iff` and `hasGradedPencilRealization_two_iff`
    (`Grade/Realization.lean`). No `d = 3` Lean: `maps` (1), the feasibility lemma's projection, the
    lift's four nodes, and the lift parts of one-witness and transfer. `Pair.lean` and `Pair2.lean`
    serve `-generic`.
  - **The chart.** The `d = 3` Lean already pads the normal of a body that is not a hub
    (`pencilChartNormal`, `fillNbr`), which `lem:pencil-d-steer`'s comparison remark says the
    `d = 3` node's proof does not. Its parameters are `hubNormal` and two padding triples a body,
    and the coordinate form (`PencilSeed.ofCoord`) shares one triple between them, where `Γ(G)` has
    `m_v` and five auxiliary vectors. Does the steer lemma pin the `d = 3` chart read through the
    polarity, or a chart on `Γ(G)`? And "Zariski-open" and "general" as a polynomial nonzero
    somewhere on `U(G)`, the form of the `exists_polynomial_ne_zero_of_*` lemmas?
  - **The definition's form.** On a pencil realization at grade `m + 1`
    (`HasPencilPlaneRealization`), whose hinges are multiples of `C(b_u, b_v)`
    (`HasPencilPlaneRealization.supportExtensor_eq_smul_panelSupportExtensor`), or on `(b, Π)` with
    the panel-hinge framework; the third condition as a bound on the dimension of `⨅ w ∈ S, Π_w`.
    The remarks after the definition (the hub bound, openness) and after the steer lemma
    ("general") have no node; their Lean lands with the nodes that cite them.
  - **The lift.** `L(b⁰, Π⁰)` as a submodule, `L(b⁰)` and one-witness's `L̃(b⁰)`; the lift by `0`
    as `gradeEmbed` from grade 2; the rank as that of the panel-hinge framework with normals `b`
    (point-configuration, `finrank_span_rigidityRows_ofNormals_linearEquiv_grade`). The remark after
    `def:pencil-d-lift-attains` that an attaining general lift gives a generic realization has no
    node; `thm:pencil-d-generic` (`-generic`) cites it.
  - **The consumers.** The ten have none outside `-generic`, so their signatures serve a later
    sub-phase: lift-no-rigid reads `L(b⁰) = L(q)` at a configuration and its lift as a
    configuration, ear-free uses the lift and one-witness, ear-extend the steer lemma. Spike each
    signature against those statements too.
  - **Steps the read found implicit** (none a repair): the feasibility lemma's open set for (b) at
    `(v, S)` includes injectivity on the `Π_w`, `w ∈ S`, which its construction gives; one-witness
    (2) applies the steer lemma under the hub bound that feasibility gives; and `maps` (2)'s "in
    particular" is (2) with `d` and `d′` exchanged.
  - **Files.** New `Grade/` file(s), at the recon's choice. A deferral naming a file a build edits
    rides with it (design doc §3).

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice), as `661f0382` (42j) and `3c2f844a` (42k) were. It
spikes the ten against the `d = 3` Lean (*Blockers*) and the landed carrier
(`Pencil/Grade/Realization.lean`, `Embedding.lean`, `Collineation.lean`), pins the ten Lean
signatures and the file plan, each spiked under `lake lean`, settles *Blockers*, and records the
signatures here. Then build leaf-first, roughly 3–5 commits by the coordinator's estimate in the
option the PI chose. Each build adds its node's `\lean{}` and `\leanok`.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42k are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42k.md` *Hand-off* lists 42k's four).
- **After 42l:** `-generic` (11 red nodes, ending in `thm:pencil-d-generic` and the headline
  `cor:pencil-d-conditioned-pair`) opens at the PI's word as a later sub-phase; its close is Phase
  42's, where Tier 0's `main_results` row is decided (design doc §3).

## Decisions made during this phase

- **PI, 2026-11-04 (42l's open):** the PI answered "Nondegenerate + lift only", whose option read:
  "Open on the 10 nodes of -nondegenerate and -lift (roughly 3–5 builds, my estimate). The 11
  generic nodes and the headline would wait for a later sub-phase." The question as put, the other
  options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): the build estimates are the
  coordinator's; the counts and the sections' descriptions hold, with qualifiers (`-generic`'s "the
  reduction's cases" only loosely); the line counts are the three whole files, which serve
  `-generic` (`Pair.lean`, `Pair2.lean`) or are one of six files of the `d = 3` parametrization
  (`Steer.lean`); no node of the ten uses a node of `-generic`, so the split is consistent.
- **Consistency read at the open:** all ten PASS, each read in full against the nodes it cites; no
  wording needs a repair. With every `\uses` parsed whole, the 18 outside dependencies (8
  definitions, 10 lemmas; 18 with the `\cref`s) are green, proofs too, none superseded. From
  `sec:pencil-d-induction` on, 62 nodes, 21 red, all in PD-HEAD (recounted).
- **The read's checks, re-derived:** three, `dim ⋂ n_w^⊥ = 4 − dim span(n_w)`; feasible,
  `πΠ_w = Ke₄ ⊕ π̄A_w` (meets in dimension 2 or 1), and the bad `c` in finitely many proper
  subspaces and the quadric `det[u, u′] = 0`; steer, `b⁰_w · n_v = 0` by hub or not; lift (3),
  hinges scaled by `c_u c_v`; one-witness, `N = c − |J|` Cramer vectors; transfer, a body of degree
  at most one in `H` is no hub, so its subspace enters no condition.
