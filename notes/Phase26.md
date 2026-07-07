# Phase 26 — Corollary 5.7 (the molecule-application capstone) (work log)

**Status:** in progress (opened 2026-07-07).

## Current state

**Next concrete commit:** `lem:molecule-rank-lower-bound` (the ≥ leg) —
compose `exists_molecular_rankHypothesis_generalPosition` on the canonical
`SimpleGraph.shadowGraph` carrier with the square-graph dictionary
(`molecular_finrank_motions_eq_square_ker`) and the genericRank glue
(`finrank_span_rigidityRow_le_genericRank`) to get
`3|V|−6−def(G̃) ≤ r(G²)`.

**Coordinator slot-trace findings (2026-07-07, verified against the landed
sources) — two prerequisites inside the same commit:**

1. **The `hends` slot gap (mechanical fix first).** The dictionary's
   `hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2`
   binds the *same* `ends` as `molecularOfCentres G' ends c`, but
   `exists_molecular_rankHypothesis_generalPosition`'s ∃-statement carries
   only `RankHypothesis ∧ IsGeneralPositionPlacement` — no `hends`
   conjunct. The fact is already in hand inside its proof:
   `PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`
   (`Molecule/Theorem56.lean:210`) returns exactly
   `∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2` as its
   second conjunct, and `Modelling.lean:91/116` binds it as `_hQends` and
   returns `Q.ends` verbatim. Fix: add the third conjunct
   `∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2` to the
   ∃-statement, discharged by the discarded `_hQends`. Statement change ⇒
   per-slice gate: restate the pinned blueprint node
   (`thm:panel-hinge-iff-molecular`, `molecule-modelling.tex`) in the same
   commit.
2. **The row-span ↔ kernel bridge (landed, no new lemma).** To turn the
   dictionary's `finrank ker (G.square.RigidityMap c)` into the glue's
   row-span form: `span_range_rigidityRow` (`RigidityMatroid.lean:296`,
   span of rows = range of `(RigidityMap).dualMap`) +
   `LinearMap.finrank_range_dualMap_eq_finrank_range` (row rank = column
   rank) + `LinearMap.finrank_range_add_finrank_ker` (rank–nullity,
   domain `Framework V 3` of finrank `3|V|`). Note the glue lemma's span is
   over `(⊤).rigidityRow p '' (val ⁻¹' H.edgeSet)` while
   `span_range_rigidityRow` is `Set.range (H.rigidityRow p)` — reconcile
   via `rigidityRow`'s graph-independence per edge (cf.
   `linearRigidityRow_subtype_val`, used the same way in the glue's proof).

Both other leaf-most nodes are now green:

* `lem:square-rank-le-genericRank` —
  `SimpleGraph.finrank_span_rigidityRow_le_genericRank`
  (`GenericRigidityMatroid.lean`): for *any* placement `p` (not necessarily
  generic), the row-span dimension realized at `p` is at most the generic
  rank, via the same `Matroid.Rep.finrank_span_image_eq_rk` row-span
  computation as `genericRank_eq_finrank_span` landing at
  `(linearRigidityMatroid V d p).rk`, then `Matroid.rk_le_iff` +
  `genericRigidityMatroid_indep_iff` to dominate `H.genericRank d`. Dropped
  `def:generic-placement` and `lem:genericRank-eq-finrank-span` from its
  `\uses` — the proof needs neither (works for any placement, and doesn't
  route through the generic-placement row-span identity).
* `lem:molecule-graph-carrier` — `SimpleGraph.shadowGraph` + its four
  properties (`Molecular/Molecule/Carrier.lean`): the canonical shadowing
  multigraph carrier, existence half (F4, resolved — see below). The
  blueprint statement was trimmed to the existence claim; the "well-defined
  invariant" clause moved to a non-`\leanok` remark (not formalized, and not
  needed — the two rank-bound leaves below each fix this one canonical
  carrier, never comparing two different carriers).

The phase assembles Katoh–Tanigawa Corollary 5.7 —
`r(G²) = 3|V| − 6 − def(G̃)` for `G` simple of min degree ≥ 2, `r` the
3-D generic bar-joint rigidity matroid rank (Jackson–Jordán 2008; KT
resolve the conjecture feeding it) — arithmetically from the two Phase-25
links, Theorem 5.6 (Phase 23/22k `d=3`), and the Phase-24 generic matroid.
No new combinatorics: Theorem 5.6's *rank* statement replaces Jackson–Jordán's
whole §3–4 (deficiency induction + independent-cover bounds). See the
assembly plan below and `notes/Phase25-design.md` §2.2/§2.6 (the live contract).

## Architectural choices made up front

- **Forward-mode chapter, all `d = 3`.** `molecule-application.tex` is the
  Phase-26 chapter; every node is dim-3 (the molecule model is `ℝ³`-only).
  Red-node consistency gate ran at open: the five nodes route through the
  same argument their statements claim, and every `\uses` target resolves to
  a green Phase-24/25 node or a green earlier node (no live-route reference
  to a superseded node). The chapter's node decomposition follows
  `notes/Phase25-design.md` §2.2 (the ≥/≤ legs) and §2.6 (consumed shapes).

- **F4 (the carrier bridge) — RESOLVED (existence half).**
  The two Phase-25 endpoints have different carrier shapes:
  `exists_molecular_rankHypothesis_generalPosition` (`Molecule/Modelling.lean`)
  takes `G : Graph α β` directly and returns `ends`; the dictionary
  `molecular_finrank_motions_eq_square_ker` (`Molecule/Dictionary.lean`) takes
  `G : SimpleGraph V` (for `G.square` + its bar-joint `RigidityMap`) **and** a
  `G' : Graph V β` shadowing it via `hshadow : ∀ u v, u ≠ v → ((∃ e,
  G'.IsLink e u v) ↔ G.Adj u v)` + `hends`. The `hcard : 6·(|α|−1) < |β|`
  label supply forbids using `β := Sym2 V` alone (too few labels on a sparse
  graph, e.g. `|V| ≤ 10`) — landed the padded label type
  `Sym2 V ⊕ Fin (6·(|V|−1)+1)`: the `Sym2 V` half tags each edge by its
  endpoint pair (spanning + simple + shadow property free), the `Fin` half is
  pure padding that alone exceeds the bound regardless of `G`'s sparsity.
  `SimpleGraph.shadowGraph` (`Molecular/Molecule/Carrier.lean`) + its four
  properties (`_simple`, `_vertexSet`, `_isLink_iff`, `card_shadowLabel_lt`).
  The "well-defined regardless of carrier" clause (any two shadowing carriers
  agree in deficiency) is **not formalized** — trimmed out of the blueprint
  lemma statement into a non-`\leanok` remark, since the two rank-bound leaves
  below each fix this one canonical carrier throughout and never compare two
  different carriers, so the invariance fact is expository, not load-bearing.

## Assembly plan (the chapter's five red nodes)

All in `blueprint/src/chapter/molecule-application.tex`, dim-3. Leaf order
bottom-up:

- [x] `lem:square-rank-le-genericRank` — **the genericRank glue.** For any
  placement `p`, `rank R(H,p) ≤ genericRank H d` (a `p`-row-independent set
  is independent in `genericRigidityMatroid` via
  `genericRigidityMatroid_indep_iff`, so its size ≤ `rk E(H)`).
  `SimpleGraph.finrank_span_rigidityRow_le_genericRank`,
  `GenericRigidityMatroid.lean`. Leaf-most, graph-free.
- [x] `lem:molecule-graph-carrier` — **F4 + the β-label supply.** See the F4
  pin above. `SimpleGraph.shadowGraph` + properties, `Molecular/Molecule/Carrier.lean`.
- [ ] `lem:molecule-rank-lower-bound` — **the ≥ leg** (`3|V|−6−def ≤ r(G²)`):
  `exists_molecular_rankHypothesis_generalPosition` → dictionary forward
  (`molecular_finrank_motions_eq_square_ker`) → `dim ker R(G²,c) = 6+def`, so
  `rank R(G²,c) = 3|V|−6−def`; then `lem:square-rank-le-genericRank` dominates.
- [ ] `lem:molecule-rank-upper-bound` — **the ≤ leg** (`r(G²) ≤ 3|V|−6−def`):
  at a placement generic ∩ general-position
  (`exists_isGenericPlacement_isGeneralPositionPlacement`, Phase 25),
  `genericRank = rank R(G²,p)` (`genericRank_eq_finrank_span`); dictionary in
  reverse identifies `dim ker R(G²,p)` with molecular `dim Z` (genuine hinges
  from GP distinctness); the genericity-free bound `6+def ≤ dim Z`
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`,
  `lem:trivial-motions-rank-bound`) caps the rank.
- [ ] `cor:molecule-rank-formula` — **Cor 5.7**, the two bounds meet.
  ℤ-valued additive form (`def` is `ℤ`-valued); prose states
  `r(G²) = 3|V| − 6 − def(G̃)`. Attribute the formula to Jackson–Jordán 2008,
  the conjecture-resolution to Katoh–Tanigawa.

## Consumed statement shapes (from Phase 25, green)

- `SimpleGraph.genericRank`, `genericRank_eq_finrank_span`,
  `genericRigidityMatroid_indep_iff` — `GenericRigidityMatroid.lean` (Phase 24).
- `SimpleGraph.exists_isGenericPlacement_isGeneralPositionPlacement`,
  `IsGeneralPositionPlacement` — `GeneralPositionPlacement.lean` (Phase 25).
- `molecular_finrank_motions_eq_square_ker` — `Molecule/Dictionary.lean`.
- `exists_molecular_rankHypothesis_generalPosition` — `Molecule/Modelling.lean`.
- `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  — `AlgebraicInduction/PanelLayer.lean` (`lem:trivial-motions-rank-bound`).
- `Graph.deficiency`, `def:D-deficiency`, `thm:def-eq-corank` — `Deficiency.lean`
  (Phase 19).

## Blockers / open questions

- None: F4 is resolved and all consumed shapes are green and axiom-clean.

## Hand-off / next phase

Phase 26 is the last phase of the molecular-conjecture program (17–26). On
close it discharges KT Corollary 5.7 (`cor:molecule-rank-formula`), completing
the program. Next concrete commit is `lem:molecule-rank-lower-bound` (the ≥
leg): fix `G.shadowGraph` (`Molecular/Molecule/Carrier.lean`) as `G'`, feed
its `hcard`/spanning/`Simple` facts to
`exists_molecular_rankHypothesis_generalPosition` to get `ends, c` at the
target rank, then compose the square-graph dictionary
(`molecular_finrank_motions_eq_square_ker` — needs `hshadow` from
`shadowGraph_isLink_iff` and an `hends` compatibility fact for the specific
`ends` the modelling theorem returns; check that `Q.ends` from
`PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4` already carries
the needed `hends`-shaped field before building one) with
`finrank_span_rigidityRow_le_genericRank` to dominate the generic rank. No
successor phase is planned beyond the program.

Also still open, for a future cleanup round at a phase boundary (not Phase-26
work): the molecular-layer dead-code/liveness sweep deferred from
`notes/Phase23-cleanup.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- Chapter opened forward-mode with five red nodes; the ≥/≤-leg decomposition
  and the F4 pin are recorded above.
- `lem:square-rank-le-genericRank` landed as
  `SimpleGraph.finrank_span_rigidityRow_le_genericRank` in
  `GenericRigidityMatroid.lean` (Phase 24's file — the lemma is graph-free,
  no molecular machinery). The proof re-derives `genericRank_eq_finrank_span`'s
  row-span computation for the *specific* (possibly non-generic) placement's
  `linearRigidityMatroid`, landing at that matroid's own `rk`, then closes the
  gap to `genericRigidityMatroid`'s `rk` via `Matroid.rk_le_iff` +
  `genericRigidityMatroid_indep_iff` (every subset independent at a specific
  placement is independent in the generic matroid, so its `rk` dominates).
- `lem:molecule-graph-carrier` landed in a new sibling file
  `Molecular/Molecule/Carrier.lean` (not `Deficiency.lean`, despite owning
  `deficiency`'s consumer-facing invariant remark — the construction is a
  `SimpleGraph`-to-`Graph` bridge specific to the molecule-application
  chapter, not a fact about `deficiency` itself) as `SimpleGraph.shadowGraph`
  + four properties, direct `Graph` structure literal (mirroring
  `edgeMultiply`/`singleEdge`'s style rather than reaching for the vendored
  `Graph.OfSimpleGraph`, which uses `β := Sym2 V` alone and so cannot meet
  the label-count bound). Trimmed the blueprint lemma statement to the
  existence claim only and moved the invariance clause to a non-`\leanok`
  remark (see the F4 pin above) rather than formalizing "any two carriers
  agree" — the successor leaves fix one carrier throughout, so that fact is
  expository, not load-bearing, and skipping it kept the leaf to one sitting.
