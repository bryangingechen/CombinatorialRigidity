# Phase 26 — Corollary 5.7 (the molecule-application capstone) (work log)

**Status:** in progress (opened 2026-07-07).

## Current state

**Next concrete commit:** `lem:molecule-rank-upper-bound` (the ≤ leg) —
choose a placement `p` simultaneously generic and in general position
(`exists_isGenericPlacement_isGeneralPositionPlacement`), identify
`genericRank = rank R(G²,p)` (`genericRank_eq_finrank_span`), run the
dictionary in reverse to identify `dim ker R(G²,p)` with the molecular
motion-space dimension, and cap it below via the genericity-free bound
`screwDim_add_deficiency_le_finrank_infinitesimalMotions`.

**Coordinator slot-trace (2026-07-07, verified against the landed
sources) — one new small brick inside the same commit:**

- Unlike the ≥ leg, no producer supplies `ends` here: the leaf must
  *construct* an endpoint selector for `G.shadowGraph` and discharge
  **both** of two per-label conditions. (i) The dictionary's `hends`
  (record every link): for a linked label `Sum.inl s(u,v)` choose that
  pair (classical choice from the link; `eq_or_eq_of_isLink_of_isLink`
  makes any linked pair work up to swap). (ii) The genericity-free
  bound's `hC : ∀ e, supportExtensor e ≠ 0` quantifies over **all**
  labels **including the `Fin` padding summand** (never linked) — so
  padding labels must also be assigned *distinct-endpoint* pairs. This
  is satisfiable: `hmin : ∀ v, 2 ≤ G.degree v` forces `3 ≤ |V|`, so a
  distinct pair exists to assign; general position makes the placement
  injective, so distinct endpoints give distinct centres and hence a
  nonzero line extensor (cf. how the dictionary's proof derives
  `c u ≠ c w` from `hgp.injective`). Check what
  `molecularOfCentres`'s `supportExtensor` unfolds to on a never-linked
  label before writing the nonzero proof.
- `screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (`AlgebraicInduction/PanelLayer.lean:2083`) takes `[Nonempty α]
  [Finite α] [Finite β]`, a `BodyHingeFramework k α β`, and `hC`;
  conclusion `(screwDim k : ℤ) + F.graph.deficiency (k+1) ≤ finrank
  F.infinitesimalMotions` — at `k = 2` this is exactly `6 + def(G̃) ≤
  dim Z` (`screwDim 2 = 6` by `decide`, as in the ≥ leg).
- The rank side reuses the ≥ leg's bridges: `genericRank_eq_finrank_span`
  at the generic placement + `span_range_rigidityRow` +
  `LinearMap.finrank_range_dualMap_eq_finrank_range` + rank–nullity
  (`Framework.finrank`), with `rigidityRow_congr` reconciling the two row
  families; close the ℤ-arithmetic by `omega` over named atoms (the ≥
  leg's TACTICS-QUIRKS §77 rw-trap applies verbatim).

**Landed this commit:** `lem:molecule-rank-lower-bound` (the ≥ leg) as
`SimpleGraph.molecule_rank_lower_bound` (`Molecular/Molecule/Application.lean`),
composing the shadowing carrier (F4) with the (now `hends`-carrying)
Theorem-5.6 producer, the square-graph dictionary, and the domination
bound. The two coordinator-flagged prerequisites are discharged in this
commit: the `hends` slot gap (added as a third ∃-conjunct to
`exists_molecular_rankHypothesis_generalPosition`, `Modelling.lean`,
discharged by the previously-discarded `_hQends`; restated the pinned
`thm:panel-hinge-iff-molecular` node in the same commit per the per-slice
gate) and the row-span ↔ `RigidityMap`-range bridge (two new lemmas,
`SimpleGraph.rigidityRow_congr` in `RigidityMatroid.lean` and
`SimpleGraph.finrank_range_rigidityMap_le_genericRank` in
`GenericRigidityMatroid.lean`, giving `lem:molecule-rank-lower-bound`'s
proof a direct `rank R(H,p) ≤ genericRank H d` it can rank-nullity
against). `molecule_rank_lower_bound` adds `[Nonempty V]` to the blueprint
statement's "finite vertex set" (ambient — matches
`thm:panel-hinge-iff-molecular`'s own "≥ 1 body" hypothesis, which its
proof route needs).

Both other leaf-most nodes are green (landed in the prior commit):

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
- [x] `lem:molecule-rank-lower-bound` — **the ≥ leg** (`3|V|−6−def ≤ r(G²)`):
  `exists_molecular_rankHypothesis_generalPosition` → dictionary forward
  (`molecular_finrank_motions_eq_square_ker`) → `dim ker R(G²,c) = 6+def`, so
  `rank R(G²,c) = 3|V|−6−def`; then `lem:square-rank-le-genericRank` dominates
  (via the new `RigidityMap`-range restatement
  `finrank_range_rigidityMap_le_genericRank`). `SimpleGraph.molecule_rank_lower_bound`,
  `Molecular/Molecule/Application.lean`.
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
the program. Next concrete commit is `lem:molecule-rank-upper-bound` (the ≤
leg): fix a placement `p : V → ℝ³` simultaneously generic for row
independence and in general position
(`exists_isGenericPlacement_isGeneralPositionPlacement`), use
`genericRank_eq_finrank_span` to identify `G.square.genericRank 3` with
`rank R(G²,p)`, run `molecular_finrank_motions_eq_square_ker` in reverse
(`hends` now free-standing per this commit's `Modelling.lean` fix, no need to
rebuild it) to identify `dim ker R(G²,p)` with the molecular framework's
`dim Z` on `G.shadowGraph` at `p` (genuine hinges from GP-distinctness of the
centres), and cap `rank R(G²,p)` below via the genericity-free bound
`screwDim_add_deficiency_le_finrank_infinitesimalMotions` (`6+def ≤ dim Z`).
Land as `SimpleGraph.molecule_rank_upper_bound`, same file as the ≥ leg. No
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
- `lem:molecule-rank-lower-bound` landed as `SimpleGraph.molecule_rank_lower_bound`
  in a new file `Molecular/Molecule/Application.lean` (dedicated home for the
  molecule-application chapter's own composite lemmas, mirroring how
  `Carrier.lean` got its own file for F4). Two reusable bridge lemmas landed
  alongside it in their defining files (per the "add lemmas where the
  definition lives" convention): `SimpleGraph.rigidityRow_congr`
  (`RigidityMatroid.lean` — a rigidity row's value doesn't depend on which
  graph's edge set packages it) and `SimpleGraph.finrank_range_rigidityMap_le_genericRank`
  (`GenericRigidityMatroid.lean` — the `RigidityMap`-range restatement of
  `finrank_span_rigidityRow_le_genericRank`, reconciling a subgraph's own row
  family with the ambient `⊤`-restricted one via `rigidityRow_congr`).
  Hit one friction point closing the final arithmetic: `rw`-ing `screwDim 2 =
  6` / `Nat.card V = Fintype.card V` into place broke ("motive is not type
  correct") because both literals also occur inside `G.shadowGraph`'s
  label-type index elsewhere in the same goal; dropping the `rw`s and handing
  the raw equalities straight to a single `omega` call sidestepped it.
  **Lifted to:** TACTICS-QUIRKS § 77 / FRICTION [idiom].
