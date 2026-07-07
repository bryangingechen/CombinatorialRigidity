# Phase 26 — Corollary 5.7 (the molecule-application capstone) (work log)

**Status:** in progress (opened 2026-07-07).

## Current state

**All five chapter nodes are green** — `cor:molecule-rank-formula`
(Corollary 5.7 itself) landed as `SimpleGraph.molecule_rank_formula`
(`Molecular/Molecule/Application.lean`): the direct `le_antisymm`
combination of the two leg lemmas, no new construction. The corollary's
"generically rigid iff `def(G̃) = 0` iff six edge-disjoint spanning
trees" reading is **not separately formalized** — trimmed to a
non-`\leanok` remark after the node (same move as the carrier-invariance
clause), since no `genericRank` ↔ `IsGenericallyRigid` bridge exists and
the formalized deliverable is the rank formula.

**Next concrete commit:** the phase-close checklist
(`PHASE-BOUNDARIES.md` *When this commit closes a phase*) — closing this
phase completes the 17–26 molecular-conjecture program, so the close also
folds the program's completion into ROADMAP (§17+ preamble + §26), the
user-facing status surfaces (README, home_page, intro.tex), and
`notes/MolecularConjecture.md`.

Nodes landed in prior commits: `lem:molecule-rank-lower-bound` /
`lem:molecule-rank-upper-bound` (`SimpleGraph.molecule_rank_lower_bound` /
`_upper_bound`, `Molecular/Molecule/Application.lean`),
`lem:square-rank-le-genericRank`
(`SimpleGraph.finrank_span_rigidityRow_le_genericRank`), and
`lem:molecule-graph-carrier` (`SimpleGraph.shadowGraph` + four properties,
`Molecular/Molecule/Carrier.lean`).

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
- [x] `lem:molecule-rank-upper-bound` — **the ≤ leg** (`r(G²) ≤ 3|V|−6−def`):
  at a placement generic ∩ general-position
  (`exists_isGenericPlacement_isGeneralPositionPlacement`, Phase 25),
  `genericRank = rank R(G²,p)` (`genericRank_eq_finrank_span`); dictionary in
  reverse identifies `dim ker R(G²,p)` with molecular `dim Z` (genuine hinges
  from GP distinctness); the genericity-free bound `6+def ≤ dim Z`
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`,
  `lem:trivial-motions-rank-bound`) caps the rank.
- [x] `cor:molecule-rank-formula` — **Cor 5.7**, the two bounds meet.
  ℤ-valued additive form (`def` is `ℤ`-valued); prose states
  `r(G²) = 3|V| − 6 − def(G̃)`. Formula attributed to Jackson–Jordán 2008,
  the conjecture-resolution to Katoh–Tanigawa.
  `SimpleGraph.molecule_rank_formula`, `Molecular/Molecule/Application.lean`.

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

All five chapter nodes are green; the phase's mathematical work is done.
The remaining commit is the **phase-close checklist** (`PHASE-BOUNDARIES.md`
*When this commit closes a phase*): ROADMAP row flip + §26 compression (+
§17+ program-preamble completion), user-facing status sync (README,
home_page, intro.tex — reader-facing, jargon-free), `notes/MolecularConjecture.md`
program completion, end-to-end blueprint-chapter re-read +
`BlueprintExposition.md`, note-tail compression, project-organization
review. No successor phase is planned beyond the program.

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
- `lem:molecule-rank-upper-bound` landed as `SimpleGraph.molecule_rank_upper_bound`
  in `Molecular/Molecule/Application.lean` (same file as the ≥ leg). Two
  small new lemmas alongside it, each in the file owning the relevant
  definition: `SimpleGraph.finrank_range_rigidityMap_eq_genericRank`
  (`GenericRigidityMatroid.lean` — the equality sibling of the ≥ leg's
  `finrank_range_rigidityMap_le_genericRank`, same row-rank/column-rank
  conversion, landing at `genericRank_eq_finrank_span`'s equality since the
  placement is generic) and `lineExtensor_ne_zero_of_ne`
  (`Molecule/ScrewVelocity.lean` — a line extensor of two distinct points is
  nonzero, via `screwOmega_lineExtensor` + contrapositive). The endpoint
  selector `ends : β → V × V` is hand-built (no producer supplies one for
  the ≤ leg): `if h : ∃ x y, G.shadowGraph.IsLink e x y then (h.choose,
  h.choose_spec.choose) else (v₀, u₀)` for a fixed distinct default pair
  `v₀ ≠ u₀` (from `hmin`'s forced edge). Distinctness of `(ends e).1`/`.2`
  reads off `shadowGraph.IsLink`'s `G.Adj` component directly (`.1.ne`) —
  no `Graph.Simple`/`Loopless` instance needed, contrary to the initial
  plan of routing through `eq_or_eq_of_isLink_of_isLink`.
