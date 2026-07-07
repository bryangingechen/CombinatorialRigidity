# Phase 26 — Corollary 5.7 (the molecule-application capstone) (work log)

**Status:** in progress (opened 2026-07-07).

## Current state

**Next concrete commit:** settle the F4 carrier bridge by landing
`lem:molecule-graph-carrier` — the shadowing multigraph carrier of a
`SimpleGraph V` with `> 6(|V|−1)` labels and adjacency-only deficiency
(the remaining leaf-most red node). The other leaf-most node,
`lem:square-rank-le-genericRank`, is now green
(`SimpleGraph.finrank_span_rigidityRow_le_genericRank`,
`GenericRigidityMatroid.lean`): for *any* placement `p` (not necessarily
generic), the row-span dimension realized at `p` is at most the generic
rank, via the same `Matroid.Rep.finrank_span_image_eq_rk` row-span
computation as `genericRank_eq_finrank_span` landing at
`(linearRigidityMatroid V d p).rk`, then `Matroid.rk_le_iff` +
`genericRigidityMatroid_indep_iff` to dominate `H.genericRank d`. Dropped
`def:generic-placement` and `lem:genericRank-eq-finrank-span` from its
`\uses` — the proof needs neither (works for any placement, and doesn't
route through the generic-placement row-span identity).

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

- **F4 (the carrier bridge) — FIRST-LEAF DECISION, pinned, leaning canonical.**
  The two Phase-25 endpoints have different carrier shapes:
  `exists_molecular_rankHypothesis_generalPosition` (`Molecule/Modelling.lean`)
  takes `G : Graph α β` directly and returns `ends`; the dictionary
  `molecular_finrank_motions_eq_square_ker` (`Molecule/Dictionary.lean`) takes
  `G : SimpleGraph V` (for `G.square` + its bar-joint `RigidityMap`) **and** a
  `G' : Graph V β` shadowing it via `hshadow : ∀ u v, u ≠ v → ((∃ e,
  G'.IsLink e u v) ↔ G.Adj u v)` + `hends`. Phase 26 must reconcile them so
  Cor 5.7 reads cleanly over `SimpleGraph V`. **Recon findings (2026-07-07):**
  no `SimpleGraph → Graph` bridge exists in mathlib (`Mathlib/Combinatorics/Graph/`)
  or the repo. `G.deficiency 3` on the carrier is `def(G̃)` with `D = bodyBarDim 3
  = 6`, matching KT's `d = 3` `D`. The `hcard : 6·(|α|−1) < |β|` label supply
  forbids using `β := Sym2 V` (too few labels on a sparse graph) — a *padded*
  label type is required.
  **Verdict (recommended, to confirm on the first build):** build a canonical
  shadowing carrier `lem:molecule-graph-carrier` (a `Graph V β` with a padded
  `β`, one link per adjacency, `Simple`, spanning) so Cor 5.7's statement is
  over `SimpleGraph V` alone and `def(G̃)` is a well-defined
  adjacency-only invariant (any two such carriers have equal deficiency, since
  `crossingEdges`/`numParts` read only the adjacency relation). The alternative
  — leave `G'`/`hshadow`/`hcard` as hypotheses in the Cor statement — is
  cheaper but leaks the carrier into the headline theorem; both endpoints are
  *stated* to accept either, so this is a statement-cleanliness call, not a
  feasibility one. Re-verify the padded-`β` construction closes (a
  `V ⊕ Fin (6·|V|)`-style label type, or similar) before committing the leaf.

## Assembly plan (the chapter's five red nodes)

All in `blueprint/src/chapter/molecule-application.tex`, dim-3. Leaf order
bottom-up:

- [x] `lem:square-rank-le-genericRank` — **the genericRank glue.** For any
  placement `p`, `rank R(H,p) ≤ genericRank H d` (a `p`-row-independent set
  is independent in `genericRigidityMatroid` via
  `genericRigidityMatroid_indep_iff`, so its size ≤ `rk E(H)`).
  `SimpleGraph.finrank_span_rigidityRow_le_genericRank`,
  `GenericRigidityMatroid.lean`. Leaf-most, graph-free.
- [ ] `lem:molecule-graph-carrier` — **F4 + the β-label supply.** See the F4
  pin above.
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

- **F4** — see the pin above; settle on the next build commit
  (`lem:molecule-graph-carrier`).
- None else: all consumed shapes are green and axiom-clean.

## Hand-off / next phase

Phase 26 is the last phase of the molecular-conjecture program (17–26). On
close it discharges KT Corollary 5.7 (`cor:molecule-rank-formula`), completing
the program. Next concrete commit is `lem:molecule-graph-carrier` (settling
F4 — the shadowing multigraph carrier + the padded-`β` label supply); see the
F4 pin above for the recommended construction. No successor phase is planned
beyond the program.

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
