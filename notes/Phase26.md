# Phase 26 — Corollary 5.7 (the molecule-application capstone) (work log)

**Status:** ✓ Complete (opened and closed 2026-07-07). The last phase of the
17–26 molecular-conjecture program.

## Current state

**Complete.** All five nodes of `blueprint/src/chapter/molecule-application.tex`
are green. The capstone `cor:molecule-rank-formula` landed as
`SimpleGraph.molecule_rank_formula` (`Molecular/Molecule/Application.lean`):
`r(G²) = 3|V| − 6 − def(G̃)` for a simple graph `G` of min degree ≥ 2, the
direct `le_antisymm` of the two leg lemmas, no new construction. Assembled
arithmetically from the two Phase-25 modelling links, Theorem 5.6 (Phase 23;
`d = 3` from Phase 22k), and the Phase-24 generic matroid — Theorem 5.6's rank
statement replaces Jackson–Jordán 2008's whole §3–4 (deficiency induction +
independent-cover bounds). Formula attributed to Jackson–Jordán 2008; the
conjecture-resolution to Katoh–Tanigawa.

## Hand-off / next phase

**No successor phase** — Phase 26 closes the molecular-conjecture program
(17–26). Still open for a future cleanup round at a phase boundary (not
scheduled): the molecular-layer dead-code/liveness sweep deferred from
`notes/Phase23-cleanup.md` (*Deferred to a future dead-code / liveness sweep*).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **F4 carrier bridge — the padded shadowing multigraph.** `lem:molecule-graph-carrier`
  landed as `SimpleGraph.shadowGraph` + four properties (`_simple`, `_vertexSet`,
  `_isLink_iff`, `card_shadowLabel_lt`) in its own file `Molecular/Molecule/Carrier.lean`.
  Label type `Sym2 V ⊕ Fin (6·(|V|−1)+1)`: the `Sym2 V` half tags each edge by
  its endpoint pair (spanning + simple + shadow-property free); the `Fin` half is
  pure padding that alone exceeds Theorem 5.6's `6·(|α|−1) < |β|` label bound
  regardless of `G`'s sparsity (`Sym2 V` alone falls short for `|V| ≤ 10`). Chose a
  direct `Graph` structure literal (mirroring `edgeMultiply`/`singleEdge`) over the
  vendored `Graph.OfSimpleGraph` (which uses `β := Sym2 V` alone). The
  carrier-invariance clause ("any two shadowing carriers agree in deficiency") is
  **not formalized** — trimmed to a non-`\leanok` blueprint remark, since the two
  rank-bound legs fix one canonical carrier throughout and never compare two.
- **`lem:square-rank-le-genericRank` — the genericRank glue.**
  `SimpleGraph.finrank_span_rigidityRow_le_genericRank` (`GenericRigidityMatroid.lean`,
  graph-free): re-derives `genericRank_eq_finrank_span`'s row-span at the *specific*
  placement's `linearRigidityMatroid`, then dominates via `Matroid.rk_le_iff` +
  `genericRigidityMatroid_indep_iff`.
- **≥ leg (`lem:molecule-rank-lower-bound`).** `SimpleGraph.molecule_rank_lower_bound`:
  `exists_molecular_rankHypothesis_generalPosition` → dictionary forward
  (`molecular_finrank_motions_eq_square_ker`) → `dim ker R(G²,c) = 6+def` →
  rank–nullity → dominated by the generic rank via the `RigidityMap`-range restatement
  `finrank_range_rigidityMap_le_genericRank`. Bridge lemmas `rigidityRow_congr`
  (`RigidityMatroid.lean`) + `finrank_range_rigidityMap_le_genericRank`
  (`GenericRigidityMatroid.lean`) landed in their defining files.
  Final-arithmetic friction (`rw`-ing `screwDim 2 = 6` / `Nat.card = Fintype.card`
  broke on "motive not type correct" because both literals recur in `shadowGraph`'s
  label-type index; hand the raw equalities to `omega` instead). **Lifted to:**
  TACTICS-QUIRKS § 77 / FRICTION [idiom].
- **≤ leg (`lem:molecule-rank-upper-bound`).** `SimpleGraph.molecule_rank_upper_bound`:
  at a placement generic ∩ general-position, `genericRank = rank R(G²,p)`
  (`finrank_range_rigidityMap_eq_genericRank`); dictionary reverse identifies
  `dim ker R(G²,p)` with molecular `dim Z`; the genericity-free bound `6+def ≤ dim Z`
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`) caps the rank. Unlike
  the ≥ leg, no producer supplies an endpoint selector, so `ends` is hand-built (a
  linked label's classically chosen link pair, else a fixed distinct default pair
  from `hmin`'s forced edge); distinctness reads off `shadowGraph.IsLink`'s `G.Adj`
  component (`.1.ne`). New siblings `finrank_range_rigidityMap_eq_genericRank`
  (`GenericRigidityMatroid.lean`) + `lineExtensor_ne_zero_of_ne`
  (`Molecule/ScrewVelocity.lean`).
- **Cor 5.7 (`cor:molecule-rank-formula`).** `SimpleGraph.molecule_rank_formula`:
  `le_antisymm` of the two legs. The "generically rigid iff `def(G̃)=0` iff six
  edge-disjoint spanning trees" reading is **not separately formalized** (no
  `genericRank` ↔ `IsGenericallyRigid` bridge exists) — a non-`\leanok` blueprint
  remark, same move as the carrier-invariance clause.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`rw` of a literal that recurs in a dependent-type index breaks with "motive not
  type correct"; feed raw equalities to `omega` instead* → TACTICS-QUIRKS § 77 /
  FRICTION [idiom].
