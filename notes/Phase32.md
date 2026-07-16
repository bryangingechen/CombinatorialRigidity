# Phase 32 — PROSPECT new-math round: Jacobs' conjecture + the degree-1 rank formula (work log)

**Status: ✓ CLOSED** (opened 2026-07-10, closed 2026-07-16).

Planning input: `notes/Prospect.md` (grouping 2 of the adjudicated phase
order). Both targets are Jackson–Jordán 2008 (*On the rigidity of
molecular graphs*, Combinatorica **28**) corollaries built on top of the
landed molecule rank formula (`SimpleGraph.molecule_rank_formula`,
Phase 26) and the Phase-24 generic matroid surface.

## Outcome

`blueprint/src/chapter/jacobs.tex` (`sec:jacobs`) is fully green — the
forward-mode chapter is the authoritative map of what landed and where.
One-paragraph summary in ROADMAP §32. Headlines (all standard-axioms-only,
verified at close):

- **`SimpleGraph.jacobs`** (`JacobsTheorem.lean`) — Jacobs' conjecture,
  JJ Conjecture 5.1 / Thm 5.4, unconditional: `E(G²)` is independent in
  the 3-D generic rigidity matroid iff `G²` is Laman (JJ's 3-D counting
  sense, `SimpleGraph.IsLaman3`).
- **`SimpleGraph.degree_one_rank_tree`** / **`SimpleGraph.degree_one_rank`**
  (`JacobsDegreeOne.lean`) — JJ Lemma 4.2 (tree case Franzblau 2000):
  `r(G²) + 5 = 2|V| + |V₁|` for trees, and the reduction
  `r(G²) = r((G^core)²) + 2|supp(G^core)ᶜ| + |V₁|` for connected
  non-trees, with the two-core `SimpleGraph.twoCore` (`TwoCore.lean`).

New files: `Jacobs.lean`, `JacobsCounting.lean`, `JacobsTheorem.lean`,
`JacobsZeroExtension.lean`, `JacobsDegreeOne.lean`, `TwoCore.lean`, plus
mirror files `Mathlib/Combinatorics/SimpleGraph/{DeleteEdges,Acyclic,
Connectivity/Connected}.lean`; adders in `SquareGraph.lean`,
`RigidityMatroid.lean`, `GeneralPositionPlacement.lean`,
`GenericRigidityMatroid.lean`, `EdgesIn.lean`, `Molecular/Deficiency.lean`.

## Hand-off / next phase

**Phase 32 is closed; the successor opened as Phase 33** (2026-07-16;
`notes/Phase33.md`): PROSPECT G1 field generality of the core Thm
5.5/5.6 chain, recon-first (the two chokepoint spikes). One
coordinator-owned residue: this phase's `notes/dispatch-log.md`
grooming (`PHASE-BOUNDARIES.md` close step) was out of scope for the
closing build commit — fold it into the coordinator's session-close
pass.

## Decisions made during this phase (one-line verdicts; detail in git + file docstrings)

### Recon verdicts and adjudications

- **L1 recon (2026-07-10, accepted).** "G² is Laman" is *not*
  `IsSparse 3 6` (the `(k,ℓ)` guard admits `|X| = 2`, failing on any
  edge; compiled K₂ witness) — pinned as standalone
  `SimpleGraph.IsLaman3` with JJ's `|X| ≥ 3` guard
  (`fmlnote:isLaman3-guard`); JJ Thm 5.3 pinned against
  `G.shadowGraph.deficiency 3` = JJ's `def(G)` at `D = 6`. Scope
  reductions: JJ Lemma 3.1 / Thm 3.4 / Thm 4.1 not needed
  (`molecule_rank_upper_bound` covers that limb); Lemma 3.2 consumed in
  reduced forms only (`fmlnote:tight-partition-consumed-forms`); JJ's
  unproven max-degree-3 → min-degree-2 reduction tracked as
  `sec:jacobs-zero-extension`. Adjudications: no `IsSparse` guard
  refactor; tight-partition arithmetic D-generic in `Deficiency.lean`;
  `lem:normal-cross-count` one node + fmlnote, sub-split at build time.
- **Zero-extension recon (2026-07-11).** Chapter-open unconditional
  `min(3, d)` rank form refuted (`K₁,₄` has rank 4); split into
  `cor:zero-extension-degree-le-three` (unconditional) +
  `cor:zero-extension-clique-rank` (JJ's own neighborhood-clique
  condition; upper bound by K₅-closure); the lift lemma gained the
  affine-independence hypothesis; Whiteley 9.1.3 verified
  fixed-placement / `s = 3` in `.refs/`.
- **L2 recon + design pass (2026-07-16).** Both `sec:jacobs-degree-one`
  statements verified faithful against JJ Lemma 4.2 (`.refs/`, p. 9–10);
  JJ's "by Lemma 3.3" rank steps genuinely need the clique form at
  `d > 3` (their 3.3 is independence-only at `s ≤ 3`). Carrier settled:
  fixed-`V` support-relative strong induction, no rank transport;
  `twoCore` as `sSup`; additive (subtraction-free) tree formula
  (`fmlnote:degree-one-fixed-carrier`). Franzblau 2000 not in `.refs/` —
  tree case verified through JJ's statement only.
- **New attributions verified:** Jacobs 1998 (J. Phys. A **31**,
  6653–6668) and Franzblau 2000 (Discrete Appl. Math. **101**, 131–155)
  added to the bibliography (and, at close, `formalization.yaml`).

### Build verdicts (compressed at close)

- **D-track / tight partitions / counting / Thm 5.3 / min-degree-2
  Thm 5.4 (2026-07-10/11, ~18 commits):** `IsLaman3` API; the
  `Graph.IsTightPartition` machinery (`Molecular/Deficiency.lean`);
  the four-way `G²` edge classification + singleton-part and
  normal-cross counts (`JacobsCounting.lean` — its module docstring
  carries the build order); `laman_square_count` per-part additive form
  closed by `omega`; `jacobs_min_degree_two` by the
  count-vs-rank-formula sandwich.
- **S1–S5 zero-extension track (2026-07-11/16):** the square/graph-theory
  nodes (`SquareGraph.lean`, `Jacobs.lean`); row-independence
  `_extend`/`_lift` via a single test-motion detector
  (`RigidityMatroid.lean`); `zero_extension_genericRank_add_degree` +
  the degree-≤3 iff (`JacobsZeroExtension.lean`); the K₅ crux
  (`indep_k5_sub_edge` by iterated star 0-extensions — TACTICS-GOLF § 20;
  `dep_k5`; the closure step) and the clique-rank assembly; the
  vertex-restriction transport `genericRigidityMatroid_indep_image_iff`
  + `genericRank_eq_rk_image` (`GenericRigidityMatroid.lean`).
- **`thm:jacobs` (2026-07-16):** strong induction on `G.edgeSet.ncard`
  (fixed `V`), leaf-peel via the 0-extension iff, else support-restrict
  + transport; new glue `edgesIn_eq_edgeSet_of_support_subset`.
- **T1–T5 degree-one track (2026-07-16):** `twoCore` + API
  (`TwoCore.lean`); the leaf-peel substrate mirrors
  (`DeleteEdges`/`Connected`/`Acyclic`, incl.
  `ncard_edgeSet_deleteIncidenceSet` added at close); the rank glue
  (`genericRank_single_edge`, `genericRank_square_peel`); both rank
  formulas by support-relative strong induction on the edge count
  (`degree_one_rank_tree_of_ncard` / `degree_one_rank_of_ncard` private
  strengthenings + public wrappers).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION

- Iterated star 0-extensions → TACTICS-GOLF § 20.
- Statement-level `[DecidableRel G.Adj]` alongside `[Fintype V]` when the
  conclusion quantifies `G.degree` → TACTICS-QUIRKS § 84 (two recurrences).
- Dot-projection traps on explicit-`variable` lemmas → TACTICS-QUIRKS § 75
  (×7 recurrences this phase).
- `rcases … with rfl` on an equality of two pre-existing locals →
  TACTICS-QUIRKS § 4; `simp`-destructured `Ne` fails `.symm` →
  TACTICS-QUIRKS § 8 (new bullet).
- Smaller items: FRICTION entries dated 2026-07-10..16 (incl. the
  `Set.Card` import gap for `.ncard`, `Sym2.isDiag_map`, and the
  `Nat.card_coe_set_eq` root-namespace name).
