# Phase 32 — PROSPECT new-math round: Jacobs' conjecture + the degree-1 rank formula (work log)

**Status:** in progress (opened 2026-07-10; chapter opened 2026-07-10).

Planning input: `notes/Prospect.md` (grouping 2 of the adjudicated
phase order). Both targets are Jackson–Jordán 2008 (*On the rigidity of
molecular graphs*, Combinatorica **28**) corollaries built on top of the
landed molecule rank formula: they consume the *statement* of
`SimpleGraph.molecule_rank_formula` (Phase 26) and the Phase-24 generic
matroid surface, not proof internals.

## Current state

**Forward-mode chapter open** — `blueprint/src/chapter/jacobs.tex`
(`sec:jacobs`), built from the accepted L1 recon's node decomposition, is
the phase's authoritative dep-graph / lemma index. Status surfaces synced
at chapter open.

**Every section except `sec:jacobs-degree-one` is fully green:**

- **`sec:jacobs-laman3` + `sec:jacobs-easy` (D-track)** —
  `SimpleGraph.IsLaman3` + monotonicity + degree bound (`Jacobs.lean`);
  both row-independence corollaries (`RigidityMatroid.lean`,
  `GeneralPositionPlacement.lean`).
- **`sec:jacobs-tight-partitions`** — the `D`-generic tight-partition
  machinery (`Graph.IsTightPartition` + structural lemmas,
  `Molecular/Deficiency.lean`).
- **`sec:jacobs-counting`** — shadow-carrier bridge, four-way `G²` edge
  classification, singleton-part neighborhood counts, normal-cross double
  count (`JacobsCounting.lean`; see its module docstring for the
  lemma-by-lemma build order).
- **`thm:laman-square-count`** (JJ Theorem 5.3) —
  `SimpleGraph.laman_square_count` (`JacobsCounting.lean`).
- **`thm:jacobs-min-degree-two`** (JJ Thm 5.4, min-degree-2 case) —
  `SimpleGraph.jacobs_min_degree_two` (`JacobsTheorem.lean`).
- **`sec:jacobs-zero-extension` (S1–S5, 2026-07-11/16)** — the four
  graph-theory nodes (`SquareGraph.lean`, `Jacobs.lean`); the
  row-independence lift `_extend`/`_lift` (`RigidityMatroid.lean`); the
  degree-≤3 corollary `zero_extension_genericRank_add_degree` +
  `zero_extension_indep_iff_of_degree_le_three` (`JacobsZeroExtension.lean`);
  the clique-rank equality `zero_extension_genericRank_add_min_of_isClique`
  (with lower bound `zero_extension_genericRank_add_min_le` and the
  K₅ crux facts `indep_k5_sub_edge`/`dep_k5`/`mem_closure_k5_sub_edge`);
  the vertex-restriction transport `genericRigidityMatroid_indep_image_iff`
  + `genericRank_eq_rk_image` (`GenericRigidityMatroid.lean`).
- **`thm:jacobs`** (JJ Conjecture 5.1 / Theorem 5.4, the full
  unconditional iff) — `SimpleGraph.jacobs` (`JacobsTheorem.lean`).

**L2 pre-build recon + design pass done (2026-07-16)** —
`sec:jacobs-degree-one`'s two theorem statements verified faithful against
JJ 2008 Lemma 4.2 (`.refs/`, p. 9–10); the carrier is settled (fixed
vertex set, support-relative induction; `twoCore` as an `sSup`), the
transport cites dropped from both proofs, and the ordered slice plan
T1–T5 is in *Hand-off*. See *Decisions made*.

**T1 landed (2026-07-16)** — `SimpleGraph.twoCore` + the six-lemma API in
a new plain-graph-theory file `TwoCore.lean`; `def:two-core` pinned
`\leanok` (def + the three characterization lemmas). See *Decisions made*.

**Next concrete step** — T2 of the L2 slice plan (the leaf-peel
substrate — generic `SimpleGraph` lemmas, upstream-eligible). See
*Hand-off*.

## Work items

- **File placement (settled):** the `sec:jacobs-counting` classification /
  counting / Thm-5.3-assembly content lives in
  `CombinatorialRigidity/JacobsCounting.lean` (plain `import`, downstream
  of `Jacobs.lean` + `Molecular/{Deficiency,Molecule/Carrier}.lean`); the
  D-track row-independence lemmas live alongside their planar analogue in
  `RigidityMatroid.lean`.
- **Single-edge rank base `r = 1`** — checked (2026-07-16): no named lemma
  exists; lands as `genericRank_single_edge` in slice T3.

## Architectural choices made up front

- **Blueprint chapter deferred to the first post-recon commit** — done
  (chapter-open commit). The Phase-30 recon-first precedent held: the
  recon overturned the natural `IsSparse 3 6` statement pin before any
  chapter committed it.
- **Status-surface obligation at chapter open** — discharged in the
  chapter-open commit (intro.tex *Reading this blueprint* + the
  phase-32 continuation paragraph; README / home_page continuation
  paragraphs).

## Blockers / open questions

- None. Everything except `sec:jacobs-degree-one` is fully green; T1 of
  the recon-settled L2 slice plan is landed, T2–T5 remain — see *Hand-off*.

## Hand-off / next phase

**Next: T2 of the L2 slice plan below** (`sec:jacobs-degree-one`:
`thm:degree-one-rank-tree`, `thm:degree-one-rank` are the remaining red
nodes in `jacobs.tex` — `def:two-core` (T1) is green; T5 closes the phase,
see `PHASE-BOUNDARIES.md` *When this commit closes a phase*: ROADMAP row,
status-surface sync, `#print axioms` alignment, exposition ledger).

**L2 slice plan (recon-settled 2026-07-16).** Carrier: everything on a fixed
vertex type `V`; both theorems by strong induction on `G.edgeSet.ncard` over
support-relative strengthenings (the `jacobs` induction shape) — the peeled
leaf stays in `V` isolated, so **no rank transport** (S5 unused here) and no
type-changing induction. Statement style: `[Fintype V]`, `G.degree` for the
`V₁` sets, additive tree formula (ℕ-subtraction trap at `|V| = 2`:
`2·2 − 5` truncates). Mathlib supplies the structural substrate (all names
sighted in-file): `IsTrail.not_mem_support_of_subsingleton_neighborSet`,
`Walk.toDeleteEdges`, `adj_of_mem_walk_support`, `Walk.induce`,
`IsTree.exists_vert_degree_one_of_nontrivial`, `IsAcyclic.induce`/`.anti`,
`degree_induce_of_support_subset`, `induce_deleteIncidenceSet_of_notMem`,
`support_deleteIncidenceSet_subset`, `Connected.card_vert_le_card_edgeSet_add_one`,
`isTree_iff_connected_and_card`, `Matroid.eRk_empty`.

- **T1 — done (2026-07-16)**, `SimpleGraph.twoCore` + API in `TwoCore.lean`;
  see *Decisions made*.
- **T2 — leaf-peel substrate** (generic `SimpleGraph` lemmas; upstream-eligible —
  builder places, `Mathlib/Combinatorics/SimpleGraph/` mirror style is fine;
  may split into two commits if heavy):
  `neighborSet_deleteIncidenceSet_of_ne (h : w ≠ v) :
  (G.deleteIncidenceSet v).neighborSet w = G.neighborSet w \ {v}` (+ the `w = v`
  empty case, + degree corollaries: unchanged off `{v, u}` since a leaf's only
  neighbor is `u`; `u` drops by one; `v` to zero);
  `support_deleteIncidenceSet_of_degree_eq_one (hv : G.degree v = 1)
  (hu : G.Adj v u) (h2 : 2 ≤ G.degree u) :
  (G.deleteIncidenceSet v).support = G.support \ {v}`;
  the two `V₁`-set identities (`{w | degree w = 1}` loses `v` when
  `3 ≤ G.degree u`, swaps `v` for `u` when `G.degree u = 2`);
  `reachable_deleteIncidenceSet (hv : G.degree v ≤ 1) (hx : x ≠ v) (hy : y ≠ v)
  (h : G.Reachable x y) : (G.deleteIncidenceSet v).Reachable x y`
  (take `h`'s path; the trail lemma keeps `v` off its support; transfer by
  `Walk.toDeleteEdges` — an edge in `incidenceSet v` would put `v` on the
  support);
  `two_le_degree_of_adj_degree_eq_one` (the `d_G(u) ≥ 2` derivation:
  `hconn : ∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y`,
  `3 ≤ G.support.ncard`, `G.degree v = 1`, `G.Adj v u` — pick
  `w ∈ G.support \ {v, u}`, a path `w → v` has penultimate vertex in
  `N(v) = {u}`, so `u` is interior; if `G.degree u = 1` the trail lemma
  expels `u` — contradiction);
  `connected_induce_support` (`hconn` + `G.support.Nonempty` ⇒
  `(G.induce G.support).Connected`; paths between support vertices stay in the
  support via `adj_of_mem_walk_support`, transfer by `Walk.induce`);
  `exists_degree_eq_one` (leaf existence: `hconn` + `G.IsAcyclic` +
  `2 ≤ G.support.ncard` ⇒ `∃ v ∈ G.support, G.degree v = 1` — the induced
  graph on the support is an `IsTree`, apply
  `exists_vert_degree_one_of_nontrivial` + `degree_induce_of_support_subset`).
- **T3 — rank glue** (new file `JacobsDegreeOne.lean`, imports
  `JacobsZeroExtension` + `SquareGraph` + `TwoCore`):
  `genericRank_single_edge [Finite V] (hxy : x ≠ y) (hE : G.edgeSet = {s(x, y)}) :
  G.genericRank 3 = 1` (the resolved work item;
  `zero_extension_genericRank_add_degree` at `x`, deleted graph has empty edge
  set, `Matroid.eRk_empty`);
  `genericRank_square_peel [Finite V] (hv : G.degree v = 1) (hu : G.Adj v u) :
  G.square.genericRank 3 = (G.deleteIncidenceSet v).square.genericRank 3 + min 3 (G.degree u)`
  (compose `zero_extension_genericRank_add_min_of_isClique` at `G.square`/`v`
  with `isClique_neighborSet_square_of_degree_eq_one`,
  `square_deleteIncidenceSet_of_degree_le_one`,
  `ncard_neighborSet_square_of_degree_eq_one`).
- **T4 — `thm:degree-one-rank-tree`** (pins + `\leanok`):
  `private theorem degree_one_rank_tree_of_ncard [Fintype V] : ∀ n, ∀ G : SimpleGraph V,
  G.edgeSet.ncard = n → (∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y) →
  G.IsAcyclic → 2 ≤ G.support.ncard →
  G.square.genericRank 3 + 5 = 2 * G.support.ncard + {w | G.degree w = 1}.ncard`
  (strong induction; base `G.support.ncard = 2` is a single edge —
  `genericRank_single_edge`, square = the graph itself; step: leaf from T2's
  `exists_degree_eq_one`, `d_G(u) ≥ 2` from T2, peel via T3's
  `genericRank_square_peel`, maintenance via T2, `omega` for the balance);
  `theorem degree_one_rank_tree [Fintype V] (hG : G.IsTree) (h2 : 2 ≤ Fintype.card V) :
  G.square.genericRank 3 + 5 = 2 * Fintype.card V + {w | G.degree w = 1}.ncard`
  (support = `univ` for a connected nontrivial graph — small helper — then the
  strengthening at `n := G.edgeSet.ncard`).
- **T5 — `thm:degree-one-rank`** (pins + `\leanok`; **closes the phase**):
  `private theorem degree_one_rank_of_ncard [Fintype V] : ∀ n, ∀ G : SimpleGraph V,
  G.edgeSet.ncard = n → (∀ x ∈ G.support, ∀ y ∈ G.support, G.Reachable x y) →
  G.support.ncard ≤ G.edgeSet.ncard →
  G.square.genericRank 3 = G.twoCore.square.genericRank 3
    + 2 * (G.support \ G.twoCore.support).ncard + {w | G.degree w = 1}.ncard`
  (case `V₁ = ∅`: every support vertex has degree ≥ 2, so
  `twoCore_eq_self_of_minDegree` closes both sides; else peel a leaf `v` —
  `G.support.ncard = 2` contradicts the edge-count hypothesis, so
  `3 ≤ G.support.ncard` and `d_G(u) ≥ 2`; `twoCore_deleteIncidenceSet` keeps
  the core fixed, `v ∈ G.support \ G.twoCore.support` by
  `notMem_support_twoCore`, `omega` balances the two degree cases);
  `theorem degree_one_rank [Fintype V] (hconn : G.Connected) (hnt : ¬ G.IsTree) :
  G.square.genericRank 3 = G.twoCore.square.genericRank 3
    + 2 * (G.twoCore.supportᶜ).ncard + {w | G.degree w = 1}.ncard`
  (`Nontrivial V` since a subsingleton connected graph is a tree
  (`IsTree.of_subsingleton`); support = `univ`; the edge-count hypothesis from
  `Connected.card_vert_le_card_edgeSet_add_one` + `isTree_iff_connected_and_card`).

## Decisions made during this phase

### Recon verdicts and adjudications

- **L2 pre-build recon + design pass (2026-07-16).** JJ Lemma 4.2 verified
  against `.refs/` (p. 9–10): both blueprint statements faithful; JJ's "by
  Lemma 3.3" rank steps genuinely need the landed clique form at
  `d_G(u) > 3` (their 3.3 is independence-only at `s ≤ 3`), so the
  transcribed proofs are correct expansions. Carrier settled: fixed-`V`
  support-relative strong induction (no rank transport — S5's rank form
  goes unused by L2; its `thm:jacobs` indep use stands); `twoCore` as
  `sSup`; additive tree formula. Blueprint repairs: transport `\uses`
  dropped, `d_G(u) ≥ 2` gap filled, unconsumed empty-iff-tree sentence
  moved out as prose, `fmlnote:degree-one-fixed-carrier` added. Franzblau
  2000 not in `.refs/` — tree case verified through JJ's statement only.
- **Zero-extension recon + design pass (2026-07-11).** The chapter-open
  unconditional `min(3, d)` rank form was refuted (`K₁,₄` has rank 4, not
  `0 + 3`); the lift lemma gained an affine-independence hypothesis on the
  neighbor images. Split: `cor:zero-extension-degree-le-three`
  (unconditional; `thm:jacobs`'s form) + `cor:zero-extension-clique-rank`
  (`min(3, d)` under a neighborhood clique — JJ's own condition; upper
  bound by a K₅-closure argument). Induce-transport strengthened to the
  rank form; three new red support-restriction nodes; Whiteley 9.1.3
  verified fixed-placement / `s = 3` in `.refs/`.
- **L1 recon verdict (2026-07-10, accepted).** "G² is Laman" is *not*
  `IsSparse 3 6`: the `(k,ℓ)` guard `ℓ ≤ k·|s|` admits `|s| = 2` where
  the bound is 0, failing on every graph with an edge (compiled K₂
  refutation witness); JJ's condition guards `|X| ≥ 3`. Pinned as the
  standalone `SimpleGraph.IsLaman3`. JJ Thm 5.3 pinned against
  `G.shadowGraph.deficiency 3` — which *is* JJ's `def(G)` at `D = 6` —
  and Jacobs as `(genericRigidityMatroid V 3).Indep G.square.edgeSet ↔
  IsLaman3 G.square`.
- **Scope reductions found by the L1 recon.** JJ Lemma 3.1 / Thm 3.4 /
  Thm 4.1 (2-thin covers, the rank *upper* bound) are not needed —
  `molecule_rank_upper_bound` already covers that limb via KT. JJ
  Lemma 3.2 is consumed in reduced forms only (chapter
  `fmlnote:tight-partition-consumed-forms`).
- **Thm 5.4 is thinner in the paper than in Lean.** The max-degree-3 core
  reduction is asserted without proof in JJ; the chapter tracks it as
  `sec:jacobs-zero-extension` (Whiteley 1996 Lemma 9.1.3 + the square
  identities + the transport), shared with L2.
- **Coordinator adjudications (2026-07-10):** standalone predicate (no
  refactor of `IsSparse`'s guard — Phase 1 API untouched); B-track
  tight-partition arithmetic stated D-generically (`Graph α β`,
  parameter `n`, `Deficiency.lean` house style); `lem:normal-cross-count`
  one node + fmlnote, sub-split at build time.
- **New attributions verified:** Jacobs 1998 (J. Phys. A **31**,
  6653–6668) and Franzblau 2000 (Discrete Appl. Math. **101**, 131–155)
  added to the bibliography; JJ Lemma 3.2 credited to the Jackson–Jordán
  companion paper via the 2008 statement.

### Settled build verdicts (details in git history + file docstrings)

- **T1 (2026-07-16).** `SimpleGraph.twoCore` + six-lemma API, new file
  `TwoCore.lean` (plain graph theory: `Mathlib.Combinatorics.SimpleGraph.
  DeleteEdges` + `Mathlib.Data.Set.Card` only). Built exactly to the recon's
  pinned signatures; `twoCore_le`/`le_twoCore` from the general
  `CompleteLattice` `sSup_le`/`le_sSup` (no need to unfold `Adj`),
  `twoCore_minDegree` via `sSup_adj` + `neighborSet_mono`,
  `twoCore_deleteIncidenceSet` composes `notMem_support_twoCore` with
  `deleteIncidenceSet_adj` both directions. `def:two-core` pinned `\leanok`
  (def + `twoCore_le`/`le_twoCore`/`twoCore_minDegree`). FRICTION: `.ncard`
  needs an explicit `Mathlib.Data.Set.Card` import — `DeleteEdges.lean`
  doesn't pull it in transitively the way the project's own `SimpleGraph/
  Finite` mirror does.
- **`thm:jacobs` (2026-07-16).** `SimpleGraph.jacobs` by strong induction
  on `G.edgeSet.ncard` (fixed `V`, the `LamanTheorem.lean` idiom): peel a
  degree-one vertex via the 0-extension iff, else restrict to the support
  and transport `jacobs_min_degree_two` back via
  `genericRigidityMatroid_indep_image_iff` + a new glue lemma
  `edgesIn_eq_edgeSet_of_support_subset` (`EdgesIn.lean`). FRICTION:
  TACTICS-QUIRKS § 75 recurrence ×3 (explicit-`variable` `Iff.rfl` lemmas
  break dot-projection — dot-call on the graph or use defeq).
- **S5 (2026-07-16).** `genericRigidityMatroid_indep_image_iff` +
  `genericRank_eq_rk_image` (general `d`, `GenericRigidityMatroid.lean`),
  via the landed row transports at `φ = Subtype.val` + a choice-function
  reindexing; new helper `genericRigidityMatroid_indep_iff_edgeSetRowIndependent`
  packages the recurring indep↔row-LI composition. FRICTION:
  `Sym2.isDiag_map` closes the image-edge-set step in one lemma.
- **S4 (2026-07-16, four commits).** Lower bound
  `zero_extension_genericRank_add_min_le` (three-neighbour star
  restriction; TACTICS-QUIRKS § 83); crux (a) `indep_k5_sub_edge` (iterated
  star 0-extensions — technique promoted to TACTICS-GOLF § 20); crux (b)
  `dep_k5` + closure step `mem_closure_k5_sub_edge`
  (`Matroid.Indep.mem_closure_iff_of_notMem`); assembly
  `zero_extension_genericRank_add_min_of_isClique` (K₅-closure,
  `eRk_mono` + `eRk_closure_eq` bridged by `cast_rk_eq_eRk_of_finite`).
- **S3 (2026-07-16).** `zero_extension_genericRank_add_degree` +
  `zero_extension_indep_iff_of_degree_le_three` (new file
  `JacobsZeroExtension.lean`); basis-witness graph for the lower bound;
  new helper `edgeSetRowIndependent_univ_iff_top`. FRICTION ×2
  (TACTICS-QUIRKS § 82; a `classical` decidability gotcha).
- **S2 (2026-07-16).** `zero_extension_edgeSetRowIndependent_extend`/`_lift`
  (`RigidityMatroid.lean`); single test-motion detector
  `Ψ := (LinearMap.single ℝ _ v).dualMap`; new mirror helper
  `LinearIndependent.disjoint_span_range_ker` (see FRICTION).
- **S1 (2026-07-11).** The four graph-theory nodes (`SquareGraph.lean`,
  `Jacobs.lean`) + `square_mono`. Two § 75-family dot-notation traps
  flagged for S2+ (see TACTICS-QUIRKS § 75).
- **`thm:jacobs-min-degree-two` (2026-07-11).** New file
  `JacobsTheorem.lean`; the recon-verified sandwich `laman_square_count`
  (`≤`) vs `molecule_rank_formula` (`=`) vs `rk_le_toFinset_card` forces
  equality; `Matroid.indep_iff_eRk_eq_encard_of_finite` converts to
  independence.
- **`thm:laman-square-count` (2026-07-11).** Per-part inequality
  (additive form) case-split on the part dichotomy; `omega` closes the
  final mixed ℕ/ℤ goal. Two traps lifted to TACTICS-QUIRKS § 4 / § 35.
- **Classification decompositions (2026-07-11).** The three missing
  `partLabels f`-indexed `_eq_biUnion` decompositions; the special-cross
  class redesigned witness-indexed → label-indexed
  (`squareSpecialCrossEdgesRootedAt`), superseding three unpinned lemmas
  (removed outright).
- **`sec:jacobs-counting` development (2026-07-10/11, ~15 commits) fully
  settled** — see `git log` and `JacobsCounting.lean`'s module docstring
  for the build order and technique notes.
