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

**`sec:jacobs-laman3` and `sec:jacobs-easy` (D-track) are fully green** —
`SimpleGraph.IsLaman3` + monotonicity + degree bound (`Jacobs.lean`), and
both row-independence corollaries (`RigidityMatroid.lean`,
`GeneralPositionPlacement.lean`).

**`sec:jacobs-tight-partitions` is fully green** — the `D`-generic
tight-partition machinery (`Graph.IsTightPartition` and its structural
lemmas: existence, merge, subfamily bound, part dichotomy, cross-pair
multiplicity, common-neighbor uniqueness) in `Molecular/Deficiency.lean`.

**`sec:jacobs-counting` is fully green** — the shadow-carrier bridge
(`SimpleGraph.IsSquareTightPartition`), the four-way edge classification
of `G²` (`squareInPartEdges`/`squareGCrossEdges`/`squareNormalCrossEdges`/
`squareSpecialCrossEdges`, `lem:square-cross-classification`), the
singleton-part neighborhood count (`lem:singleton-part-neighborhood` +
converse), and the normal-cross double count (`lem:normal-cross-count`)
— all in `CombinatorialRigidity/JacobsCounting.lean`. See that file's
module docstring and `git log` (2026-07-10/11 commits) for the
lemma-by-lemma build order; no forward-looking detail remains here.

**`thm:laman-square-count` (JJ Theorem 5.3) is now fully green** —
`SimpleGraph.laman_square_count` (`JacobsCounting.lean`), `\lean{}` +
`\leanok` pinned, `blueprint/verify.sh` green. The assembly needed three
more `partLabels f`-indexed classification decompositions beyond what
`sec:jacobs-counting` had built (the previous hand-off's sketch undersold
this): `squareInPartEdges_eq_biUnion`, `squareNormalCrossEdges_eq_biUnion`
(via `squareNormalCrossEdgesRootedAt`), and `squareSpecialCrossEdges_eq_biUnion`
(via a **new** `squareSpecialCrossEdgesRootedAt` predicate, indexed by the
apex's *label* rather than by the apex vertex — see *Decisions made* for
why this superseded an earlier witness-indexed design). Combined with the
part dichotomy (`IsSquareTightPartition.ncard_eq_one_or_three_le`), the
per-part inequality (`IsSquareTightPartition.perPart_le`) sums
(`sum_perPart_le`) against the classification's `ncard` identity
(`square_ncard_eq_sum_classes`) and the `partitionDef`/`bodyBarDim 3 = 6`
unfolding to close the theorem — plain `omega` handled the final mixed
ℕ/ℤ arithmetic directly, no `zify` needed.

**`thm:jacobs-min-degree-two` (JJ Conjecture 5.1 / Theorem 5.4, minimum-degree
case) is now fully green** — `SimpleGraph.jacobs_min_degree_two` (new file
`JacobsTheorem.lean`), `\lean{}` + `\leanok` pinned, `blueprint/verify.sh`
green. Short corollary of `laman_square_count` + `molecule_rank_formula`; see
*Decisions made*.

**`sec:jacobs-zero-extension` restated post-recon (2026-07-11)** — the
transcribed rank form was refuted against the carrier before any Lean was
built on it; the corrected node set is in the chapter (all red), the slice
plan in *Hand-off*, the refutation in *Decisions made*.

**S1 (the four graph-theory nodes) is fully green (2026-07-11)** —
`SimpleGraph.square_deleteIncidenceSet_of_degree_le_one`,
`SimpleGraph.neighborSet_square_of_degree_eq_one` (+ its two
`ncard`/`IsClique` companions), `SimpleGraph.square_induce_of_support_subset`
(+ `SimpleGraph.square_support_subset`) in `SquareGraph.lean`, and
`SimpleGraph.IsLaman3.induce` in `Jacobs.lean`; all four blueprint nodes
`\leanok`, `blueprint/verify.sh` green. `square_mono` (the work-items glue)
landed alongside in `SquareGraph.lean`. See *Decisions made*.

**S2 (`lem:zero-extension-rowIndependent`) is now fully green (2026-07-16)** —
the `_extend`/`_lift` pair `SimpleGraph.zero_extension_edgeSetRowIndependent_extend`
(conditional core) and `SimpleGraph.zero_extension_edgeSetRowIndependent_lift`
(unconditional, `\lean{}` + `\leanok` pinned on the node) in `RigidityMatroid.lean`,
plus the reusable upstream helper `LinearIndependent.disjoint_span_range_ker` in the
`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean` mirror; `blueprint/verify.sh`
green. See *Decisions made*.

**S3 (`cor:zero-extension-degree-le-three`) is now fully green (2026-07-16)** —
`SimpleGraph.zero_extension_genericRank_add_degree` (rank formula) and
`SimpleGraph.zero_extension_indep_iff_of_degree_le_three` (independence iff), new
file `JacobsZeroExtension.lean`, both `\lean{}` + `\leanok` pinned on the one
blueprint node; plus the reusable reindexing lemma
`SimpleGraph.edgeSetRowIndependent_univ_iff_top` in `RigidityMatroid.lean`;
`blueprint/verify.sh` green. See *Decisions made*.

**S4 lower bound landed (2026-07-16)** — `SimpleGraph.zero_extension_genericRank_add_min_le`
(`JacobsZeroExtension.lean`): `r(H - E_H(v)) + min 3 (d_H(v)) ≤ r(H)`, clique-free. Not
blueprint-pinned yet (the node `cor:zero-extension-clique-rank` is the full equality, still red);
it becomes one of the node's `\lean{}` pins once the upper bound lands. See *Decisions made*.

**S4 upper-bound crux fact (a) landed (2026-07-16)** — `SimpleGraph.indep_k5_sub_edge`
(`JacobsZeroExtension.lean`): `K₅` minus an edge is independent in `genericRigidityMatroid V 3`,
built from the empty graph by four `0`-extension steps. Not blueprint-pinned (a proof-internal
crux fact, not a node of its own). See *Decisions made*; the reusable technique is promoted to
TACTICS-GOLF § 20.

**Next concrete step** — S4 upper-bound crux fact (b) (`K₅` is dependent — short, via
`isLaman3_of_genericRigidityMatroid_indep` + `IsClique.ncard_edgesIn`), then the K₅-closure
assembly and the clique-rank equality `cor:zero-extension-clique-rank`; see *Hand-off*.

## Work items

- **File placement (settled):** the `sec:jacobs-counting` classification /
  counting / Thm-5.3-assembly content lives in
  `CombinatorialRigidity/JacobsCounting.lean` (plain `import`, downstream
  of `Jacobs.lean` + `Molecular/{Deficiency,Molecule/Carrier}.lean`); the
  D-track row-independence lemmas live alongside their planar analogue in
  `RigidityMatroid.lean`.
- **Trivial glue for the zero-extension build, remaining (S3+):** edge-set
  bookkeeping for `SimpleGraph.map` / `induce` images under the transports;
  the single-edge rank base `r = 1` (L2's `K₂` base case). (`square_mono`,
  the third item, landed with S1 — see *Current state*.)

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

- None. `thm:jacobs-min-degree-two` and S1–S3 are fully green, S4's lower
  bound has landed, and S4's upper-bound crux fact (a) (`K₅ ∖ e` independent) is
  landed; the remaining degree-≤1 zero-extension reduction is scoped and
  slice-sized (crux fact (b) + the K₅-closure assembly, then S5) — see
  *Hand-off*.

## Hand-off / next phase

**`sec:jacobs-zero-extension`'s remaining slices S4–S5 are the authoritative
to-do list** (two still-red nodes; recon + design pass 2026-07-11, see
*Decisions made*). Ordered slice plan, recon-sized:

1. **S4 upper bound (hard — next concrete commit):** finish
   `cor:zero-extension-clique-rank`. The lower bound is landed
   (`zero_extension_genericRank_add_min_le`); crux fact (a) is landed
   (`SimpleGraph.indep_k5_sub_edge`: `K₅ ∖ e` is independent in `𝓡₃`, built by
   four `0`-extension steps from the empty graph — see *Decisions made*). Still
   needed: crux fact (b) — `K₅` is dependent, via
   `isLaman3_of_genericRigidityMatroid_indep` + `IsClique.ncard_edgesIn`
   (10 > 3·5−6 = 9) — and the K₅-closure assembly itself. Route: for
   `d_H(v) ≥ 4`, fix three neighbours `u₁,u₂,u₃`, form
   `H₃ = H - E_H(v) + {vu₁,vu₂,vu₃}` (`r(H₃) = r(H-E_H(v)) + 3` by S3), and show
   every further star edge `vw` (`w ∈ N_H(v) ∖ {u₁,u₂,u₃}`) lies in
   `M.closure H₃.edgeSet` via `vw ∈ M.closure (K₅ ∖ vw)` (the nine edges on
   `{v,u₁,u₂,u₃,w}` all live in `H₃.edgeSet`, using the clique hypothesis for the
   six edges among `u₁,u₂,u₃,w`, and crux facts (a)/(b) for the closure step
   itself: a dependent set minus one element that stays independent has that
   element in the smaller set's closure — check `Matroid.Indep.mem_closure_iff_of_notMem`
   or its neighbours against this project's `Matroid` API before assuming the
   name, not yet used anywhere in this codebase). Then
   `H.edgeSet ⊆ M.closure H₃.edgeSet` gives `r(H) ≤ r(H₃)`; combine with the
   landed lower bound for the equality, and pin both `\lean{}` names on the node.
2. **S5 (medium):** `lem:genericMatroid-induce-transport` (indep-iff +
   rank form, general `d`) via the landed forward/reverse row transports
   at `φ = Subtype.val`.

Then the `thm:jacobs` assembly (strong induction on `edgeFinset.card`),
then `sec:jacobs-degree-one` (L2: `thm:degree-one-rank-tree` and
`thm:degree-one-rank`; consumes S4 + S5 + the single-edge rank base).
`sec:jacobs-easy` (D-track) is already fully green and independent of all
of the above.

## Decisions made during this phase

- **S4 upper-bound crux fact (a) landed (2026-07-16).** `SimpleGraph.indep_k5_sub_edge`
  (`JacobsZeroExtension.lean`): `K₅` minus an edge is independent in
  `genericRigidityMatroid V 3`, for five pairwise-distinct named vertices. Built
  from the empty graph by four applications of a new private step lemma
  (`indep_zero_extension_star`: attaching a fresh isolated vertex's star to
  ≤ 3 already-placed vertices preserves independence, via S3's iff) plus a
  companion (`incidenceSet_sup_star_eq_empty`) that propagates each vertex's
  isolation through one more star without recomputing it. Stated the target
  edge set in the orientation the construction naturally produces (no
  `Sym2.eq_swap` needed for the final identification) rather than a "readable"
  alphabetical order. Technique promoted to TACTICS-GOLF § 20.
- **S4 lower bound landed (2026-07-16).** `zero_extension_genericRank_add_min_le`
  (`JacobsZeroExtension.lean`): `r(H - E_H(v)) + min 3 (d_H(v)) ≤ r(H)`, no clique
  hypothesis. `d ≤ 3`: the S3 equality plus `min 3 d ≤ d`. `d ≥ 4`: restrict the
  star to three neighbours via
  `H₃ = H.deleteEdges (E_H(v) ∖ {vu₁,vu₂,vu₃})` — `H₃ ≤ H`,
  `(H₃ - E_{H₃}(v)).edgeSet = (H - E_H(v)).edgeSet`, `d_{H₃}(v) = 3` — so S3 gives
  `r(H₃) = r(H-E_H(v)) + 3`, and `r(H₃) ≤ r(H)` by `Matroid` rank monotonicity.
  Three-neighbour pick via `neighborFinset` + `Finset.exists_subset_card_eq`
  (FRICTION / TACTICS-QUIRKS § 83: not `Set.toFinset` + ad-hoc `Fintype.ofFinite`).
  The `set`-bound `starEdges`/`D` characterised by explicit membership iffs to
  dodge defeq-through-`set` accessor issues.
- **S3 closed in one commit (2026-07-16).** New file `JacobsZeroExtension.lean`:
  `zero_extension_genericRank_add_degree` (rank formula) +
  `zero_extension_indep_iff_of_degree_le_three` (indep iff), both stated with a plain
  `Set.ncard` degree hypothesis (no dangling `[Fintype …]` in the signature — a local
  Fintype instance is derived from `[Finite V]` only where the S2 lift needs one). Rank
  formula: upper bound via `Matroid.rk_union_le_rk_add_rk` on the disjoint
  `H'.edgeSet ∪ H.incidenceSet v` decomposition (`Set.diff_diff_cancel_left` identifies
  the star `H.edgeSet \ H'.edgeSet` with `H.incidenceSet v`, cardinality `deg` via
  `incidenceSetEquivNeighborSet`); lower bound builds a witness graph
  `H₃ := H.deleteEdges (H'.edgeSet \ J)` carrying a matroid basis `J` of `H'.edgeSet`
  plus the full star at `v` (`Set.diff_diff_right` + `Set.inter_eq_right` compute
  `H₃.edgeSet`), shows `H₃.deleteIncidenceSet v` has edge set exactly `J` and
  `H₃.neighborSet v = H.neighborSet v` (via `mk'_mem_incidenceSet_left_iff`), then
  applies the landed `zero_extension_edgeSetRowIndependent_lift` at a placement
  simultaneously generic and in general position. New reusable helper
  `edgeSetRowIndependent_univ_iff_top` (`RigidityMatroid.lean`) reconciles a graph's own
  `Set.univ`-relative row-independence with `(⊤ : SimpleGraph V)`'s, via
  `rigidityRow_congr` — needed to move `J`'s matroid independence into the S2 lift's
  hypothesis and back. Two FRICTION entries (TACTICS-QUIRKS § 82: `rw` reused
  symmetrically across an `Iff`'s two unlike-shaped sides; and a `classical`/
  `incidenceSetEquivNeighborSet` decidability gotcha).
- **S2 closed in one commit (2026-07-16).** `_extend` (conditional core) + `_lift`
  (pins the node) in `RigidityMatroid.lean`. Key shapes: `_extend` takes an arbitrary
  `p` agreeing with `p'` off `v` (not `Function.update`), so no `[DecidableEq V]`; a
  single test-motion detector `Ψ := (LinearMap.single ℝ _ v).dualMap` kills the
  non-incident rows and sends each star row to `innerₗ` of its displacement, yielding
  both star-row LI (`.of_comp`) and the `LinearIndepOn.union` disjointness (new mirror
  helper `LinearIndependent.disjoint_span_range_ker`, converse of `LinearIndependent.map`
  — see FRICTION). `_lift` picks `q` off the neighbor images' affine hull and gets
  displacement-LI by the `∑ cᵤ = 0` split. `mem_edgeSet`/`mem_neighborSet` `Iff.rfl`
  trap (TACTICS-QUIRKS § 75) recurred — used defeq, never `rw`'d `he` in a goal subterm.

- **S1 closed in one commit (2026-07-11).** The four graph-theory nodes
  landed in `SquareGraph.lean` (`square_deleteIncidenceSet_of_degree_le_one`,
  `neighborSet_square_of_degree_eq_one` + its `ncard`/`IsClique` companions,
  `square_support_subset` + `square_induce_of_support_subset`) and
  `Jacobs.lean` (`IsLaman3.induce`), plus `square_mono`. Two proof shapes
  worth flagging for S2+: (a) `mem_commonNeighbors`/`mem_edgesIn` are
  `Iff.rfl`, so `.mpr ⟨…⟩` on them can hit the already-documented
  TACTICS-QUIRKS § 75 "Unknown constant" dot-notation trap — supply the
  underlying conjunction directly instead; (b) a hypothesis surviving a
  `Set.mem_singleton_iff`-style `simp only` unfold can present as a bare
  `_ = _ → False` rather than a foldable `Ne`, breaking `.symm` dot notation
  the same way — use `fun h => hyp h.symm` instead of `hyp.symm`.
- **Zero-extension recon + design pass (2026-07-11).** The chapter-open
  unconditional `min(3, d)` rank form was refuted (`K₁,₄` has rank 4, not
  `0 + 3`), and the lift lemma gained an affine-independence hypothesis on
  the neighbor images (`K₅ − e` placed with coincident endpoints refutes
  the bare form already at `s = 2`). Split: `cor:zero-extension-degree-le-three`
  (unconditional; `thm:jacobs`'s form) + `cor:zero-extension-clique-rank`
  (`min(3, d)` under a neighborhood clique — JJ's own "complete (and hence
  rigid)" condition, Thm 4.3 proof; upper bound by a K₅-closure argument).
  Induce-transport strengthened to the rank form (L2 uses it inside a rank
  formula); three new red support-restriction nodes; Whiteley 9.1.3
  verified fixed-placement / `s = 3` in `.refs/`.
- **L1 recon verdict (2026-07-10, accepted).** "G² is Laman" is *not*
  `IsSparse 3 6`: the `(k,ℓ)` guard `ℓ ≤ k·|s|` admits `|s| = 2` where
  the bound is 0, failing on every graph with an edge (compiled K₂
  refutation witness); JJ's condition guards `|X| ≥ 3`. Pinned as the
  standalone `SimpleGraph.IsLaman3`. JJ Thm 5.3 pinned against
  `G.shadowGraph.deficiency 3` — which *is* JJ's `def(G)` at `D = 6`
  (`partitionDef 3` unfolds to `6(|P|−1) − 5·d_G(P)` by `rfl`) — and
  Jacobs as `(genericRigidityMatroid V 3).Indep G.square.edgeSet ↔
  IsLaman3 G.square`.
- **Scope reductions found by the recon.** JJ Lemma 3.1 / Thm 3.4 /
  Thm 4.1 (2-thin covers, the rank *upper* bound) are not needed —
  `molecule_rank_upper_bound` already covers that limb via KT. JJ
  Lemma 3.2 is consumed in reduced forms only (chapter
  `fmlnote:tight-partition-consumed-forms`): 3.2(a) as a subfamily
  inequality on `G` itself, 3.2(b) as the part dichotomy proved by a
  single-vertex split — no induced-subgraph deficiency objects.
- **Thm 5.4 is thinner in the paper than in Lean.** The max-degree-3
  core reduction is asserted without proof in JJ; it rests on the
  0-extension lemma (Whiteley 1996 Lemma 9.1.3, verified in `.refs/`),
  the identity `(G − E(v))² = G² − E(v)` for `deg v ≤ 1`, and a
  support-restriction transport — all tracked as chapter nodes
  (`sec:jacobs-zero-extension`), shared with L2 (the degree-1 rank
  formula, grouping 2's second target). The 0-extension rank form is
  `min(3, d)` (L2's trees have unbounded neighbor degree; the indep-iff
  conjunct holds only for `d ≤ 3`).
- **Coordinator adjudications (2026-07-10):** standalone predicate (no
  refactor of `IsSparse`'s guard — Phase 1 API untouched); B-track
  tight-partition arithmetic stated D-generically (`Graph α β`,
  parameter `n`, `Deficiency.lean` house style); `lem:normal-cross-count`
  one node + fmlnote, sub-split at build time.
- **New attributions verified:** Jacobs 1998 (J. Phys. A **31**,
  6653–6668) and Franzblau 2000 (Discrete Appl. Math. **101**, 131–155)
  added to the bibliography; JJ Lemma 3.2 credited to the
  Jackson–Jordán companion paper via the 2008 statement (no separate
  bib entry — its published details not independently verified).
- **`sec:jacobs-counting`'s development (2026-07-10/11, ~15 commits) is
  fully settled** — the tight-partition-cross-pair split, the shadow-carrier
  bridge, the classification's disjoint-union + moreover clause, the
  singleton-part-neighborhood direct/converse split, and the
  normal-cross-count double count (steps i–iv). No forward-looking detail
  remains; see `git log` and `JacobsCounting.lean`'s module docstring for
  the lemma-by-lemma build order and technique notes.
- **`squareInPartEdges`/`squareNormalCrossEdges`/`squareSpecialCrossEdges`
  classification decompositions (2026-07-11).** Assembling
  `thm:laman-square-count` surfaced that the classification's four edge
  classes didn't all decompose *over `partLabels f`* yet — only
  `squareGCrossEdges` did (directly, as `d_G(P)`). Landed the missing
  three-class decomposition across two commits, each via the same
  `_eq_biUnion` / `_pairwiseDisjoint` / `sum_ncard_...` trio (mirroring
  the earlier `squareNormalCrossEdgesRootedAt` shape). For the
  special-cross class, redesigned from an earlier **witness-indexed**
  approach (index by singleton-part vertex `v`) to a **label-indexed**
  `squareSpecialCrossEdgesRootedAt` predicate (mirroring
  `squareNormalCrossEdgesRootedAt` exactly, uniqueness via
  `eq_of_common_nbr`) — this avoids a genuinely awkward label↔witness
  reindexing step the witness-indexed version would have needed to join
  the other two classes in one `partLabels f`-indexed sum. The three
  witness-indexed lemmas this superseded were not blueprint-pinned, so
  removed outright rather than left dead.
- **`thm:laman-square-count` assembly, closed in one commit (2026-07-11).**
  The per-part inequality (`IsSquareTightPartition.perPart_le`, additive
  form to avoid `ℕ`-subtraction) case-splits on the part-size dichotomy
  (`ncard_eq_one_or_three_le`): at `≥ 3` the Laman bound plus the *exact*
  normal-cross count (special-cross empty there); at a singleton the
  in-part and normal-cross counts are `0` and the special-cross count is
  *exactly* `2 deg_G(v) - 3`, matching `(3·1-6) + 2·gCutEdges(a).ncard`
  via `gCutEdges_singleton_part_ncard_eq_degree`. `Finset.sum_le_sum`
  plus the two handshakes fold this to `3|V| - 6t + 5d_G(P)`, matching
  `partitionDef 3 f`'s unfolding against `deficiency 3` exactly — plain
  `omega` closed the final mixed ℕ/ℤ goal directly (no `zify` needed).
  Two dot-notation/`subst`-direction traps hit along the way, both
  instances of already-documented patterns — see
  **FRICTION.md** *Two dot-notation/subst traps hit assembling
  `thm:laman-square-count`*, lifted to **TACTICS-QUIRKS § 4** (the
  `.symm`-flip fix) and **§ 35** (the `Eq`-headed dot-notation variant).
- **`thm:jacobs-min-degree-two` closed in one commit (2026-07-11).**
  `SimpleGraph.jacobs_min_degree_two`, new file `JacobsTheorem.lean` (kept
  separate from `JacobsCounting.lean`, which was already at the ~1500-LoC
  tripwire, and mirrors the blueprint's own `sec:jacobs-theorem` boundary).
  The recon-verified matroid bridge held exactly: `laman_square_count`
  (`≤`) against `molecule_rank_formula` (`=`) plus `Matroid.rk_le_toFinset_card`
  (rank `≤` cardinality, the always-true direction) sandwich `r(G²)` between
  `|E(G²)|` on both sides, forcing equality; `omega` closes the mixed ℕ/ℤ
  arithmetic, and `Matroid.indep_iff_eRk_eq_encard_of_finite` (not
  `Matroid.Indep.rk_eq_ncard`, which is the converse direction) converts
  rank-equals-cardinality to independence.
