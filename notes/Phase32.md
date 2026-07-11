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

**Next concrete step** — see *Hand-off*.

## Work items

- **File placement (settled):** the `sec:jacobs-counting` classification /
  counting / Thm-5.3-assembly content lives in
  `CombinatorialRigidity/JacobsCounting.lean` (plain `import`, downstream
  of `Jacobs.lean` + `Molecular/{Deficiency,Molecule/Carrier}.lean`); the
  D-track row-independence lemmas live alongside their planar analogue in
  `RigidityMatroid.lean`.
- **Trivial glue for the zero-extension build** (coordinator adjudication:
  not chapter nodes): `square_mono` (`G' ≤ G → G'.square ≤ G.square`, feeds
  `IsLaman3.mono_left` in the `thm:jacobs` peel); edge-set bookkeeping for
  `SimpleGraph.map` / `induce` images under the transports; the single-edge
  rank base `r = 1` (L2's `K₂` base case).

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

- None. `thm:jacobs-min-degree-two` is fully green; the degree-≤1
  zero-extension reduction is scoped and slice-sized (S1–S5) — see
  *Hand-off*.

## Hand-off / next phase

**`thm:jacobs-min-degree-two` is fully green** —
`SimpleGraph.jacobs_min_degree_two` in `JacobsTheorem.lean`, blueprint
`\leanok`, `blueprint/verify.sh` green. See *Current state*.

**`sec:jacobs-zero-extension` is repaired and is the authoritative to-do
list** (all nodes red; recon + design pass 2026-07-11, see *Decisions
made*). Ordered slice plan, recon-sized:

1. **S1 (small — next concrete commit):** the graph-theory nodes:
   `lem:square-delete-degree-le-one`, `lem:square-leaf-neighborhood`,
   `lem:square-induce-support`, `lem:isLaman3-induce`, plus the trivial
   glue in *Work items*.
2. **S2 (hard):** `lem:zero-extension-rowIndependent` — an
   `_extend`/`_lift` pair mirroring `typeI_edgeSetRowIndependent_extend`
   but on fixed `V` (`Function.update`; needs a `rigidityRow`-update
   congruence for non-incident edges, NOT
   `linearIndependent_rigidityRow_lift_of_injective`) and a uniform
   `s ≤ 3` coefficient helper; the vsub-LI bridges in
   `GeneralPositionPlacement.lean` supply the difference-vector LI. Open
   choice at build time: graph-level vs set-level (basis + star) statement
   — graph-level suffices if the rank lower bound applies it to the
   spanning subgraph carrying a base plus the star.
3. **S3 (medium):** `cor:zero-extension-degree-le-three` — witness upgrade
   via `exists_isGenericPlacement_isGeneralPositionPlacement`, then
   matroid arithmetic.
4. **S4 (hard):** `cor:zero-extension-clique-rank` — lower bound from S3 +
   rank monotonicity; upper bound is the K₅-closure assembly (repeated S3
   applications on explicit 5-vertex subgraphs +
   `isLaman3_of_genericRigidityMatroid_indep` + `Matroid` closure API).
   May split lower/upper into two commits.
5. **S5 (medium):** `lem:genericMatroid-induce-transport` (indep-iff +
   rank form, general `d`) via the landed forward/reverse row transports
   at `φ = Subtype.val`.

Then the `thm:jacobs` assembly (strong induction on `edgeFinset.card`),
then `sec:jacobs-degree-one` (L2: `thm:degree-one-rank-tree` and
`thm:degree-one-rank`; consumes S4 + S5 + the single-edge rank base).
`sec:jacobs-easy` (D-track) is already fully green and independent of all
of the above.

## Decisions made during this phase

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
