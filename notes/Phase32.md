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

**Next concrete step** — see *Hand-off*.

## Work items

- **File placement (settled):** the `sec:jacobs-counting` classification /
  counting / Thm-5.3-assembly content lives in
  `CombinatorialRigidity/JacobsCounting.lean` (plain `import`, downstream
  of `Jacobs.lean` + `Molecular/{Deficiency,Molecule/Carrier}.lean`); the
  D-track row-independence lemmas live alongside their planar analogue in
  `RigidityMatroid.lean`.

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

- None. `thm:laman-square-count` is fully green; the next concrete task
  (`thm:jacobs-min-degree-two`) is a short corollary with no open design
  question (see *Hand-off*).

## Hand-off / next phase

**`thm:laman-square-count` (JJ Theorem 5.3) is fully green** —
`SimpleGraph.laman_square_count` in `JacobsCounting.lean`, blueprint
`\leanok`, `blueprint/verify.sh` green. See *Current state*.

**Next concrete commit: `thm:jacobs-min-degree-two`** (blueprint
`sec:jacobs-theorem`, line ~728) — Jacobs' conjecture at minimum degree
two: `G²` Laman ⟹ `E(G²)` independent in `𝓡₃(V)`. The blueprint proof is a
two-line chain: `|E(G²)| ≤ 3|V| - 6 - def(G̃) = r(G²) ≤ |E(G²)|` (via
`thm:laman-square-count` and `SimpleGraph.molecule_rank_formula`, already
landed in Phase 26), forcing equality, i.e. independence. The Lean-side
gap to check first: `(genericRigidityMatroid V 3).Indep S` needs a
bridge to `rank S = S.ncard` (a standard matroid fact — confirm the exact
mathlib/project lemma name, e.g. via `Matroid.rk`/`genericRank`'s
definitional relationship in `GenericRigidityMatroid.lean`) before the
arithmetic chain closes; this is new territory only in the sense of
"which existing matroid lemma to cite", not new proof content. Likely a
short (single-commit) corollary.

**Beyond that:** the full Jacobs' conjecture (`thm:jacobs`, no min-degree
hypothesis) needs the degree-≤1 vertex reduction — the `sec:jacobs-zero-extension`
chapter section (Whiteley 1996 Lemma 9.1.3, `.refs/`, and the identity
`(G − E_G(v))² = G² − E_{G²}(v)` for `deg v ≤ 1`) — and, per the phase
title, "the degree-1 rank formula" (grouping 2's second target, not yet
scoped in detail). Assess scope once `thm:jacobs-min-degree-two` lands.
`sec:jacobs-easy` (D-track) is already fully green and independent of
all of the above.

## Decisions made during this phase

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
