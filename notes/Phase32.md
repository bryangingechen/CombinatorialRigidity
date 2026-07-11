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
(`sec:jacobs`), built from the accepted L1 recon's node decomposition,
is the phase's authoritative dep-graph / lemma index. Status surfaces
(intro.tex, README, home_page) synced at chapter open. **The
`sec:jacobs-laman3` slice is landed**: `def:isLaman3`,
`lem:isLaman3-mono`, `lem:clique-edgesIn-count`,
`lem:isLaman3-degree-le-three` are green
(`CombinatorialRigidity/Jacobs.lean` — `SimpleGraph.IsLaman3`,
`.mono_left`, `.degree_le_three`; `CombinatorialRigidity/EdgesIn.lean`
— `SimpleGraph.IsClique.ncard_edgesIn`). **The `sec:jacobs-easy`
D-track is landed**: `lem:isLaman3-of-rowIndependent` (green as
`SimpleGraph.isLaman3_of_edgeSetRowIndependent_dim_three`,
`RigidityMatroid.lean`, mirroring `isSparse_of_edgeSetRowIndependent_dim_two`
one dimension up — `RigidityMatroid.lean` now `public import`s
`Jacobs.lean`) and `cor:genericMatroid-indep-isLaman3` (green as
`SimpleGraph.isLaman3_of_genericRigidityMatroid_indep`,
`GeneralPositionPlacement.lean`, after the lemmas it composes —
declaration order in that file matters, see `TACTICS-QUIRKS.md` § 8).
**The B-track's first four slices are landed**: `lem:exists-tight-partition`
(green as `Graph.IsTightPartition` / `Graph.exists_isTightPartition`),
`lem:partitionDef-merge` (green as `Graph.crossingEdgesWithin` /
`Graph.partitionDef_merge`), `lem:tight-partition-subfamily` (green
as `Graph.IsTightPartition.subfamily_le`), and `lem:tight-partition-parts`
(green as `Graph.IsTightPartition.parts`), all in `Molecular/Deficiency.lean`,
`## Tight partitions` section ahead of `rank_matroidMG_le`. The first two
are proved more general than the blueprint's literal hypotheses (no
`V(G).Nonempty` for the first, no `2 ≤ S.ncard` for the second — the
`Finite.exists_max` / merge-arithmetic route doesn't need them; each
docstring notes the generalization; see `lake lint`'s
`unusedArguments` linter for why dropping is the right call over
carrying a dead hypothesis). `subfamily_le`'s proof is exactly the route
the phase note predicted: collapse `S` via `fun x => if x ∈ S then a else x`,
apply `partitionDef_merge`, then `partitionDef_le_deficiency` + tightness
+ `linarith`. `parts`'s proof follows the route worked out last session
almost exactly (`exists_fresh_label` private helper, `Function.update`,
`partitionDef_congr` to recover `f` from the merge) — see *Decisions made*
for the two spots where the actual Lean pushed back on the plan.
**`lem:tight-partition-cross-pair`'s `D ≥ 3` edge-multiplicity half is
landed**, green as `Graph.IsTightPartition.crossingEdgesWithin_pair_le_one`
(`Molecular/Deficiency.lean`) — exactly the one-instance-of-`subfamily_le`-
at-`|Q| = 2` corollary the hand-off predicted. The blueprint node is split
into `lem:tight-partition-cross-pair-mult` (this half, green) and
`lem:tight-partition-cross-pair-nbr` (the `D ≥ 5` common-neighbor-uniqueness
half) per the "sliced producer" discipline (`blueprint/CLAUDE.md`
*Sliced producers*: one node can't claim a conjunction only half proved);
the three downstream proofs that cited the combined lemma
(`lem:square-cross-classification`, `lem:singleton-part-neighborhood`,
`lem:normal-cross-count`) have their `\uses`/`\cref` repointed to whichever
new label(s) they actually invoke. **`lem:tight-partition-cross-pair-nbr` is
now also landed**, green as `Graph.IsTightPartition.eq_of_common_nbr`
(`Molecular/Deficiency.lean`, right after `crossingEdgesWithin_pair_le_one`)
— proved more general than the blueprint's literal hypotheses (no
nonadjacency of `u, w`: the proof only ever uses `f u ≠ f w`; docstring notes
the generalization). This completes `sec:jacobs-tight-partitions` — every
node from `lem:exists-tight-partition` through `lem:tight-partition-cross-pair-nbr`
is green. **`lem:square-cross-classification` is now fully green** in a new file
`CombinatorialRigidity/JacobsCounting.lean`: the shadow-carrier bridge
(`IsSquareTightPartition`, `shadowGraph_adj_iff`, transported
`IsSquareTightPartition.eq_of_common_nbr` and `.parts`), the four edge-class
definitions (`squareInPartEdges` / `squareGCrossEdges` / `squareCrossEdges` /
`squareNormalCrossEdges` / `squareSpecialCrossEdges`), the disjoint-union
(`square_edgeSet_eq_union` + the `disjoint_*` trio; `squareCrossEdges_eq_union` +
`squareNormalCrossEdges_disjoint_special`), the count `squareGCrossEdges_ncard_eq_crossingEdges`
(the "numbering `d_G(P)`" clause + the Thm 5.3 crossing-count bridge), and the
*moreover* clause — `squareSpecialCrossEdges_singleton_part` (special common
neighbor is a singleton part, via the degree-4 contradiction against
`IsLaman3.degree_le_three`) and `squareNormalCrossEdges_part_three_le` (normal
common neighbor in a part of ≥3 with exactly one endpoint). Node pinned + `\leanok`
(9-name `\lean{}`), blueprint gates green. **`lem:singleton-part-neighborhood`'s
direct direction is now landed** (JJ eq. (5),(7); `\leanok`, 3-name `\lean{}`):
`SimpleGraph.isClique_neighborSet_square` (`SquareGraph.lean`, unconditional clique
fact), `SimpleGraph.ncard_edgesIn_neighborSet_square` (`Jacobs.lean`, the count
`2 d_G(v) - 3`, also unconditional — see *Decisions made*), and
`SimpleGraph.IsSquareTightPartition.mem_squareSpecialCrossEdges_of_singleton_part`
(`JacobsCounting.lean`, the per-pair "special cross edge with common neighbor `v`"
fact, via two new shadow-transported lemmas `IsSquareTightPartition.not_adj_adj_of_same_part`
/ `.not_adj_triangle`). The blueprint's "conversely...exactly one singleton part"
sentence split out to a new sibling node `lem:singleton-part-converse`, per the
sliced-producer discipline (the direct and converse directions are logically
independent conjuncts). **`lem:singleton-part-converse` is now also landed**, green as
`SimpleGraph.exists_unique_singleton_part_of_mem_squareSpecialCrossEdges`
(`JacobsCounting.lean`) — see *Hand-off* for the proof shape. **Next concrete step** —
see *Hand-off*.

## Work items

The chapter's red nodes are the to-do list. Lean-side glue the chapter
deliberately does not track (blueprint selectivity), to land inside the
slices that need it:

- shadow-carrier crossing-count bridge: *landed* — `shadowGraph_adj_iff`
  (adjacency) and `squareGCrossEdges_ncard_eq_crossingEdges`
  (`(G.squareGCrossEdges f).ncard = (G.shadowGraph.crossingEdges f).ncard =
  d_G(P)`), both via the `Sum.inl s(·,·)` injection from the `Sym2 V` set
  into the shadow-label set (the recurring shadow-count idiom of this file);
- part-Finsets from a labeling `f : V → V` (fibers restricted to the
  label image) + the partition handshake `∑ parts d_G(P_i) = 2·d_G(P)`
  (still pending, for the Thm 5.3 assembly);
- **file placement (settled):** the `sec:jacobs-counting` classification
  / counting content lives in the new sibling file
  `CombinatorialRigidity/JacobsCounting.lean` (plain, downstream of
  `Jacobs.lean` + `Molecular/{Deficiency,Molecule/Carrier}.lean`); the
  D-track row-independence lemmas already landed alongside their planar
  analogue in `RigidityMatroid.lean`.

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

- None. `fmlnote:normal-cross-split` records the one node expected to
  sub-split during formalization (`lem:normal-cross-count`); split at
  the seam when it arrives.

## Hand-off / next phase

**`lem:singleton-part-converse` is landed**, green as
`SimpleGraph.exists_unique_singleton_part_of_mem_squareSpecialCrossEdges`
(`JacobsCounting.lean`, right after `mem_squareSpecialCrossEdges_of_singleton_part`) — the
predicted shape held exactly: existence unfolds `squareSpecialCrossEdges` membership (induct on
`e`) to the apex `v`, applies `squareSpecialCrossEdges_singleton_part` for the singleton-part half
and `mk_mem_edgesIn` for the `edgesIn`-membership half; uniqueness is one call to
`IsSquareTightPartition.eq_of_common_nbr`. The flagged `Sym2`/`Set`-coercion risk on
`mem_edgesIn`'s `(e : Set V) ⊆ s` conjunct resolved cleanly with `Sym2.coe_mk` +
`Set.insert_subset_iff` + `Set.singleton_subset_iff`. The theorem carries an explicit
`hlaman : G.square.IsLaman3` hypothesis (needed by `squareSpecialCrossEdges_singleton_part`,
matching the section's standing "square is Laman" assumption), which the hand-off sketch omitted
naming.

**Next concrete commit:** `lem:normal-cross-count` (JJ eq. (6), `sec:jacobs-counting`, the
`fmlnote:normal-cross-split` node — sub-split at the seam per the fmlnote) and the part-Finset +
handshake glue, feeding `thm:laman-square-count` (Thm 5.3) and the rest of
`sec:jacobs-counting`. `sec:jacobs-zero-extension` / `sec:jacobs-theorem` /
`sec:jacobs-degree-one` wait on those. Both prior tracks are fully discharged (D-track; B-track
tight-partition machinery) — `sec:jacobs-counting` is the only remaining work.

## Decisions made during this phase

- **L1 recon verdict (2026-07-10, accepted).** "G² is Laman" is *not*
  `IsSparse 3 6`: the `(k,ℓ)` guard `ℓ ≤ k·|s|` admits `|s| = 2` where
  the bound is 0, failing on every graph with an edge (compiled K₂
  refutation witness); JJ's condition guards `|X| ≥ 3`. Pinned as the
  standalone `SimpleGraph.IsLaman3`. JJ Thm 5.3 pinned against
  `G.shadowGraph.deficiency 3` — which *is* JJ's `def(G)` at `D = 6`
  (`partitionDef 3` unfolds to `6(|P|−1) − 5·d_G(P)` by `rfl`) — and
  Jacobs as `(genericRigidityMatroid V 3).Indep G.square.edgeSet ↔
  IsLaman3 G.square`. The Thm 5.3 + rank-formula ⇒ `|E| ≤ r` assembly
  arithmetic compiled against the landed surface.
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
  (`sec:jacobs-zero-extension`), shared with L2. The 0-extension rank
  form is `min(3, d)` (L2's trees have unbounded neighbor degree; the
  indep-iff conjunct holds only for `d ≤ 3`).
- **Coordinator adjudications (2026-07-10):** standalone predicate (no
  refactor of `IsSparse`'s guard — Phase 1 API untouched); B-track
  tight-partition arithmetic stated D-generically (`Graph α β`,
  parameter `n`, `Deficiency.lean` house style); `lem:normal-cross-count`
  one node + fmlnote, sub-split at build time.
- **`lem:tight-partition-cross-pair` split into `-mult`/`-nbr` (blueprint).**
  The `D ≥ 5` common-neighbor half needs a genuine multi-branch case analysis
  (see the `eq_of_common_nbr` entry below), so once only the `D ≥ 3` half was
  proved, one node couldn't carry `\leanok` for both — the "sliced producer"
  discipline (`blueprint/CLAUDE.md`) applies to a plain lemma's conjunction,
  not just producer statements. Chose to rename/split the node outright (not
  append a sibling) so no node ever claims the full conjunction; the three
  downstream proofs citing the combined lemma had their `\uses`/`\cref`
  repointed in the same commit.
- **`lem:tight-partition-cross-pair-nbr` (`Graph.IsTightPartition.eq_of_common_nbr`).**
  Proved more general than JJ's hypotheses: `u, w` need not be nonadjacent,
  only `f u ≠ f w` (unused elsewhere in the proof). Route: `by_contra` on
  `v ≠ v'`, establish the four canonical edges `uv, vw, uv', v'w` pairwise
  distinct (all of `u, v, w, v'` are pairwise distinct off `Loopless` +
  `f u ≠ f w`, so no two edges share an endpoint pair — new structural
  helper `isLink_ne_of_ne_ends`), then a 9-leaf case split on which of
  `f u, f v, f w, f v'` coincide, each leaf closing via one of three factored
  helpers (`false_of_two_crossing` / `_three_crossing` / `_four_crossing`,
  instances of `crossingEdgesWithin_pair_le_one` / `subfamily_le` at 2/3/4
  labels) — the `D ≤ |Q| ≤ 4` contradiction is uniform across leaves given
  `D ≥ 5`, so the leaves differ only in which labels/edges witness it.
- **`lem:tight-partition-parts` (`Graph.IsTightPartition.parts`).** The
  planned route held, but the ≥3-vertex half is proved via a general
  injective-map cardinality bound (in-part edges of `v` inject into
  the rest of the part via `G.Simple.eq_of_isLink`, so their count is
  ≤ part-size − 1) rather than the planned ad-hoc `|A| = 2` exclusion
  — cleaner and gives the bound for any part size at once. Two Lean
  potholes hit were both already-logged patterns (no new FRICTION
  entries): `subst` on `x = v` eats `v` not `x` (TACTICS-QUIRKS § 4;
  worked around with `rw [hxv]` on the goal instead), and a
  goal-changing `show` trips the `linter.style.show` gate (FRICTION
  *A goal-changing `show`…*; worked around with `simp only
  [Function.comp_apply]` before the `rw` chain).
- **New attributions verified:** Jacobs 1998 (J. Phys. A **31**,
  6653–6668) and Franzblau 2000 (Discrete Appl. Math. **101**, 131–155)
  added to the bibliography; JJ Lemma 3.2 credited to the
  Jackson–Jordán companion paper via the 2008 statement (no separate
  bib entry — its published details not independently verified).
- **`sec:jacobs-counting` encoding, settled (`JacobsCounting.lean`).** (b) Bridge:
  `IsSquareTightPartition G f := G.shadowGraph.IsTightPartition 3 f` (`bodyBarDim 3 =
  6` = JJ's `D`); `shadowGraph_adj_iff` (`G.shadowGraph.Adj = G.Adj`) transports the
  tight-partition lemmas to `SimpleGraph`/`f : V → V` — the one the classification
  needs, `eq_of_common_nbr` (unique common neighbor), landed. (a) The four classes are
  `Set (Sym2 V)` (so `|E(G²)|` sums their `ncard`), split by `(e.map f).IsDiag` (same
  part) and `e ∈ G.edgeSet`; normal/special carry `∃ v, (∀ z ∈ e, G.Adj z v) ∧ f v
  ∈/∉ e.map f` — disjoint via `eq_of_common_nbr`, cover via common-neighbor existence.
- **`lem:square-cross-classification` moreover clause + count, green.** Special
  singleton (`squareSpecialCrossEdges_singleton_part`): the special edge's two
  endpoints + (if the part were non-singleton) two in-part neighbors (`.parts`)
  give `v` degree ≥ 4, contra `degree_le_three` — no min-degree needed. Normal
  ≥3 (`squareNormalCrossEdges_part_three_le`): the shared-part endpoint is an
  adjacent distinct part-mate, so `.parts` gives ≥3; "exactly one endpoint" is
  cross+normal. Transported `.parts` and the count bridge both use the recurring
  **shadow-count idiom**: a shadow edge set = `Sum.inl s(·,·) '' (Sym2 V set)`, so
  `Set.InjOn.ncard_image` transfers the count (edge↔neighbor, `squareGCross`↔`crossingEdges`).
- **D-track file placement, settled by the import DAG.**
  `lem:isLaman3-of-rowIndependent` needs only `EdgeSetRowIndependent`
  and `rigidityMap_finrank_range_le_of_affinelySpanning`, so it goes in
  `RigidityMatroid.lean` alongside its dim-2 analogue, per the file's
  own convention of housing row-independence results next to the
  machinery even when the predicate (`IsLaman3`) is defined elsewhere
  (`Jacobs.lean`, now `public import`ed by `RigidityMatroid.lean` — no
  cycle, since `Jacobs.lean` is a leaf). `cor:genericMatroid-indep-isLaman3`
  needs `genericRigidityMatroid`/`IsGeneralPositionPlacement`, both
  *downstream* of `RigidityMatroid.lean`, so it cannot live there too —
  it lands in `GeneralPositionPlacement.lean` instead, which already
  transitively re-exports `IsLaman3` through the same import chain.
- **The count `2 d_G(v) - 3` is unconditional on the partition.** Realized while
  scoping `lem:singleton-part-neighborhood`: `N_G(v)`'s clique-of-`G²` property
  (`isClique_neighborSet_square`, new one-liner in `SquareGraph.lean` — restrict
  `isClique_closedNeighborSet_square` from `N[v]` to `N(v) ⊆ N[v]`) and the degree
  bound `d_G(v) ∈ {2,3}` (`IsLaman3.degree_le_three` + min-degree-two) never mention
  `f`/tight partitions, so the count itself doesn't either — only the *edge-type*
  classification (special cross, common neighbor `v`) needs the partition. Landed the
  count as `SimpleGraph.ncard_edgesIn_neighborSet_square` in `Jacobs.lean` (next to
  `degree_le_three`, its only real dependency) rather than `JacobsCounting.lean`.
- **`lem:singleton-part-neighborhood` split (blueprint).** The blueprint statement's
  last sentence ("every special cross edge arises this way from exactly one
  singleton part") is a logically independent conjunct from the "clique + special +
  count" content, so it moved to a new sibling node `lem:singleton-part-converse`
  (red) rather than forcing one node to carry `\leanok` for both — same
  sliced-producer call as the earlier `-cross-pair` split. `thm:laman-square-count`'s
  `\uses` picked up the new node alongside the original.
- **`IsSquareTightPartition.not_adj_adj_of_same_part` / `.not_adj_triangle`**
  (`JacobsCounting.lean`) transport `Graph.IsTightPartition.crossingEdgesWithin_pair_le_one`
  / `.subfamily_le` through the shadow carrier, mirroring `eq_of_common_nbr`'s
  transport but constructing the needed shadow-edge memberships by hand (`Sum.inl
  s(x,y) ∈ crossingEdgesWithin f S`, a new `private` helper) rather than reusing
  `eq_of_common_nbr`'s internal (non-exported) case-split helpers. **Elaboration
  pothole:** passing a rigid `Eq`-typed term (e.g. `hfuw.symm`) as the second
  disjunct of a `Set.mem_insert_iff.mpr (Or.inr ·)` proof fails when the target
  set `S` is itself an unconstrained implicit (no other argument pins it) — the
  membership goal's expected type isn't known before elaborating the term, unlike
  `rfl`, which unifies regardless. Fixed by naming `(S := {...})` explicitly at
  each call site.
