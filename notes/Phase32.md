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
(`JacobsCounting.lean`). **The `lem:normal-cross-count` node is now split and its first two
arms landed**: the `squareNormalCrossEdgesRootedAt` definition + root-uniqueness
(`SimpleGraph.IsSquareTightPartition.rootedAt_inj`, blueprint `lem:normal-cross-count-rooted`)
and the local count (`SimpleGraph.IsSquareTightPartition.ncard_inPartNeighbors_eq_two`,
blueprint `lem:normal-cross-count-local`), both in `JacobsCounting.lean`. **The producer brick is
now also green**: `SimpleGraph.IsSquareTightPartition.mk_mem_squareNormalCrossEdgesRootedAt`
(blueprint `lem:normal-cross-count-producer`) — a crossing edge `vw` at a part plus an in-part
neighbor `u` of `v` yields `s(u,w) ∈ squareNormalCrossEdgesRootedAt f (f v)` with `v` its unique
common neighbor (the map `(vw, u) ↦ uw` of the double count). **Steps (i)+(ii) of the fiber-sum
are now landed too**: the single-label cut set `SimpleGraph.gCutEdges` (blueprint `def:g-cut-edges`,
the `d_G(A)` base) and the per-crossing-edge fiber lemma
`IsSquareTightPartition.ncard_normalCrossEdges_of_crossing_eq_two` (blueprint
`lem:normal-cross-count-fiber`) — each crossing edge `vw` at a big part yields exactly two rooted
normal cross edges `s(u,w)`, a size-2 subset of `squareNormalCrossEdgesRootedAt f (f v)`.
**Step (iii), the disjoint cover, is now landed too** (blueprint `lem:normal-cross-count-partition`,
green): the oriented-crossing-edge index `SimpleGraph.squareCutPairs` + its bijection with the cut
edges `ncard_squareCutPairs_eq_gCutEdges` (= `d_G(A)`), the cover
`IsSquareTightPartition.squareNormalCrossEdgesRootedAt_eq_biUnion`, and the disjointness
`IsSquareTightPartition.squareCutPairs_pairwiseDisjoint`. **`lem:normal-cross-count` is now fully
green** — step (iv), the disjoint-union `ncard` sum, closed as
`SimpleGraph.IsSquareTightPartition.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges`
(`JacobsCounting.lean`): `Set.Finite.ncard_biUnion` against the biUnion + disjointness of step
(iii), a per-fiber rewrite to `2` (via a big-part witness from `hbig` fed to the step-(i)/(ii)
fiber lemma), then `finsum_one` + `mul_finsum_mem` to fold the constant sum to
`2 * (squareCutPairs f a).ncard`, then the step-(iii) bijection to `2 * (gCutEdges f a).ncard`.
This closes `sec:jacobs-counting`'s last red node and its `fmlnote:normal-cross-split` decomposition
in full. **The part-Finset / handshake infrastructure for the Thm 5.3 assembly is now also
landed** (`CombinatorialRigidity/JacobsCounting.lean`): `SimpleGraph.partLabels` (the finite label
set of a partition `f : V → V`, packaged as a `Finset V` via `Set.Finite.toFinset` since `V` need
not carry a `Fintype` instance) and `SimpleGraph.sum_gCutEdges_eq_two_mul_squareGCrossEdges`
(`∑ a ∈ partLabels f, d_G(a) = 2 · d_G(P)`, JJ's `∑_i d_G(P_i) = 2 d_G(P)`), proved by
double-counting the oriented cross pairs `(v, w)` (`G.Adj v w`, `f v ≠ f w`) two ways —
fibering by the part `f p.1` recovers the per-part cut sets (already known to number `d_G(A)`,
`ncard_squareCutPairs_eq_gCutEdges`); fibering by the edge `s(p.1, p.2)` is 2-to-1 onto the
`G`-cross edges (`Finset.card_eq_sum_card_fiberwise`, applied twice, mirroring
`SimpleGraph.sum_degrees_eq_twice_card_edges`'s dart-based proof). No blueprint node — this is
Lean-side glue the chapter deliberately does not track (see *Work items*). **The companion
vertex handshake and the per-part edge bound are now also landed**: `SimpleGraph.sum_ncard_eq_card`
(`∑ a ∈ partLabels f, |P_a| = Nat.card V`, JJ's `∑_i |P_i| = |V|`, the 1-to-1 analogue of the edge
handshake's fiberwise-count idiom), `SimpleGraph.edgesIn_square_part_le` (the big-part case,
`|E(G²) ∩ P_a| + 6 ≤ 3|P_a|` at `|P_a| ≥ 3`, a direct application of the new
`SimpleGraph.IsLaman3.ncard_edgesIn_le` in `Jacobs.lean` — the Laman bound restated for a `Set V`
rather than a `Finset V`) and `SimpleGraph.edgesIn_square_singleton_part_eq_zero` (the singleton
case, `|E(G²) ∩ P_a| = 0`, directly from `edgesIn_singleton` — no partition structure needed).
**The `squareInPartEdges` classification-decomposition brick is now also landed**
(`squareInPartEdges_eq_biUnion`, `squareInPartEdges_pairwiseDisjoint`,
`sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges`): `squareInPartEdges f` — `E(G²)`'s in-part
class — is the disjoint union, over `partLabels f`, of the per-part in-part edge sets
`G.square.edgesIn {x | f x = a}`, and its `ncard` sums to their per-part counts exactly (1-to-1,
no factor of two — an in-part edge belongs to exactly one part, unlike the cross classes'
handshakes). This was discovered while attempting the full `thm:laman-square-count` assembly:
it is genuinely new infrastructure the previous hand-off's three-step sketch didn't name (see
*Decisions made*). **Next concrete step** — see *Hand-off*.

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
  label image) + the partition handshake `∑ parts d_G(P_i) = 2·d_G(P)`:
  *landed* — `SimpleGraph.partLabels`, `SimpleGraph.sum_gCutEdges_eq_two_mul_squareGCrossEdges`
  (`JacobsCounting.lean`); see *Current state*;
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

- None. `sec:jacobs-counting` is fully green and the part-Finset/handshake infrastructure it
  needed is landed (see *Current state*); the residual work is assembling
  `thm:laman-square-count` (Thm 5.3) itself, not blocked on any open question.

## Hand-off / next phase

**`sec:jacobs-counting` is fully green.** `lem:normal-cross-count` closed as
`SimpleGraph.IsSquareTightPartition.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges`
(`JacobsCounting.lean`) — see *Current state*. Every node in the section (classification,
singleton-part count + converse, normal-cross-count and its five sub-nodes) is green.

**The part-Finset / handshake infrastructure is landed** (`SimpleGraph.partLabels`,
`SimpleGraph.sum_gCutEdges_eq_two_mul_squareGCrossEdges` — see *Current state*).

**The companion vertex handshake and the per-part edge bound are landed**
(`SimpleGraph.sum_ncard_eq_card`, `SimpleGraph.edgesIn_square_part_le`,
`SimpleGraph.edgesIn_square_singleton_part_eq_zero`, `SimpleGraph.IsLaman3.ncard_edgesIn_le` in
`Jacobs.lean` — see *Current state*). This closes items (a) and (b) of the previous hand-off.

**Recon correction (2026-07-11): the previous hand-off's "(a) handshake, (b) per-part bound, (c)
assemble" sketch undersold the work.** Attempting the assembly this session surfaced a missing
step between the classification (`square_edgeSet_eq_union`/`squareCrossEdges_eq_union`, which
splits `E(G²)` into four edge classes: in-part, `G`-cross, normal-cross, special-cross) and the
existing per-class counts: **two of the four classes don't yet decompose *over `partLabels f`*
at all.** `squareGCrossEdges` does (`squareGCrossEdges_ncard_eq_crossingEdges` gives its `ncard`
directly as `d_G(P)`, no per-part sum needed). But `squareNormalCrossEdges` only has a per-*fixed*-part
count (`ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges`, one `a` at a time) — summing it over
all parts needs its own `squareNormalCrossEdges = ⋃ a ∈ partLabels f, squareNormalCrossEdgesRootedAt f a`
decomposition (disjoint via `rootedAt_inj`), not yet built. `squareSpecialCrossEdges` has no
per-part indexing at all yet (only `exists_unique_singleton_part_of_mem_squareSpecialCrossEdges`,
an `∃!`-form fact about individual edges). **`squareInPartEdges`'s decomposition is the one class
this commit lands** (`squareInPartEdges_eq_biUnion`, `squareInPartEdges_pairwiseDisjoint`,
`sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges` — see *Current state*), using
`Set.Finite.ncard_biUnion` + `finsum_mem_coe_finset` (a route not previously used in this file;
the cross-class handshakes instead double-count via ordered `V × V` pairs, since a cross edge
belongs to *two* parts — an in-part edge belongs to exactly one, so the direct biUnion route
applies and needs no factor-of-two bookkeeping. See *Decisions made*).

**The remaining pieces, in dependency order (reassess commit-sizing as each lands):**
1. ~~`squareInPartEdges` decomposition~~ — done this commit.
2. `squareNormalCrossEdges` decomposition over `partLabels f` — mirrors (1)'s shape but
   disjointness comes from `rootedAt_inj` (distinct parts can't both root the same edge) rather
   than the trivial label-uniqueness (1) used.
3. `squareSpecialCrossEdges` decomposition over the *singleton-part witnesses* — index by
   `v : V` with `∀ x, f x = f v → x = v` (not by `partLabels f` directly, though the two index
   sets are in bijection via `f`); the producer half is
   `IsSquareTightPartition.mem_squareSpecialCrossEdges_of_singleton_part`, the disjointness/cover
   half is `exists_unique_singleton_part_of_mem_squareSpecialCrossEdges`. Comparable in size to
   (1)/(2); the newest territory of the three.
4. Two small per-part facts the closing inequality needs: `(G.gCutEdges f a).ncard = G.degree v`
   at a singleton part `{v}` (`f v = a`) — every edge at `v` qualifies as a cut edge, since its
   other endpoint is automatically outside the singleton part; and
   `G.squareNormalCrossEdgesRootedAt f a = ∅` when `{x | f x = a}.ncard < 3` — direct from
   `squareNormalCrossEdges_part_three_le`'s contrapositive.
5. The per-part inequality itself: `inPart(a) + rooted(a) + special(a) ≤ (3|P_a| - 6) +
   2·(gCutEdges f a).ncard`, case-split singleton vs. `≥ 3` per part (no size-2 part exists,
   `IsSquareTightPartition.parts`) — at a big part it's `edgesIn_square_part_le` (≤) plus the
   *exact* `ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges` (special(a) = 0, no root there);
   at a singleton part both sides are equal by construction (`ncard_edgesIn_neighborSet_square`
   reproducing `2 deg_G(v) - 3` against item 4's `gCutEdges` identity). Then `Finset.sum_le_sum`
   over `partLabels f`, then the closing `partitionDef`/`bodyBarDim 3 = 6` arithmetic
   (`partitionDef 3 f = 6 * (numParts f - 1) - 5 * crossingEdges` by `rfl`, per *Decisions made*)
   plus `linarith`/`omega`.

The `def(G̃) = 0` corner case (blueprint's opening sentence, `X = V` directly) is a separate,
simpler leg of the same proof, independent of items 1–5. `sec:jacobs-easy` (D-track) is
unaffected — it's already fully green and independent of Thm 5.3.

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
- **`lem:normal-cross-count` split (blueprint) + first two arms green.** The
  `fmlnote:normal-cross-split` node stabilized into three: `-rooted` (root unique via
  `eq_of_common_nbr` + big-part from the classification's moreover clause; pins the
  `squareNormalCrossEdgesRootedAt` def and `rootedAt_inj`), `-local` (a `v ∈ A` on a
  crossing edge has exactly two in-part neighbors — `ncard_inPartNeighbors_eq_two`,
  upper bound from the disjoint in-/out-of-part split of `N_G(v)` at size `d_G(v) ≤ 3`,
  lower from `IsSquareTightPartition.parts`), and the residual red `lem:normal-cross-count`
  (`2·d_G(A)` global assembly). No new friction (existing idioms).
- **Producer brick + sub-split of the count (2026-07-11).** The residual `2·d_G(A)`
  count is a fibered double count (each of `d_G(A)` crossing edges → 2 rooted normal
  cross edges, injectively) — new territory (no 2-to-1 `ncard` idiom in the tree), so
  it does not fit one clean commit. Landed the constructive core first:
  `mk_mem_squareNormalCrossEdgesRootedAt` (`lem:normal-cross-count-producer`), the map
  `(vw, u) ↦ uw`, mirroring the special-edge producer
  `mem_squareSpecialCrossEdges_of_singleton_part` (only `hf` needed — not `hlaman`/big
  part). Residual fiber-sum handed off (see *Hand-off*). No new friction.
- **Fiber-sum steps (i)+(ii) (2026-07-11).** Landed the `d_G(A)` base
  `SimpleGraph.gCutEdges` (`def:g-cut-edges`; `G`-edges `s(x,y)` with `f x = a`, `f y ≠ a` —
  exactly one endpoint in the part) and the per-crossing-edge fiber lemma
  `ncard_normalCrossEdges_of_crossing_eq_two` (`lem:normal-cross-count-fiber`): the image of
  `v`'s in-part neighbors under `u ↦ s(u,w)` is a size-2 subset of `squareNormalCrossEdgesRootedAt
  f (f v)` — ncard 2 via `Set.InjOn.ncard_image` (`u ↦ s(u,w)` injective, shared `w`, `u ≠ w`) +
  `-local`, subset via `-producer`. Residual steps (iii)+(iv) (disjoint cover + biUnion sum)
  handed off. No new friction (existing idioms).
- **Fiber-sum step (iii): the disjoint cover (2026-07-11).** Landed the oriented-crossing-edge
  index `squareCutPairs` (pairs `(v,w)`, `f v = a ≠ f w`, `G.Adj v w`), its bijection with the
  cut edges (`ncard_squareCutPairs_eq_gCutEdges` = `d_G(A)`), the cover
  (`squareNormalCrossEdgesRootedAt_eq_biUnion`, ⊇ by producer, ⊆ by the moreover clause), and the
  disjointness (`squareCutPairs_pairwiseDisjoint`, via `eq_of_common_nbr`) — blueprint
  `lem:normal-cross-count-partition`. Only step (iv), the `Set.Finite.ncard_biUnion` sum, remains
  (all inputs green; see *Hand-off*). Hit two known quirks: § 75 (`G.mem_edgeSet.mpr`, explicit
  structure arg) and § 4 (`rcases ⟨rfl,rfl⟩` subst direction — bound the eq, used `▸`).
- **Fiber-sum step (iv): the closing arithmetic (2026-07-11).** Pinned the previously-unverified
  finsum-of-a-constant step to `Set.exists_ne_of_one_lt_ncard` (big-part witness from `hbig`),
  `finsum_one : ∑ᶠ i ∈ s, 1 = s.ncard`, and `mul_finsum_mem` (no finiteness side-condition needed —
  ℕ has `NoZeroDivisors`) rather than a nonexistent `finsum_mem_const`. Full chain:
  `Set.Finite.ncard_biUnion` (biUnion + disjointness from step iii) → `finsum_mem_congr` to rewrite
  each fiber to the constant `2` (step i/ii lemma fed the big-part witness) → `← finsum_one` +
  `mul_finsum_mem` to fold to `2 * (squareCutPairs f a).ncard` → `ncard_squareCutPairs_eq_gCutEdges`.
  Landed as `IsSquareTightPartition.ncard_normalCrossEdgesRootedAt_eq_two_mul_gCutEdges`, closing
  `lem:normal-cross-count` and all of `sec:jacobs-counting`. No new friction (all mathlib lemmas
  found on first search).
- **Part-Finset / handshake infrastructure (2026-07-11).** Landed `SimpleGraph.partLabels`
  (`Set.Finite.toFinset` of `f '' Set.univ` — `V` has no `Fintype` instance, only `[Finite V]`,
  so `Finset.univ.image` isn't available directly) and
  `sum_gCutEdges_eq_two_mul_squareGCrossEdges`, proved by double-counting the oriented cross pairs
  `{(v,w) : G.Adj v w, f v ≠ f w}` via `Finset.card_eq_sum_card_fiberwise` twice — fibering by
  `f p.1` reuses `squareCutPairs`/`ncard_squareCutPairs_eq_gCutEdges` (already landed for
  `lem:normal-cross-count`); fibering by `s(p.1,p.2)` is the 2-to-1 map, mirroring mathlib's
  `SimpleGraph.dart_card_eq_twice_card_edges` proof shape. `partLabels` dropped its planned `G`
  receiver argument (`lake lint`'s `unusedVariables`: the label set depends only on `f`, not the
  graph) — called unqualified (`partLabels f`, no `G.` prefix) despite living in the `SimpleGraph`
  namespace. No blueprint node (per *Work items*, this is untracked assembly glue). No new
  friction beyond the already-logged unused-arg-drop pattern (this phase's tight-partition slice).
- **Vertex handshake + per-part edge bound (2026-07-11).** Landed `sum_ncard_eq_card`
  (`Nat.card V`, matching `molecule_rank_formula`'s `[Fintype V]` convention — `Nat.card` and
  `Fintype.card` agree there), proved by the exact same `Finset.card_eq_sum_card_fiberwise`
  fiberwise-count idiom as the edge handshake but 1-to-1 (`hVfin.toFinset` fibered by `f`
  directly, no second fibering step needed). For the per-part bound, added a small general
  restatement `IsLaman3.ncard_edgesIn_le` in `Jacobs.lean` (`IsLaman3`'s home file, per the
  "lemma lives with its definition" convention) converting the `Finset`-quantified definition to
  a `Set`-with-finiteness-hypothesis form via `Set.ncard_eq_toFinset_card` +
  `Set.Finite.coe_toFinset` — reusable beyond this one call site. Kept the big-part
  (`edgesIn_square_part_le`) and singleton (`edgesIn_square_singleton_part_eq_zero`) cases as two
  separate lemmas rather than one case-split fact, matching the hand-off's framing and the
  blueprint proof's own two-case treatment; the assembly commit selects between them per part.
  No new friction — both lemmas built clean on the first attempt, reusing idioms already
  established in this file's handshake proof.
- **`squareInPartEdges` classification decomposition (2026-07-11); scope correction.** Set out to
  do the full `thm:laman-square-count` assembly per the coordinator's three-step sketch; found
  instead that the classification's four edge classes don't all decompose over `partLabels f`
  yet (only `squareGCrossEdges` did, directly). Landed the missing decomposition for the in-part
  class only (`squareInPartEdges_eq_biUnion`, `_pairwiseDisjoint`,
  `sum_ncard_edgesIn_part_eq_ncard_squareInPartEdges`) and stopped there rather than pushing into
  the comparably-sized normal-cross and (newest-territory) special-cross decompositions in the
  same commit — see the *Hand-off*'s corrected 5-item breakdown. Technique: `Set.Finite.ncard_biUnion`
  (`(partLabels f).finite_toSet`) + `finsum_mem_coe_finset`, simpler than the cross-class
  handshakes' ordered-pairs double-count since an in-part edge belongs to exactly one part (no
  factor-of-two bookkeeping). Two build-error round-trips via the `lean-lsp` MCP (faster than a
  full `lake build` per iteration): forgot `[Finite V]` on the two new `partLabels`-taking lemmas
  (instance-resolution error, not a real API gap); `Set.PairwiseDisjoint`'s goal is wrapped in
  `Function.onFun`, so `rw [Set.disjoint_left]` doesn't find the pattern until `Function.onFun` is
  unfolded first (`simp only [Function.onFun, Set.disjoint_left]`) — already the exact idiom
  `squareCutPairs_pairwiseDisjoint` uses earlier in this file, so not logged as new FRICTION (a
  precedent already in-file, just not consulted before writing the first draft).
