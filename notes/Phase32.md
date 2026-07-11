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
**The B-track's first two slices are landed**: `lem:exists-tight-partition`
(green as `Graph.IsTightPartition` / `Graph.exists_isTightPartition`),
`lem:partitionDef-merge` (green as `Graph.crossingEdgesWithin` /
`Graph.partitionDef_merge`), and `lem:tight-partition-subfamily` (green
as `Graph.IsTightPartition.subfamily_le`), all in `Molecular/Deficiency.lean`,
`## Tight partitions` section ahead of `rank_matroidMG_le`. The first two
are proved more general than the blueprint's literal hypotheses (no
`V(G).Nonempty` for the first, no `2 ≤ S.ncard` for the second — the
`Finite.exists_max` / merge-arithmetic route doesn't need them; each
docstring notes the generalization; see `lake lint`'s
`unusedArguments` linter for why dropping is the right call over
carrying a dead hypothesis). `subfamily_le`'s proof is exactly the route
the phase note predicted: collapse `S` via `fun x => if x ∈ S then a else x`,
apply `partitionDef_merge`, then `partitionDef_le_deficiency` + tightness
+ `linarith`. Everything else in the chapter is still red. **Next
concrete step** — see *Hand-off*.

## Work items

The chapter's red nodes are the to-do list. Lean-side glue the chapter
deliberately does not track (blueprint selectivity), to land inside the
slices that need it:

- shadow-carrier crossing-count bridge: `(G.shadowGraph.crossingEdges
  f).ncard` = number of `G`-edges crossing `f` (padding labels never
  linked);
- part-Finsets from a labeling `f : V → V` (fibers restricted to the
  label image) + the partition handshake `∑ parts d_G(P_i) = 2·d_G(P)`;
- file placement for the remaining tracks: B-track tight-partition
  arithmetic D-generically in `Molecular/Deficiency.lean`; the
  D-track's row-independence lemmas alongside their planar analogue in
  `RigidityMatroid.lean`. Builder's discretion on the final split.

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

**Next concrete commit:** the B-track's existence, merge, and subfamily
lemmas (`lem:exists-tight-partition`, `lem:partitionDef-merge`,
`lem:tight-partition-subfamily`) are landed (see *Current state*); the
remaining two lemmas of `sec:jacobs-tight-partitions` are the next step:

- `lem:tight-partition-parts` — JJ Lemma 3.2(b), consumed form: every
  part of a tight partition is a singleton or has ≥3 vertices with
  in-part degree ≥2 everywhere. **Route worked out this session** (not
  yet built): for `v` in a part `A` with `|A| ≥ 2` (witnessed by some
  `w ≠ v`, `f w = f v = a`), `f` is non-injective at `{v, w}`, so
  `f '' V(G) = f '' (V(G) \ {w})` has `ncard ≤ V(G).ncard - 1 <
  Nat.card α` — a genuinely fresh label `b ∉ f '' V(G)` exists (the
  key sub-lemma; ~10–15 lines via `Set.ncard_image_le` + a cardinality
  contradiction). Let `f' = Function.update f v b` (splits `{v}` off
  `A`); apply `partitionDef_merge` with base `f'`, `S = {b, a}`, `c`
  collapsing both to `a` (so `c ∘ f' = f`); `partitionDef_le_deficiency`
  at `f'` + tightness of `f` gives `D ≤ (D-1)·d` where `d` is the count
  of `G`-edges from `v` to `A \ {v}` (only `v` carries label `b`), so
  `d ≥ 2`; `d ≤ 1` when `|A| = 2` (simple graph, ≤ 1 edge on 2
  vertices) rules out the two-vertex part. **Open design call:** no
  existing `Graph α β` primitive states "in-part degree" (`cutEdges` /
  `crossingEdgesWithin` are whole-graph / whole-label-family, not
  one-vertex-vs-one-part) — the natural choice is an inline set
  `{e | ∃ y, y ≠ v ∧ y ∈ A ∧ G.IsLink e v y}`, matching the `e_G(Q)`
  quantity the merge identity already produces.
- `lem:tight-partition-cross-pair` — the `D ≥ 3` edge-multiplicity half
  is one instance of `lem:tight-partition-subfamily` at `|Q| = 2`; the
  `D ≥ 5` common-neighbor-uniqueness half needs the blueprint's 4-part
  case analysis (harder — do after `parts` lands, since the
  classification lemmas immediately downstream need both).

`sec:jacobs-counting`, `sec:jacobs-zero-extension`,
`sec:jacobs-theorem`, and `sec:jacobs-degree-one` all wait on the rest
of the B-track (the D-track dependency is now discharged).

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
- **New attributions verified:** Jacobs 1998 (J. Phys. A **31**,
  6653–6668) and Franzblau 2000 (Discrete Appl. Math. **101**, 131–155)
  added to the bibliography; JJ Lemma 3.2 credited to the
  Jackson–Jordán companion paper via the 2008 statement (no separate
  bib entry — its published details not independently verified).
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
