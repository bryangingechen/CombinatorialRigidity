# Perf pass (post-Phase-22l) — molecular file splits (work log)

**Status:** in progress.

The post-Phase-22 molecular split round: tackling the over-cap molecular
giants logged in `notes/PERFORMANCE.md` *Post-Phase-22 split candidates* /
*(C) Other molecular split candidates*. Pure semantics-preserving moves (no
decl renamed → blueprint `\lean{…}` pins + `checkdecls` unaffected), driven by
factors 2/4 (file size vs. the ~1500-LoC soft cap; navigability) — factor 1
(downstream-import surface) is near-nil on the linear molecular import spine,
and factor 3 (incremental-rebuild) is live only for the active realization-layer
files (`AlgebraicInduction/Case*`), not the stable ones.

## Current state

**Next step:** decide whether to continue with the next candidate
(`ForestSurgery.lean` or `CaseIII.lean`) or pause. Slice 1 (RigidityMatrix
bricks) is landed, build + lint green, warning-clean.

Slice 1 landed: `Molecular/RigidityMatrix.lean` (3527 LoC) → carved the three
rank-addition brick sections (`CutEdgeBrick`/`SpliceBrick`/`PinnedPlacementBrick`,
the old L2935–3523) into a new leaf `Molecular/RigidityMatrix/Bricks.lean`
(634 LoC). Core drops to 2937 LoC. Rename-free.

## Slice plan / candidate ranking

- [x] **Slice 1 — `RigidityMatrix.lean` brick-carve.** Most straightforward
  (cleanest seams). The three bricks sat in clearly-marked `section`s at the
  file tail inside `namespace BodyHingeFramework`, with a clean forward
  dependency (bricks → core API; core does not use the bricks). Carved to
  `RigidityMatrix/Bricks.lean` (`module`, `public import`s the core).
- [ ] **Slice 2 (candidate) — `Induction/ForestSurgery.lean` (3783 LoC).**
  2.5× cap; ~20 `/-! ##` doc sections keyed to KT lemmas; natural 2-way cut
  (KT 4.2 forest core | KT 4.1/4.9/reduction material). *Stable* Induction
  subtree → factor-3 low. Confirm the two arcs don't share private helpers
  before cutting.
- [ ] **Slice 3 (candidate) — `AlgebraicInduction/CaseIII.lean` (4000 LoC).**
  Highest effort: flat namespace, no section markers, 44 top-level decls.
  Needs a read-pass to group the decls (or at minimum add `/-! ##` headers)
  before any file cut. Active realization subtree → factor-3 high.

(`RigidityMatrix.lean` core itself stays ~2937 LoC after slice 1 — a partial
win; the un-sectioned `BodyHingeFramework` core would need sub-sectioning for a
deeper split. Not pursued; navigability/size of the carved bricks is the win.)

## Decisions made during this phase

### Slice 1 — RigidityMatrix brick-carve

- **Factor-1 is nil (corrects `PERFORMANCE.md` (C)#2's "could carry factor-1
  benefit").** The earliest brick consumer is `Pinning.lean` (2nd in the
  `RigidityMatrix ← PanelLayer ← Pinning ← …` chain, via
  `le_finrank_span_rigidityRows_of_pinned_placement`), so carving the bricks
  into a leaf saves import surface only for `PanelLayer` (1st in the chain, and
  stable Phase-18 infra). The split is justified on factors 2/4, not 1.
- **Minimal import wiring.** Only `Pinning.lean` gains
  `import …RigidityMatrix.Bricks`; the rest of the chain (PanelHinge …
  Theorem55) inherits it transitively, and `PanelLayer` keeps importing only
  the core (the small factor-1 win). Added to the `CombinatorialRigidity.lean`
  aggregator too, matching its explicit-molecular-listing convention.
- **`Bricks.lean` is `module` + `public section`.** All brick `def`s are
  `private` (proof-internal); the public decls are theorems, whose names+types
  are exposed under plain `public section`. No `@[expose]` needed, no
  `backward.privateInPublic` opt-in. (Parent file is `@[expose] public section`,
  but that is a no-op for an all-private-defs + public-theorems file.)
- **"Brick" is not KT's term — terminology pass flagged.** Verified against KT
  2011: "brick" occurs once, in a bibliography entry (Jackson–Jordán *Brick
  partitions of graphs* 2008, unrelated). It's established project shorthand
  (the `*Brick` section names, blueprint lemma titles). User chose to keep
  `Bricks.lean` and open a separate terminology-faithfulness sweep. Flagged:
  `notes/FRICTION.md` *[process] "Brick" is a project mnemonic…*.

## Hand-off / next step

Slice 1 is a clean handoff point. Next concrete commit: either slice 2
(`ForestSurgery.lean` 2-way cut — confirm no shared private helpers first) or
slice 3 (`CaseIII.lean` — add `/-! ##` section headers as a cheap first step
before any file cut). Both are independent of slice 1.
