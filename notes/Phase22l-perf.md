# Perf pass (post-Phase-22l) — molecular file splits (work log)

**Status:** complete (all three split candidates done).

The post-Phase-22 molecular split round: tackling the over-cap molecular
giants logged in `notes/PERFORMANCE.md` *Post-Phase-22 split candidates* /
*(C) Other molecular split candidates*. Pure semantics-preserving moves (no
decl renamed → blueprint `\lean{…}` pins + `checkdecls` unaffected), driven by
factors 2/4 (file size vs. the ~1500-LoC soft cap; navigability) — factor 1
(downstream-import surface) is near-nil on the linear molecular import spine,
and factor 3 (incremental-rebuild) is live only for the active realization-layer
files (`AlgebraicInduction/Case*`), not the stable ones.

## Current state

**Round complete** — all three `PERFORMANCE.md` split candidates done; every commit
build + lint + checkdecls green, warning-clean. No over-cap molecular *split*
candidates remain (what's left in `PERFORMANCE.md` is non-split: the
profile-then-localize `maxHeartbeats` budgets, and the low-priority style-only files
`Deficiency`/`PanelLayer`/`GenericityDevice`/`Pinning` — out of this round's scope).

- **Slice 1 (`fd0ccd2`):** `RigidityMatrix.lean` 3527 → 2937 LoC; the three
  rank-addition bricks → new leaf `Molecular/RigidityMatrix/Bricks.lean` (634).
- **Slice 2 (`8d2c8fc`):** `CaseIII.lean` gained 7 `/-! ##` section headers
  (comment-only) — making the grouping + a clean 2-way seam explicit.
- **Slice 3 (`39a6a8e`):** `CaseIII.lean` (4040 LoC) 2-way cut at that seam into
  flat `CaseIIICandidate.lean` (§1–§4) + `CaseIII.lean` (§5–§7).
- **Slice 4 (`6088c94`):** reorganized the Case-III block into a `CaseIII/`
  subdirectory of 4 files — `Candidate` (1564) / `Arms` (859) / `Relabel` (1016) /
  `Realization` (692). Chain `CaseII ← .Candidate ← .Arms ← .Relabel ← .Realization
  ← Theorem55`.
- **Slice 5 (`Induction/ForestSurgery/` subdirectory):** `ForestSurgery.lean`
  (3783 LoC) → 2-way cut into `ForestSurgery/EdgeSplitting.lean` (1736, KT 4.2) +
  `ForestSurgery/Reduction.lean` (2077, KT 4.1/4.9). Both stay over cap (no single
  dominant sub-block) — accepted for a stable, low-leverage file.

## Slice plan / candidate ranking

- [x] **Slice 1 — `RigidityMatrix.lean` brick-carve.** Carved the three
  rank-addition brick `section`s (clean forward dependency: bricks → core API)
  to `RigidityMatrix/Bricks.lean` (`module`, `public import`s the core).
- [x] **Slice 2 — `AlgebraicInduction/CaseIII.lean` (4000 LoC) section headers.**
  The flat 44-decl namespace got 7 `/-! ##` headers grouping the decls by KT §6.4
  sub-argument (the read-pass item 8 calls for; comment-only, warning-clean after
  a 2-line longLine reflow). Active realization subtree → factor-3 high.
- [x] **Slice 3 — `CaseIII.lean` 2-way cut at the seam** (`39a6a8e`): flat
  `CaseIIICandidate.lean` (§1–§4) + `CaseIII.lean` (§5–§7).
- [x] **Slice 4 — `CaseIII/` subdirectory (4 files).** Reorganized the flat cut +
  sub-split the realization: `Candidate`/`Arms`/`Relabel`/`Realization` under
  `AlgebraicInduction/CaseIII/`. See *Decisions → Slices 3–4*.
- [x] **Slice 5 — `Induction/ForestSurgery.lean` (3783 LoC) → `ForestSurgery/`
  subdirectory.** 2-way cut at L1742 (the only `private` helper `vfiber_inc_iff` is
  downstream of the seam → clean): `EdgeSplitting.lean` (KT 4.2) +
  `Reduction.lean` (KT 4.1/4.9). Both over cap — accepted (stable, low-leverage).

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

### Slice 2 — CaseIII section headers + the file-split seam

- **7-section grouping** (mapped via a subagent read-pass against `case-iii.tex`'s
  milestone skeleton; only ~11 of the 44 decls are blueprint-pinned, the rest are
  helpers): (1) Claim 6.11 redundant `ab`-row (L64–); (2) candidate-completion +
  old/new block split (L578–); (3) the `caseIIICandidate` shear-family device
  (L854–); (4) per-line/restriction families + `t=0` rank certification (L1018–);
  (5) arms M₁/M₂ + triangle base + producer spine (L1577–); (6) relabel/split-off
  transport, the M₃ machinery (L2369–); (7) the dispatch + final
  `case_III_realization` (L3357–). (Pre-header line numbers.)
- **Clean 2-way file-split seam (for slice 3):** after `case_III_rank_certification`,
  before `case_III_arm_realization`. §1–§4 (L64–~1576) is pure single-framework
  infrastructure that nothing downstream reaches into; §5–§7 (arms + relabel +
  dispatch + capstone) consumes it. **Carry-across caveat:**
  `exists_candidateRow_bottomRows_of_rigidOn` (§1, the W6b `ρ`/`w` feed) is consumed
  by the §7 dispatch — it travels with the upstream file fine, but must not be
  orphaned. A 3-way is *not* clean: M₃ (§6) reuses the M₁ engine
  `case_III_arm_realization` (§5), so §5/§6 can't separate.

### Slices 3–4 — CaseIII split into the `CaseIII/` subdirectory

- **End state: a 4-file `AlgebraicInduction/CaseIII/` subdirectory** (the flat
  `CaseIIICandidate.lean` + `CaseIII.lean` of slice 3 were a stepping stone; slice 4
  reorganized them + sub-split the realization). The decl namespace stays flat
  `CombinatorialRigidity.Molecular` (the directory is file organization, not
  namespacing — mathlib-normal):
  - `Candidate.lean` (1564) — §1–§4: Claim 6.11 + candidate-completion +
    `caseIIICandidate` device + `t=0` certification.
  - `Arms.lean` (859) — §5: M₁/M₂ arm closers + triangle base + producer spine.
  - `Relabel.lean` (1016) — §6: the `ρ=(av)` relabel transport + M₃ arm closer.
  - `Realization.lean` (692) — §7: the M₁/M₂/M₃ dispatch + `case_III_realization`
    capstone (the chain terminal `Theorem55` imports).
- **Cut chain (forward, clean):** `CaseII ← CaseIII.Candidate ← .Arms ← .Relabel ←
  .Realization ← Theorem55`. Seam between §4 and §5 was the slice-2 finding; the
  §5/§6/§7 sub-seams are the §5→§6→§7 forward chain (M₃ reuses the M₁ engine, so
  Relabel imports Arms; the dispatch consumes all arms, so Realization imports
  Relabel). Rename-free, non-`module`; safety-checked (no `private` decl / backward
  dependency crosses any seam). Only `CaseIII/` is promoted to a subdirectory —
  `CaseI`/`CaseII` stay flat single files (mathlib convention: only the oversized
  case gets a directory).
- **Why a subdirectory** (user call): groups the largest case's 4 files instead of
  accumulating `CaseIII*`-prefixed flat siblings; matches `PERFORMANCE.md` *Mathlib
  subdirectory pattern*. No `Defs.lean`/`Basic.lean` — Case III divides by KT
  sub-argument, not defs-vs-API, so the files carry descriptive KT-aligned names.

### Slice 5 — ForestSurgery 2-way cut into a `ForestSurgery/` subdirectory

- **The cut.** `Induction/ForestSurgery.lean` (3783 LoC) → `Induction/ForestSurgery/`:
  `EdgeSplitting.lean` (1736, KT Lemma 4.2 — acyclicity transport + reroute +
  edge-splitting extension) + `Reduction.lean` (2077, KT 4.1/4.9 — reduction-step +
  Theorem 4.9 + repacking + forest-surgery count/assembly + 4.3(ii)/4.4/4.7).
- **Clean seam (verified):** the only `private` helper `vfiber_inc_iff` (L2486) is
  used only at L2532 — both downstream of the L1742 seam, so it doesn't cross; the
  file is in dependency order so the upstream half is self-contained. Consumers
  (`PanelLayer`, the aggregator) switched `import …ForestSurgery` → `…ForestSurgery.Reduction`.
- **Partial win, accepted.** Both halves stay over the ~1500 cap (~1736 / ~2077) — no
  single dominant sub-block to carve, and a deeper split isn't worth it for the
  *stable, lowest-leverage* file (factor-3 ≈ 0). Subdirectory chosen over flat
  siblings for parity with `CaseIII/` (user call).

## Hand-off / next step

**Round complete.** The three over-cap molecular split candidates are done
(`RigidityMatrix` bricks; `CaseIII/` 4-file subdir; `ForestSurgery/` 2-file subdir).
What remains in `PERFORMANCE.md` is *non-split* work, for a future round if wanted:
the profile-then-localize `maxHeartbeats` budgets in the CaseI/Theorem55 producers,
and the low-priority style-only files (`Deficiency`/`PanelLayer`/`GenericityDevice`/
`Pinning`, each modestly over cap). The `RigidityMatrix.lean` core (2937 LoC) could
also take a deeper split once its un-sectioned `BodyHingeFramework` body is
sub-sectioned (see *Decisions → Slice 1*).
