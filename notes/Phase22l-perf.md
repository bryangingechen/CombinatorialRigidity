# Perf pass (post-Phase-22l) — molecular file splits (work log)

**Status:** in progress (reopened — sectioning + splitting the `RigidityMatrix` core, slices 6+).

The post-Phase-22 molecular split round: tackling the over-cap molecular
giants logged in `notes/PERFORMANCE.md` *Post-Phase-22 split candidates* /
*(C) Other molecular split candidates*. Pure semantics-preserving moves (no
decl renamed → blueprint `\lean{…}` pins + `checkdecls` unaffected), driven by
factors 2/4 (file size vs. the ~1500-LoC soft cap; navigability) — factor 1
(downstream-import surface) is near-nil on the linear molecular import spine,
and factor 3 (incremental-rebuild) is live only for the active realization-layer
files (`AlgebraicInduction/Case*`), not the stable ones.

## Current state

**Next step:** slice 7 (decision pending) — the `RigidityMatrix` core *file split*
along the now-explicit seam (core rank-theory vs. Claim-6.12 / candidate-row machinery,
matching the blueprint `rigidity-matrix.tex` / `case-iii.tex` chapter boundary), OR stop at
the sectioning. The seam is clean dependency-wise (zero core→downstream back-edges) but
**non-contiguous** — two separated ranges + a namespace re-open (see *Decisions → Slice 6*).
Slices 1–6 landed; build + lint + checkdecls green, warning-clean. (The three original
`PERFORMANCE.md` split candidates were all done in slices 1–5; what else remains there is
*non-split*: the profile-then-localize `maxHeartbeats` budgets and the low-priority
style-only files `Deficiency`/`PanelLayer`/`GenericityDevice`/`Pinning`.)

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
- **Slice 5 (`2c30c02`):** `ForestSurgery.lean` (3783 LoC) → 2-way cut into
  `ForestSurgery/EdgeSplitting.lean` (1736, KT 4.2) + `ForestSurgery/Reduction.lean`
  (2077, KT 4.1/4.9). Both stay over cap — accepted (stable, low-leverage).
- **Slice 6 (RigidityMatrix core sectioning):** added 10 `/-! ##` section headers to the
  2937-LoC core (comment-only), exposing the clean-but-non-contiguous core-vs-Claim-6.12
  file-split seam.

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
- [x] **Slice 6 — `RigidityMatrix.lean` core sectioning.** Slice 1 only carved the
  brick tail; the ~2937-LoC core stayed un-sectioned. Added 10 `/-! ##` headers (the
  read-pass, comment-only) across the `Molecular` head + the `BodyHingeFramework` body,
  exposing the core-vs-Claim-6.12 seam. See *Decisions → Slice 6*.
- [ ] **Slice 7 (decision pending) — `RigidityMatrix.lean` core file split.** Cut the
  core rank-theory from the Claim-6.12 / candidate-row machinery (≈1500 + ≈1400 LoC,
  matching the blueprint chapter split). Clean dependency-wise but **non-contiguous**
  (two ranges + a namespace re-open) — more surgery than a tail-cut.

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

### Slice 6 — RigidityMatrix core sectioning + the split-seam analysis

- **10 `/-! ##` sections** (subagent read-pass) across the two un-sectioned regions —
  the `Molecular` head (ScrewSpace carrier; Claim-6.12 panel geometry; `ExtensorInPanel`
  + the `BodyHingeFramework` structure) and the body (hinge constraint; rigidity rows;
  infinitesimal motions; candidate-completion `columnOp`/pinned-block; Claim 6.12
  disjunction; multi-edge forest independence; trivial motions + rank Lemmas 5.1–5.3).
  Comment-only; warning-clean after a 3-line longLine reflow.
- **The split seam (for slice 7): clean but non-contiguous.** Dependency flow is strictly
  core → Claim-6.12 (zero back-edges — no core decl, incl. the rank lemmas, references the
  candidate-row / geometry / `case_III_claim612` layer). So a `RigidityMatrix` (core) +
  `RigidityMatrixClaim612` (downstream) cut is realizable and matches the blueprint
  `rigidity-matrix.tex` / `case-iii.tex` chapter boundary. **Caveat:** the downstream half
  is *two separated ranges* — the geometry (top-level `Molecular`) + the candidate-row /
  Claim-6.12 block (extracted from the *middle* of `BodyHingeFramework`) — so the new file
  reopens two namespace blocks. More surgery than a tail-cut; unlike ForestSurgery it's a
  genuine seam, not a "sectioning-only" case.

## Hand-off / next step

**Slice 7 decision pending** (the only open item): split the `RigidityMatrix` core along
the slice-6 seam (≈1500 core + ≈1400 Claim-6.12, matching the blueprint chapters), or stop
at the sectioning. Clean dependency-wise but non-contiguous (two ranges + namespace re-open);
`RigidityMatrix` is a stable file (factor-3 low), so it's a navigability/size call, not a
build-perf one. Beyond that, what remains in `PERFORMANCE.md` is *non-split* work for a
future round (the profile-then-localize `maxHeartbeats` budgets; the low-priority style-only
files `Deficiency`/`PanelLayer`/`GenericityDevice`/`Pinning`).
