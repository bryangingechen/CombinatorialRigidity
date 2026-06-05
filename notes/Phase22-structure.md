# Phase 22 structure pass (pre-Phase-22b) — file splits (work log)

**Status:** in progress (opened 2026-06-05, before opening Phase 22b).

A dedicated **structure pass** — not a feature phase — run before Phase 22b, mirroring the
project's perf-pass precedent (`notes/Phase8-perf.md`, `notes/Phase9-perf.md`; the
post-Phase-9-perf `PebbleGame/` subdirectory split). Scope: split the two over-cap Molecular
giants into subdirectories and split the large `algebraic-induction.tex` blueprint chapter, so
the Phase-22b work (KT Claim 6.4) lands in a navigable file and every 22b rebuild re-elaborates
only the active leaf. See `notes/PERFORMANCE.md` *Factors to weigh when ranking splits* / *Split
candidates* and the pre-pass review that motivated this.

## Targets

| File | Was | Action |
|---|---|---|
| `Molecular/AlgebraicInduction.lean` | 5918 LoC (3.9× the ~1500 cap), the active 22b file | → `AlgebraicInduction/` (5 files) |
| `Molecular/Induction.lean` | 4256 LoC (2.8× cap), stable (Phase 20) | → `Induction/` (5 files) |
| `blueprint/.../algebraic-induction.tex` | 1918 lines, 9 subsections | → thin parent + `\input` sub-files |

## Verified mechanics (the split is a pure, semantics-preserving move)

- **No blueprint pin rewrites.** `\lean{…}` pins are by fully-qualified declaration name, not
  file path, so a *move* keeps every name; `checkdecls` is unaffected.
- **Tiny import surface.** The only consumer of either giant is the root aggregator
  `CombinatorialRigidity.lean`; no math file imports them. Per the project's no-hub convention
  (PERFORMANCE.md *Mathlib subdirectory pattern*; the deleted `PebbleGame.lean`), the original
  is deleted and the aggregator imports the **terminal leaf** of the new linear import chain.
- **Keep non-module.** Both giants are non-module files (unlike `Extensor`/`Meet`/`RigidityMatrix`);
  the split files match (plain `import`, no `module`/`public section`). Module-system conversion is
  out of scope for this pass.
- **Bottom-up extraction + linear import chain** is safe because the original declaration order is
  already a valid topological sort; each new file reconstructs the `namespace`/`variable`/`open`
  preamble of the section it came from (the `SparsityIComponents` `variable`-redeclaration gotcha).

## Progress

### A — `AlgebraicInduction.lean` split ✓ (this commit)

5 files, linear chain `PanelLayer ← Pinning ← PanelHinge ← GenericityDevice ← CaseI`; original
deleted; aggregator → `…AlgebraicInduction.CaseI`. Build green + warning-clean + lint green.

| File | LoC | Contents (blueprint nodes) |
|---|---|---|
| `PanelLayer.lean` | 563 | panel support extensor (`def:panel-support-extensor`) + B0 annihilator family (`lem:rows-polynomial-in-normals`) |
| `Pinning.lean` | 1329 | `BodyHingeFramework` infra: `panelRow`/spans, `RankHypothesis`+base, cycle base (5.4), `withGraph`, `pinnedMotionsOn` |
| `PanelHinge.lean` | 1128 | `PanelHingeFramework`, `withNormal`/Case-II infra, `IsHingeCoplanar`, Theorem 5.5 + motives, Prop 1.1 analytic half |
| `GenericityDevice.lean` | 1568 | `lem:genericity-device`: `exists_good_realization` engine, splice + rank-polynomial producers |
| `CaseI.lean` | 1428 | couple/block-triangular producers, `extProj`, `case_I_realization` (green-modulo `lem:claim-6-4`) ← **22b lands here** |

### B — `algebraic-induction.tex` split ✓ (this commit)

Thin parent `algebraic-induction.tex` (99 lines: `\section` + preamble + 5 `\input`s) keeps the
single logical chapter (dep-graph grouping + all internal `\cref`s intact; `main.tex` unchanged).
Sub-files under `chapter/algebraic-induction/`: `panel-layer.tex` (335), `case-i.tex` (595),
`case-ii.tex` (230), `genericity-and-count.tex` (644), `case-iii.tex` (20). `blueprint/verify.sh`
green (`inv bp` + `inv web` + `checkdecls` all pass — pins resolve, no dangling `\uses`/`\cref`).
Also fixed `intro.tex`'s two Phase-21/21b file-path references to the new subdir.

### C — `Induction.lean` split ☐ (next)

### D — pass close (PERFORMANCE.md executed-split record, ROADMAP status flip) ☐

## Hand-off / next

After D closes: open Phase 22b per `notes/Phase22b.md`, now landing in
`Molecular/AlgebraicInduction/CaseI.lean`. One small tooling note for this pass: when scanning for
`linter.style.longLine` (>100-char) violations, count **characters not bytes** — `awk length()` is
byte-based and false-positives on lines with multibyte glyphs (`ℝ`, `§`, `–`, `…`); trust the build's
linter output, which counts characters.
