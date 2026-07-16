# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** in progress (opened 2026-07-16, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1
open recon question, and the **R1-5** spike sharpenings. Queue position
(G1 next after the Phase-32 new-math round, recon-first) was
user-adjudicated 2026-07-10 (`notes/Prospect.md` *Hand-off*).

## Current state

Opened recon-first; **next concrete step: dispatch the two chokepoint
spikes** (work items A and B below — independent of each other, either
order). No ℝ→K sweep work is sanctioned until both spikes return
compiler-witnessed verdicts and the sweep is adjudicated on them. No
Lean or blueprint file has changed yet.

## What this phase is

Generalize the core KT Theorem 5.5/5.6 chain (Phases 17–23 surface)
from `ℝ` to a general field `K` (the exact field hypothesis — infinite
certainly; orderedness is what the spikes remove — is a spike
deliverable). Survey verdict (Prospect G1): **no essentially-real
step** — zero topology/analysis under `Molecular/` (KT's "Lemma 5.2
semicontinuity" is formalized as algebraic span-monotonicity,
`RigidityMatrix/Basic.lean`); exactly two ℝ chokepoints, both
proof-local with field-general statements (work items A and B). The
rest is a mechanical ℝ→K signature sweep over ~30 files. Precedent:
Whiteley 1988 proves the matroid-union layers over any infinite field;
a field-general KT Thm 5.5/5.6 appears to be **new**. Scope
**excludes** the molecule application layer (Phases 24–26): genuinely
ℝ³-bound physics (Prospect K4).

## Architectural choices made up front

- **Recon-first, spike-before-sweep.** The two chokepoint spikes run
  (compiler-witnessed, Phase-30-recon style) before the ~30-file sweep
  is sanctioned — adjudicated order, `notes/Prospect.md` *Hand-off*.
- **Structural-edit mode, no new blueprint chapter.** The ℝ→K reshape
  restates existing (all-green) molecular-chapter nodes in step with
  the Lean, per the structural-edit discipline (CLAUDE.md *Working*,
  incl. the per-slice statement-restate grep gate — every sweep slice
  changes statements). The to-do list is this note's work items, not a
  chapter. Inherited obligation: should a slice leave any node red,
  `intro.tex`'s "every node is green" phrasing goes stale in the same
  commit (the Phase-32 chapter-open precedent).
- **Codes-until-open seam (recorded, not pre-divided).** Should the
  phase run long, the likely seam is chokepoint-spikes vs. the
  mechanical ℝ→K sweep (`notes/Prospect.md` *Hand-off*); sub-letter at
  the seam only when a split actually arrives.

## Work items

- [ ] **Spike A — `Molecular/MeetHodge.lean` metric-free.** Reprove the
  file's Gram–Schmidt-backed chokepoint without the inner-product
  structure. R1-5 sharpenings (`notes/Prospect.md`): (i)
  `finrank_toDualPerp_pair_eq` is cheaply metric-free (kernel
  intersection of two independent functionals has codimension 2) — the
  easy third; (ii) the real chokepoint is
  `complementIso_extensor_mem_range_map_subtype`, whose metric-free
  route is GL-equivariance-up-to-determinant replacing the current
  O(n)-equivariance (the target is a membership/proportionality, hence
  scalar-blind), retiring the Gram–Schmidt helper
  `exists_orthonormalBasis_span_pair_eq`; (iii) named risk: over a
  non-ordered field the normal pair's span can meet its own
  `toDual`-perp (isotropic normals) — a hand-checked `ℂ`, `k = 1`
  example suggests the *statement* survives while any frame-extension
  proof route does not; (iv) independent payoff even over ℝ:
  metric-free folds `MeetHodge.lean` into `Meet.lean` (the file split
  exists only for the PiL2-import `whnf` regression, TACTICS-QUIRKS
  § 59).
- [ ] **Spike B — genericity engine onto the maximal-minor twin.**
  Reroute the three `Mathlib/LinearAlgebra/Matrix/Rank.lean`
  genericity-engine lemmas
  (`finite_setOf_not_linearIndependent_rows_along_affine_path`,
  `finite_setOf_not_linearIndependent_rows_of_polynomial`,
  `exists_linearIndependent_rows_specialize`) off the ordered-field
  Gram-determinant characterization
  (`linearIndependent_rows_iff_det_mul_transpose_ne_zero`, the file's
  only `[LinearOrder R] [IsStrictOrderedRing R]` site) onto its
  field-general maximal-minor twin in the same file
  (`exists_submatrix_det_ne_zero_of_linearIndependent_rows`, which
  already powers the parallel
  `linearIndependent_rows_of_specialized_submatrix_det_ne_zero` route
  live in `BodyBar/KFrame.lean`).
- [ ] **Adjudicate the sweep on the spike verdicts** — pin the field
  hypothesis (infinite `K`; any characteristic or isotropy caveats the
  spikes surface) and the sweep slice plan (~30 files under
  `Molecular/` + the touched mirrors), then execute mechanically,
  green at every slice.
- [ ] *Optional rider (Prospect S1):* the one-line retention
  docstrings on the d=3 exposition decls — docs-only but rebuilds the
  molecular tree; bundle into this phase's first molecular-tree
  commit rather than a standalone rebuild.

## Blockers / open questions

- R1-5(iii): isotropic normals over non-ordered fields (Spike A's
  named risk) — does the `complementIso` statement survive with a
  proof that avoids frame extension entirely, or does the field
  hypothesis need a non-isotropy side condition?
- Whether both spikes GO. A NO-GO on either bounds the phase down to
  whatever partial generality survives (adjudicate before any sweep).

## Hand-off / next phase

**Next concrete step: dispatch Spike A** (the `MeetHodge.lean`
metric-free spike — the smaller, sharper-scoped of the two; Spike B
can run before or alongside it, they are independent). Both spikes are
read-mostly compiler-witnessed recons in the Phase-30 mold: verdict +
witness Lean, no tree-wide edits. Only after both verdicts land does
the sweep get adjudicated and sliced.

## Decisions made during this phase

(none yet)
