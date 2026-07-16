# Phase 33 — PROSPECT G1: field generality of the core Thm 5.5/5.6 chain (work log)

**Status:** in progress (opened 2026-07-16, recon-first).

Planning input: `notes/Prospect.md` — the Tier-2 **G1** entry, the G1
open recon question, and the **R1-5** spike sharpenings. Queue position
(G1 next after the Phase-32 new-math round, recon-first) was
user-adjudicated 2026-07-10 (`notes/Prospect.md` *Hand-off*).

## Current state

Spike A returned **GO, all three decls**, compiler-witnessed sorry-free
(2026-07-16; verdict record + new-decl inventory under *Decisions
made* — the spike was read-only, no tree file changed). **Next concrete
step: dispatch Spike B** (work item below). No ℝ→K sweep work is
sanctioned until Spike B also returns a compiler-witnessed verdict and
the sweep is adjudicated on both. No Lean or blueprint file has changed
yet.

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

- [x] **Spike A — `Molecular/MeetHodge.lean` metric-free.** GO, all
  three decls, compiler-witnessed sorry-free (2026-07-16); full verdict
  record + the build slice's new-decl inventory under *Decisions made*.
  Highlights vs. the R1-5 sharpenings (`notes/Prospect.md`):
  contragredient equivariance (an *exact* equation) refines the
  GL-up-to-determinant route (ii); the isotropy risk (iii) is refuted —
  no side condition; the fold-back payoff (iv) is confirmed GO.
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

- **Sweep-adjudication decision opened by Spike A's GO:** land the
  metric-free `MeetHodge.lean` reproofs *pre-sweep over ℝ* (immediate
  payoff: fold MeetHodge into `Meet.lean`, retire the PiL2 mirror) vs.
  bundle them into the sweep's `Meet.lean` slice. Decide at sweep
  adjudication, on both spike verdicts.
- Whether Spike B GOes. A NO-GO bounds the phase down to whatever
  partial generality survives (adjudicate before any sweep).

## Hand-off / next phase

**Next concrete step: dispatch Spike B** (the genericity-engine
maximal-minor spike, work item above). Same mold as Spike A: read-only
compiler-witnessed recon in the Phase-30 style — verdict + witness
Lean, no tree edits. Only after both verdicts land does the sweep get
adjudicated and sliced (including the pre-sweep-vs-bundle decision
under *Blockers*).

## Decisions made during this phase

- **Spike A verdict (2026-07-16): GO, all three `MeetHodge.lean`
  decls, metric-free** — compiler-witnessed sorry-free (the session's
  spike scratch file, ~425 lines, compiled clean against the current
  tree importing only `Molecular/Meet.lean`; that file is
  session-ephemeral — this record is the durable route registry).
  Route refinement over the R1-5(ii) pin: O(n)-equivariance is
  replaced by **contragredient equivariance**, an *exact equation*
  (not an up-to-determinant proportionality): for surjective `g` and
  `h` with `⟨h x, g y⟩ = ⟨x, y⟩` (the standard `Pi.basisFun.toDual`
  pairing), `complementIso hj (map j g X) = det g • map (k+2−j) h
  (complementIso hj X)`.
  - **R1-5(iii) isotropy risk refuted — no side condition needed.**
    The proof still extends a frame, but a **GL** frame: the pair `n`
    extended by a basis of an *arbitrary* complement of `span n`
    (`Submodule.exists_isCompl`), never an adapted frame needing
    `span n ⊕ n^⊥ = V`; nothing in the route intersects `span n` with
    `W`. Statement and proof survive isotropic normals unconditionally.
  - **Field hypothesis (MeetHodge layer): `Field K` + finite
    dimension, nothing else.** No order, no characteristic caveat (the
    wedge-pairing diagonal ±1 is a unit even in char 2), no
    infiniteness — infinite `K` enters the phase only via the Spike-B
    genericity engine.
  - **Fold-back GO (R1-5(iv)).** The metric-free proofs import only
    `Meet.lean`, so the TACTICS-QUIRKS § 59 PiL2 quarantine —
    MeetHodge's only reason to exist — disappears. On fold-back:
    retire `exists_orthonormalBasis_span_pair_eq` (callerless outside
    MeetHodge) and the O(n) pair `complementIso_map_orthogonal_eq`
    (`Meet.lean`, sole caller MeetHodge) /
    `exteriorPower_basis_toDual_map_orthogonal_eq` (sole caller that
    O(n) lemma) — both are the `h = g = O` specializations of the new
    two-map lemmas; the mirror
    `Mathlib/Analysis/InnerProductSpace/PiL2.lean` is orphaned (sole
    importer MeetHodge, grep-verified). None of the four names is
    blueprint-`\lean{}`-pinned (grep-verified over `blueprint/src/`);
    the deletion-variant grep gate still owes the prose repoints (the
    `exteriorPower_map_mem_range_map_subtype_of_mapsTo` docstring in
    `Meet.lean`, the MeetHodge header). Downstream untouched: the sole
    external consumer is `extensor_join_proportional_complementIso_meet`
    (`RigidityMatrix/Claim612.lean`, `AlgebraicInduction/PanelLayer.lean`),
    statement preserved verbatim.
  - **New-decl inventory for the build slice** (all kernel-checked in
    the spike; the three target statements byte-identical to
    `MeetHodge.lean`'s):
    1. `piBasisFun_toDual_eq_sum` — `toDual w v = ∑ i, w i * v i` over
       any field (`Basis.sum_repr` + `Basis.toDual_eq_repr`).
    2. `piBasisFun_toDual_symm` — symmetry, from 1 (replaces the
       inline EuclideanSpace `hsymm` transport; unused by the route
       itself, kept for the sweep).
    3. `finrank_toDualPerp_pair_eq` reproof, general `K`: the perp is
       the `toDualEquiv`-preimage of
       `(span (range n)).dualAnnihilator`, then
       `Subspace.finrank_add_finrank_dualAnnihilator_eq` +
       `finrank_span_eq_card`. (~25 lines, vs. ~60 metric.)
    4. `exteriorPower_basis_toDual_map_dualPair_eq` — two-map Gram
       invariance: `⟨h x, g y⟩ = ⟨x, y⟩` for all `x, y` implies
       `toDual (map n h Z) (map n g B) = toDual Z B`; verbatim
       adaptation of the O(n) proof through
       `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`.
    5. `contragredient g := toDualEquiv.symm ∘ₗ (g.symm).dualMap ∘ₗ
       toDualEquiv` — the `toDual` inverse-transpose of a `≃ₗ`.
    6. `contragredient_toDual_pairing` —
       `⟨contragredient g x, g y⟩ = ⟨x, y⟩` (three rewrites).
    7. `complementIso_map_contragredient_eq` — the equivariance above;
       proof mirrors `complementIso_map_orthogonal_eq` line-for-line
       (pair against `map (k+2−j) g B'` via `map_surjective`;
       `wedgePairing_map` on the left, 4 on the right).
    8. `exists_linearEquiv_basisFun_pair` — `g : V ≃ₗ V` with
       `g e₀ = n 0`, `g e₁ = n 1`: `Submodule.exists_isCompl` on
       `span (range n)` + `finBasisOfFinrankEq` on the complement +
       `linearIndependent_sum` over `Sum.elim`, reindexed by
       `finSumFinEquiv.trans (finCongr _)` (which fixes positions 0,
       1), then `basisOfLinearIndependentOfCardEqFinrank` +
       `Basis.equiv` with `Pi.basisFun`. Hitting `n` *exactly* drops
       the `exists_smul_extensor_eq_of_mem_span_range` proportionality
       step from the chokepoint.
    9. `complementIso_extensor_mem_range_map_subtype` reproof: trivial
       dependent case as now; `W = Q` via 3 +
       `Submodule.eq_of_le_of_finrank_eq`; frame `g` from 8, `h :=
       contragredient g`; `map 2 g e_S = ⟨extensor n, _⟩` exactly (the
       `{0,1}`-enumeration bookkeeping as in the current proof);
       `h e_t ∈ Q` for `t ∉ {0,1}` via 6 + `Basis.toDual_apply`;
       assemble with 7 +
       `exteriorPower_map_mem_range_map_subtype_of_mapsTo` +
       `Submodule.smul_mem`.
    10. `extensor_join_proportional_complementIso_meet` reproof:
       current body verbatim with the two metric calls swapped for 3
       and 9.
