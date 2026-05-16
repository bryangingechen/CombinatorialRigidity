# Phase 8 — Linear-matroid framing (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` §8 for
the high-level plan and `../DESIGN.md` for cross-cutting design
choices.

**Workflow:** Phase 8 runs in **forward blueprint mode** per
`../blueprint/DESIGN.md` *Recommendation for Phase 6* (which
generalised to Phase 6 onward). The Phase 7 chapter
`chapter/rigidity-matroid.tex` already carries the forward-looking
aside that names the linear-matroid framing as future work
(lines 485–498); Phase 8 extends that chapter with a new section
holding the dep-graph + lemma index. This file does **not**
duplicate the dep-graph.

## Current state

**Phase 8 complete.** `SimpleGraph.linearRigidityMatroid_eq_rigidityMatroid`
in `LinearRigidityMatroid.lean` lands the matroid identification of
the linear rigidity matroid with the combinatorial planar rigidity
matroid in dimension 2 (Lovász–Yemini, linear-matroid form). The
phase shipped:

- the `linearRigidityMatroid V d p` definition built on
  `apnelson1/Matroid`'s `Matroid.ofFun`, with extension of
  `(⊤).rigidityRow p` from `(⊤).edgeSet` to all of `Sym2 V` by zero
  off the edge set via `Function.extend` (see FRICTION
  *Extending a function on a subtype via `Function.extend`*).
- the row-LI bridge
  `linearRigidityMatroid_indep_iff_edgeSetRowIndependent` (linear-
  matroid analogue of Phase 7's matroid-form Lovász–Yemini bridge).
- the uniform-genericity auxiliary
  `exists_uniform_rowIndependent_placement_dim_two`: induction on
  the finite family of `(2, 3)`-sparse subsets via linear-interpolation
  perturbation, closing through the polynomial-along-line cofinite helper.
- two new mirror lemmas under
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`:
  `Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero`
  (rectangular Gram-det characterization, derived from
  `rank_self_mul_transpose`) and
  `LinearIndependent.finite_setOf_not_along_affine_path` (cofiniteness
  of LI along an affine line, via the polynomial-entry matrix
  `X • C(B) + C(A)` and `Polynomial.finite_setOf_isRoot`).
- the project-internal helper `rigidityRow_add_smul` in
  `RigidityMatroid.lean` capturing linearity of `rigidityRow` in the
  placement, the bridge from `Framework`-level affine paths to
  `Module.Dual`-level affine paths.

Blueprint section *Linear-matroid framing* in
`chapter/rigidity-matroid.tex` is fully `\leanok`; the dep-graph at
`blueprint/web/dep_graph_document.html` is fully green.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Add `apnelson1/Matroid` as a dependency** (per `../DESIGN.md`
  *Phase 8: `apnelson1/Matroid` dependency*; Phase 6 investigation
  closed at commit `5f11c6b` confirmed matching toolchain pin). The
  alternatives — mirror `Matroid.ofFun` under
  `CombinatorialRigidity/Mathlib/Combinatorics/Matroid/` or build the
  matroid directly on mathlib's `IndepMatroid.ofFinitaryCardAugment`
  — were considered and rejected: the first duplicates upstream-
  eligible code that already lives at a matching pin; the second
  throws away the named abstraction Phase 6's audit already picked
  as the right one.

- **Forward-mode blueprint authoring.** Extend
  `chapter/rigidity-matroid.tex` with a new section
  *Linear-matroid framing* whose dep-graph is the authoritative
  Phase 8 lemma index. Do **not** maintain a parallel checklist
  here. Rationale: `../blueprint/DESIGN.md` *Recommendation for
  Phase 6*.

- **New file `LinearRigidityMatroid.lean`.** Slots beside
  `MatroidIdentification.lean`. Imports `MatroidIdentification`
  (for `SimpleGraph.rigidityMatroid` + the row-LI iff) plus
  `Matroid.ofFun` from the new dep. Keeps `MatroidIdentification.lean`
  matroid-construction-agnostic (it only uses `IndepMatroid.ofFinite`
  via `CountMatroid.lean`).

- **Target statement: matroid isomorphism, not equality.** The Phase 7
  chapter aside writes the goal as
  $M_{p_{\text{gen}}} \cong \mathrm{rigidityMatroid}\,V$.
  Two matroids on the same ground set $E(K_V)$ with the same
  independence relation are equal as `Matroid (Sym2 V)`, so we
  expect the final statement to be definitional equality / propositional
  equality of the `Matroid` packages, not a structural iso. The
  *content* is the bridge lemma identifying the two independence
  relations; the *package equality* falls out of matroid extensionality.
  Decision to revisit if `Matroid.ofFun`'s ground set ends up being
  `Set α` rather than `Sym2 V`-shaped — in which case an explicit
  `Matroid.mapEquiv`-style iso is the right shape.

- **"Generic placement" formulation.** The linear matroid is
  `Matroid.ofFun (G.rigidityRow p)` for *some* placement $p$; the
  matroid identity holds at any placement that achieves maximum
  rank on every dependent set, and Phase 6's
  `exists_affinelySpanning_of_eventually` plus the Phase 7
  row-LI-openness lemma `EdgeSetRowIndependent.eventually` package
  the existence witness. No Zariski-open / measure-zero notion is
  introduced.

## Lemma checklist

**Maintained in the blueprint, not here.** All four dep-graph nodes
(`def:linearRigidityRow`, `def:linearRigidityMatroid`,
`lem:linearRigidityMatroid-indep-iff`,
`lem:exists-uniform-rowIndependent-placement`,
`thm:linearRigidityMatroid-eq-rigidityMatroid`) are
`\leanok`-tagged green in
`chapter/rigidity-matroid.tex`'s *Linear-matroid framing* subsection.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Polynomial-along-line via rectangular Gram det, not minors.** The
  natural form of "LI cofinitely along an affine line `M(t) = A + t • B`"
  is "the bad-`t` set is finite when LI holds at some `t₀`". This breaks
  into two mathlib gaps: (i) a rectangular analogue of
  `Matrix.linearIndependent_rows_iff_isUnit`, namely "rows of `M` LI
  ↔ `(M * Mᵀ).det ≠ 0`" over `LinearOrderedField`; (ii) the cofiniteness
  via `Polynomial.finite_setOf_isRoot` applied to
  `det((X • C(B) + C(A)) * (X • C(B) + C(A))ᵀ)`. The Gram-det route was
  chosen over a minor-based "∃ |ι|×|ι| nonzero submatrix" route because
  `Matrix.rank_self_mul_transpose` already exists in mathlib (over
  `LinearOrderedField`), bridging rectangular rank to a square unit
  question with no new minor-rank machinery. Both pieces landed as
  upstream-eligible mirrors in
  `CombinatorialRigidity/Mathlib/LinearAlgebra/Matrix/Rank.lean`.

- **Extension by zero off the edge set via `Function.extend`.** The
  underlying row function of `linearRigidityMatroid V d p` extends
  `(⊤).rigidityRow p : (⊤).edgeSet → Module.Dual …` to all of
  `Sym2 V` by zero off the edge set. The natural dependent
  `if h : e ∈ (⊤).edgeSet then … else 0` shape needs
  `Decidable (e ∈ (⊤).edgeSet)` (not auto-synthesizable);
  `Function.extend Subtype.val ((⊤).rigidityRow p) 0` avoids the
  instance dance entirely and gives clean rewrites via
  `Subtype.val_injective.extend_apply`. See FRICTION
  *Extending a function on a subtype to the parent type*.

- **No `[Finite V]` on `linearRigidityMatroid`.** `Matroid.ofFun`
  doesn't require finiteness, and the unused-arguments lint
  enforces dropping it (matching ROADMAP's weakest-typeclass
  convention). The matroid identification with `rigidityMatroid V`
  (red target) will pull in `[Finite V]` at its statement, since
  `rigidityMatroid V` requires it.

- **Uniform-genericity as a separate auxiliary lemma.** The Phase 8
  opening (`3e7e2e5`) sketched the matroid equality as a direct
  composition of `EdgeSetRowIndependent.eventually` with
  `exists_affinelySpanning_of_eventually`, but those only give *one*
  placement row-LI on *one* edge subset — not a placement uniformly
  row-LI across the finite family of `(2, 3)`-sparse subsets the
  matroid equality needs. The uniform collapse becomes its own
  lemma `exists_uniform_rowIndependent_placement_dim_two` (linear-
  interpolation perturbation on the finset, closing via the
  polynomial-along-line cofinite helper). Blueprint surfaces it as
  the explicit red node `lem:exists-uniform-rowIndependent-placement`.

- **Subtype factoring at `Matroid.ext_indep`.** Converting
  `J : Set (Sym2 V)` (with `J ⊆ (⊤).edgeSet`) to
  `I : Set (⊤).edgeSet` via `I := Subtype.val ⁻¹' J` and
  `hI_image : Subtype.val '' I = J` (`Set.image_preimage_eq_of_subset`
  + `Subtype.range_coe`) lets the two pre-existing
  `_indep_iff_edgeSetRowIndependent` iffs (both keyed on `Set (⊤).
  edgeSet`) apply. Watch-only: promote to TACTICS-GOLF if the shape
  recurs at a second matroid-identity site.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Extension by zero off a subtype: prefer `Function.extend` over
  `dite`* → FRICTION [resolved] *Extending a function on a subtype
  to the parent type — `dite` vs `Function.extend`*

### Cleanup pass summaries

*(Empty — no cleanup pass yet.)*

## Blockers / open questions

- ~~**apnelson1/Matroid pin drift.**~~ **Resolved at dep-bump
  commit.** Pinned to `e6852cec…`; `lake build Matroid.Representation.Map`
  green against our mathlib `21b745fd…` despite the 179-commit
  forward gap. Pin-drift recurrence is now in `DESIGN.md` *Choices
  to revisit → Phase 8: `apnelson1/Matroid` dependency* as a
  "watch this on every mathlib bump" reminder.

- ~~**Ground-set shape of `Matroid.ofFun`.**~~ **Resolved.**
  Signature `Matroid.ofFun ℝ E f : Matroid α` (with `f : α → W`,
  ground set `E`). Our linear matroid lands on `Sym2 V` with ground
  set `(⊤ : SimpleGraph V).edgeSet`, matching `rigidityMatroid V`'s
  ground set exactly, so package equality is the right target.
  `Matroid.ofFun` requires `f` on all of `Sym2 V`; extending
  `(⊤).rigidityRow p` by zero off the edge set bridges via
  `Function.extend`.

- **Mathlib upstream of `Matroid.ofFun`.** If `Matroid.ofFun` lands
  in mathlib during the phase (apnelson1's matroid library has been
  upstreaming piecewise), the dependency becomes redundant. Track;
  drop the dep in that case.

## Hand-off / next phase

Phase 8 closes the rigidity-matroid trio (combinatorial $(2, 3)$-count
matroid from Phase 7, linear matroid `Matroid.ofFun` at a generic
placement from Phase 8) and ends the planned ROADMAP. No follow-up
phase is queued. Possible next directions:

- **Drop the `apnelson1/Matroid` dep** if `Matroid.ofFun` lands
  upstream in mathlib (currently apnelson1's matroid library is being
  upstreamed piecewise — watch the dep-bump cron PR for absorption).
- **Upstream the two mirror lemmas**
  (`Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero` and
  `LinearIndependent.finite_setOf_not_along_affine_path`,
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`). Both are direct
  corollaries of `Matrix.rank_self_mul_transpose` and standard
  `Polynomial` machinery — the kind of "missing iff" packaging that
  mathlib accepts without controversy.
- **Higher-dimensional generalization.** The Phase 8 target is
  stated at dimension 2 because Phase 6/7's row-LI ↔ sparse iff is
  dim-2-specific (Lovász–Yemini's $\Leftarrow$ direction at $d > 2$
  is open in the literature). A $d$-general analogue would track the
  rigidity-matroid-from-`Matroid.ofFun` definition; the matroid
  identification with $(d, \binom{d+1}{2})$-sparsity is the open
  $d$-general generic-rigidity conjecture for $d \geq 3$.
- **Post-Phase-8 cleanup round.** Opened at commit `f133a7b`,
  scoped light (Phase 8 surface only) for buckets A–D + import-
  structure audit-only for bucket E. See
  `Phase8-cleanup.md` for the round's work log and round-level
  manual `../CLEANUP.md` for discipline.
