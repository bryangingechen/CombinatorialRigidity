# Phase 8 — Linear-matroid framing (work log)

**Status:** in progress.

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

Phase opened by a scaffolding commit (`3e7e2e5`), followed by the
dep bump landing `apnelson1/Matroid` at revision `e6852cec…` (commit
*to land next*). `lake build Matroid.Representation.Map` and
`lake build CombinatorialRigidity.MatroidIdentification` both green
post-bump, so the 179-commit mathlib-pin gap (apnelson1's `1b045b9…`
→ ours `21b745fd…`) didn't break apnelson1's API.

Next concrete commit: open `CombinatorialRigidity/LinearRigidityMatroid.lean`
with the `linearRigidityMatroid` definition skeleton via
`Matroid.ofFun`, plus the *Linear-matroid framing* section in
`blueprint/src/chapter/rigidity-matroid.tex` carrying the
dep-graph for the new section.

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

**Maintained in the blueprint, not here.** The authoritative
checklist will be `chapter/rigidity-matroid.tex`'s *Linear-matroid
framing* section, visible as a dep-graph at
`blueprint/web/dep_graph_document.html` after `inv bp && inv web`.
A red node = not yet formalized; a green node = formalized and
`\leanok`-tagged. Pick leaf-most red.

Sketch of the planned nodes (the blueprint will hold the final
list):

- `def:linearRigidityMatroid` — `Matroid.ofFun (G.rigidityRow p)`
  in dimension 2 for a chosen generic placement.
- `lem:linearRigidityMatroid-indep-iff` — independent iff
  row-LI at $p$.
- `thm:linearRigidityMatroid-eq-rigidityMatroid` — the matroid
  identification. Composes Phase 7's
  `rigidityMatroid_indep_iff_edgeSetRowIndependent` with the
  generic-placement existence witness.

The actual entries will land in the blueprint as the Lean lemmas
are formalized.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — to be filled as Phase 8 lands lemmas.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — to be filled at phase end.)*

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
  Signature is `Matroid.ofFun (𝔽 : Type*) [DivisionRing 𝔽]
  [Module 𝔽 W] (E : Set α) (f : α → W) : Matroid α` (in
  `Matroid/Representation/Map.lean`). Ground set is `E`. For our
  purposes the linear matroid lands on `Sym2 V` with ground set
  `(⊤ : SimpleGraph V).edgeSet`, matching `rigidityMatroid V`'s
  ground set exactly — package equality is the right target.
  `Matroid.ofFun` requires an `f` defined on all of `α = Sym2 V`,
  not just `G.edgeSet`; extending `G.rigidityRow p` by zero off
  `G.edgeSet` is the obvious move (the bridge lemma will then
  identify the two matroids' independent sets via
  `rigidityMatroid_indep_iff_edgeSetRowIndependent`).

- **Mathlib upstream of `Matroid.ofFun`.** If `Matroid.ofFun` lands
  in mathlib during the phase (apnelson1's matroid library has been
  upstreaming piecewise), the dependency becomes redundant. Track;
  drop the dep in that case.

## Hand-off / next phase

*(To be filled when Phase 8 closes.)*
