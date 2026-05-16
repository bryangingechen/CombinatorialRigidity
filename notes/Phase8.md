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

Phase opened by a scaffolding commit (this file + ROADMAP Status
table + §8 plan; no Lean changes). Next concrete commit adds
`apnelson1/Matroid` to `lakefile.toml` and runs `lake update` so
the manifest pins resolve, then runs `lake build` to confirm the
new dep imports cleanly alongside mathlib. After the dep lands, the
first Lean commit opens `CombinatorialRigidity/LinearRigidityMatroid.lean`
with the `linearRigidityMatroid` definition skeleton via
`Matroid.ofFun`.

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

- **apnelson1/Matroid pin drift.** Phase 6 confirmed matching
  toolchain pin at commit `5f11c6b` (2026-05-13). If `lake update`
  surfaces a pin mismatch, options are: bump our mathlib pin to
  match, pin apnelson1 to an older revision matching ours, or
  vendor `Matroid.ofFun` under our `Mathlib/` mirror. Track in a
  blocker entry if this comes up.

- **Ground-set shape of `Matroid.ofFun`.** If `Matroid.ofFun`'s
  ground set is `Set α` (for the function's domain) and our
  `G.rigidityRow` is indexed by `G.edgeSet : Set (Sym2 V)`, the
  linear matroid lands on `Set (Sym2 V)` and matches
  `rigidityMatroid V` directly — equality, not iso. If instead it
  lands on a subtype, an extensionality / restriction step
  intervenes. To be confirmed once the dep is in.

- **Mathlib upstream of `Matroid.ofFun`.** If `Matroid.ofFun` lands
  in mathlib during the phase (apnelson1's matroid library has been
  upstreaming piecewise), the dependency becomes redundant. Track;
  drop the dep in that case.

## Hand-off / next phase

*(To be filled when Phase 8 closes.)*
