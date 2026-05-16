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

Phase opened by a scaffolding commit (`3e7e2e5`), the dep-bump
landing `apnelson1/Matroid` at revision `e6852cec…` (`6df664c`),
and the **skeleton commit** that lands
`CombinatorialRigidity/LinearRigidityMatroid.lean` with the
`linearRigidityMatroid` def + the row-LI bridge
(`linearRigidityMatroid_indep_iff_edgeSetRowIndependent`) and adds
the *Linear-matroid framing* subsection to
`blueprint/src/chapter/rigidity-matroid.tex` (dep-graph: three
green leaves + one red target `thm:linearRigidityMatroid-eq-rigidityMatroid`).

Next concrete commit: land the **auxiliary** uniform-genericity
lemma `SimpleGraph.exists_uniform_rowIndependent_placement_dim_two`
— existence of a placement `p : Framework V 2` row-LI on *every*
`(2, 3)`-sparse edge subset of `K_V` simultaneously. This is the new
red leaf `lem:exists-uniform-rowIndependent-placement` in the
blueprint. The originally-sketched composition
"`EdgeSetRowIndependent.eventually` +
`exists_affinelySpanning_of_eventually`" gives a single `p`
satisfying *one* row-LI property along with affine spanning, not a
`p` uniform across the finite family of `(2, 3)`-sparse subsets —
the genuinely new content is the linear-interpolation perturbation
in the proof of the auxiliary (see blueprint proof sketch). Once
the auxiliary lands, the main target
`linearRigidityMatroid_eq_rigidityMatroid` follows via
`Matroid.ext_indep` reducing to ground-set agreement (one `rfl`)
and per-set independence agreement
(`linearRigidityMatroid_indep_iff_edgeSetRowIndependent` ↔
`rigidityMatroid_indep_iff_edgeSetRowIndependent` modulo the
uniform-genericity collapse of the existential).

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
  in dimension 2 for a chosen generic placement. **Done.**
- `lem:linearRigidityMatroid-indep-iff` — independent iff
  row-LI at $p$. **Done.**
- `lem:exists-uniform-rowIndependent-placement` — existence of a
  single placement `p` row-LI on every `(2, 3)`-sparse edge subset
  of `K_V` simultaneously. Proof via linear-interpolation
  perturbation: induct on the finite family of sparse subsets;
  along the interpolation `p_t := (1−t) p_0 + t q` between the IH
  witness `p_0` and a new-subset witness `q`, each "row-LI on S"
  condition is a polynomial-in-`t` nonzero at `t = 0` or `t = 1`,
  so cofinitely-many `t` work.
- `thm:linearRigidityMatroid-eq-rigidityMatroid` — the matroid
  identification. Composes Phase 7's
  `rigidityMatroid_indep_iff_edgeSetRowIndependent` with the
  uniform-genericity witness above.

The actual entries will land in the blueprint as the Lean lemmas
are formalized.

## Decisions made during this phase

### Phase-local choices and proof techniques

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

- **Uniform-genericity as a separate auxiliary lemma.** The
  original Phase 8 opening (commit `3e7e2e5`) sketched the matroid
  equality as a direct composition of `EdgeSetRowIndependent.eventually`
  with `exists_affinelySpanning_of_eventually`. On re-examination
  those two only give *one* placement `p` simultaneously row-LI on
  *one* edge subset and affinely-spanning — not a `p` uniformly
  row-LI across the finitely many `(2, 3)`-sparse subsets that
  `rigidityMatroid V`'s existential ranges over. The uniform
  collapse needs its own lemma
  `exists_uniform_rowIndependent_placement_dim_two` whose proof is
  linear-interpolation perturbation on a finset (a polynomial-in-`t`
  nonzero somewhere has finitely many roots, so the union of
  bad-`t` sets across the finite family is finite). Blueprint
  updated to surface this as an explicit red node
  `lem:exists-uniform-rowIndependent-placement` and rewrite the
  main theorem's proof sketch accordingly.

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
