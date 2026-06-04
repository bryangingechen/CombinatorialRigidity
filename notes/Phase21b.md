# Phase 21b — Genericity device (Claim 6.4/6.9) (work log)

**Status:** in progress (opened 2026-06-03).

Sub-phase scoped out of Phase 21 on 2026-06-03 (user decision, risk
#4/#7), the **analytic sibling** of the Phase-21a meet sub-phase. The one
genuinely new analytic crux of Katoh–Tanigawa's algebraic induction
(KT 2011 §6.1 Claim 6.4, §6.3 Claim 6.9): the entries of the panel-hinge
rigidity matrix `R(G,p)` are polynomials in the algebraically independent
panel coordinates (the per-vertex normals), so the rank is lower
semicontinuous and attains its maximum on a Zariski-open (generic) set —
hence a *single* good realization at the target rank lifts to a *generic*
one. This is the shared black-box that Phase 21 left cited in `lem:case-I`
(`hglue`), `lem:case-II` (`hspan`), `thm:theorem-55` (transitively),
`prop:rigidity-matrix-prop11` (`hub`/`hgen`), and the projective assembly
of `lem:cycle-realization`. Phase 21b discharges it once; the consumers
flip GREEN-modulo-21b → GREEN.

Program-level plan, reuse map, citations, risk register:
`notes/MolecularConjecture.md` *Phase 21b*. Scope-out rationale + the
node-by-node consumer split: `DESIGN.md` *Genericity device (Claim
6.4/6.9) is its own sub-phase (Phase 21b)* and `notes/Phase21.md`
*Hand-off*. Forward-mode dep-graph node:
`blueprint/src/chapter/algebraic-induction.tex`
(`lem:genericity-device`, `sec:molecular-algebraic-induction-genericity`).
Lean lands in `CombinatorialRigidity/Molecular/AlgebraicInduction.lean`
(beside the consumers) unless it grows enough to warrant its own file.

## Current state

**Cross-hinge star independence landed (2026-06-03) — `linearIndependent_hingeRow_star`: rows from distinct hinges at a common body are jointly independent.**
`linearIndependent_hingeRow_star` (`Molecular/RigidityMatrix.lean`, after
`exists_independent_rigidityRows_of_edge`): fix a body `v` and distinct other endpoints
`w : J → α` (`hw` injective, `hwv` each `w j ≠ v`) — a *star* of edges all incident to `v`, the
shape a rigid block pinned at `v` presents. If for each `j` the hinge-row functionals `r j` are LI,
the combined rigidity-row family `⟨j,i⟩ ↦ hingeRow (w j) v (r j i)` over `Σ j, I j` is LI on
`α → ScrewSpace k`. This is the **substantive cross-hinge step** the hand-off flagged:
`linearIndependent_hingeRow`'s single-edge dual-map argument does not extend because rows from
*different* hinges route through *different* `screwDiff (w j) v`. The independence is instead the
*pin-a-body* / disjoint-support count — evaluate a vanishing combination at
`Function.update 0 (w j₀) x` (place `x` on body `w j₀`, `0` elsewhere; legitimate since `w j₀ ≠ v`
and the `w j` distinct), which collapses the `Σ`-sum (via `Fintype.sum_sigma` + `Finset.sum_eq_single
j₀`) to `∑ i, c⟨j₀,i⟩ • (r j₀ i) x = 0` for all `x`, so per-hinge independence
(`Fintype.linearIndependent_iff` on `r j₀`) forces every coefficient at `j₀` to vanish. Green, build
warning-clean + lint clean, checkdecls clean, axioms {propext, Classical.choice, Quot.sound}. Folded
into the `def:rigidity-matrix` node's `\lean{...}` pin (the cross-hinge sibling of the per-edge
brick); node body gains a sentence on the star combination. **Residual Case-I work toward `hindep`:**
the star handles all of one rigid block's hinges that share a *single* pinned body; the remaining
geometric content (the genuine cycle/spanning-tree structure of a rigid block whose hinges span
multiple bodies, where the `m ≤ D` extensor-independence of `lem:cycle-realization` re-enters) plus
exhibiting `F₀` and matching `#s = D(|V|−1) − dim Z_s` (`hmatch`) is the rest of `hglue_of_realization`'s
inputs.

**Per-edge independent-rows brick landed (2026-06-03) — `exists_independent_rigidityRows_of_edge`: one transversal hinge ⇒ `D−1` independent rigidity rows.**
`exists_independent_rigidityRows_of_edge` (`Molecular/RigidityMatrix.lean`, after
`finrank_hingeRowBlock`): for a genuine edge `e = uv` (`u ≠ v`, `supportExtensor e ≠ 0`,
transversal hinge) there is an LI family `Fin (screwDim k − 1) → Dual ℝ (α → ScrewSpace k)` of
rigidity rows, all in `F.rigidityRows`. Composes the two prior per-edge bricks: a basis of the
`(D−1)`-dimensional hinge-row block (`finrank_hingeRowBlock`) coerced out as ambient functionals,
then lifted to rigidity rows by `linearIndependent_hingeRow`; membership in `rigidityRows` by the
`⟨e, u, v, hlink, c i, …⟩` witness. The basis-coercion is factored into a new upstream-eligible
mirror lemma `Submodule.exists_linearIndependent_fin_of_finrank_eq`
(`Mathlib/LinearAlgebra/Dimension/Constructions.lean`): a finite-dim subspace `W` of finrank `n`
carries an LI family `Fin n → V` valued in `W` (the basis, coerced along `W.subtype`). The
existence-over-abstract-field form is *load-bearing*: doing the basis/`map'` step inside
`RigidityMatrix.lean` directly timed out at `whnf` (the heavy `Module.Dual` of an exterior power
unfolds during `Basis.linearIndependent.map' W.subtype` unification); the mirror lemma's opaque
proof keeps `ScrewSpace` from unfolding at the use site (FRICTION [molecular] entry). This is the
per-edge unit of the Case-I `hindep`/`hmatch` assembly — each transversal hinge of a rigid block
contributes exactly `D − 1` independent rows of `R(G,p)`. Green, build warning-clean + lint clean,
checkdecls clean, axioms {propext, Classical.choice, Quot.sound}. Folded into the
`def:rigidity-matrix` node's `\lean{...}` pin (the mirror lemma is skipped per the blueprint
mirror-lemma rule); node body gains a sentence on the per-edge `D−1`-row count. Residual Case-I work:
combine across the rigid block's hinges into a single LI family indexed by `s`, match
`#s = D(|V|−1) − dim Z_s` (`hmatch`), and exhibit the realization `F₀`.

**Independence bridge landed (2026-06-03) — Case-I `hindep` brick: independent extensors → independent rigidity rows.**
`linearIndependent_hingeRow` (`Molecular/RigidityMatrix.lean`, after `hingeRow_apply`),
with two supporting glue lemmas `screwDiff_surjective` and `hingeRow_eq_dualMap`:
for a genuine edge `e = uv` with distinct endpoints (`u ≠ v`), if a family `r : ι → Dual ℝ
(ScrewSpace k)` of hinge-row-block functionals is LI, then so is the induced rigidity-row family
`i ↦ hingeRow u v (r i)` on `α → ScrewSpace k`. Proof: `screwDiff u v` (the relative-screw
evaluation `S ↦ S u − S v`) is surjective at distinct bodies (`Function.update 0 u x` witness,
`classical` for `DecidableEq α`), so its dual map `(screwDiff u v).dualMap = hingeRow u v`
(`hingeRow_eq_dualMap`, definitional via `LinearMap.dualMap_apply'`) is injective
(`LinearMap.dualMap_injective_of_surjective`), and `LinearIndependent.map'` preserves LI under an
injective linear map. This turns the independent supporting extensors of a rigid block
(`exists_independent_panelSupportExtensor`, through the `(D−1)`-dim hinge-row block
`finrank_hingeRowBlock`) into the independent rigidity-row subfamily `hglue_of_realization`'s
`hindep` requires — one transversal hinge `e = uv` contributes `D − 1` independent rows of
`R(G,p)`, all routed through the same `screwDiff u v`, so block-row independence reduces to
hinge-row-block independence. Green, build warning-clean + lint clean, checkdecls clean, axioms
{propext, Classical.choice, Quot.sound}. Folded into the `def:rigidity-matrix` node's `\lean{...}`
pin (`linearIndependent_hingeRow`; the two glue lemmas are skipped per the blueprint skip-glue
rule); node body gains one sentence on the row-map injectivity. Residual Case-I work: assemble the
single realization `F₀` and match `#s` to the corank (`hmatch`) — the genuinely-geometric §6.2/6.5
piece; `hindep` is now a single edge-by-edge application of this bridge over the rigid block's hinges.

**Per-edge row-count brick landed (2026-06-03) — first geometric brick toward Case-I `hindep`/`hmatch`.**
`finrank_hingeRowBlock` (`Molecular/RigidityMatrix.lean`, after `exists_finite_spanning_rigidityRows`):
when the supporting extensor `C(p(e))` is nonzero (transversal hinge, the
`panelSupportExtensor_ne_zero_iff` general-position condition), the hinge-row block
`r(p(e)) = (span C(p(e)))^⊥` has dimension `D − 1`, `finrank ℝ (hingeRowBlock e) = screwDim k − 1`.
Three-line proof: `Subspace.finrank_add_finrank_dualAnnihilator_eq` (codimension identity) +
`finrank_span_singleton` (the `1`-dim span of a nonzero extensor) + `screwSpace_finrank` + `omega`.
This is Katoh–Tanigawa's `(D−1) × D` block-row count carried basis-free — the per-edge brick that
counts the rigidity rows `rigidityRows` of a rigid block, the source of the matching-size
independent subfamily `s` that `hglue_of_realization`'s `hindep`/`hmatch` require. Green, build
warning-clean + lint clean, axioms {propext, Classical.choice, Quot.sound}. Folded into the
`def:hinge-row-block` node's `\lean{...}` pin (the `(D−1)`-row count is exactly that node's content;
no new node).

**Finite spanning row family landed (2026-06-03) — input (2) of `hglue_of_realization` discharged.**
`exists_finite_spanning_rigidityRows` (`Molecular/RigidityMatrix.lean`, after
`infinitesimalMotions_eq_dualCoannihilator`): when `α` is finite, the screw-assignment space
`α → ScrewSpace k` is finite-dimensional (`finrank_screwAssignment`), so its dual is too
(`Subspace.instModuleDualFiniteDimensional`) and every submodule is FG — in particular
`span ℝ F.rigidityRows`. Hence a *finite* family `a : Fin n → Dual ℝ (α → ScrewSpace k)` with
`span (range a) = span F.rigidityRows` exists (`Submodule.fg_iff_exists_fin_generating_family` via
`IsNoetherian.noetherian`). This is exactly input (2) the Case-I capstone `hglue_of_realization`
requires (the finite-index spanning family `a` + `hspanrows`), and `Fin n` is `Finite` so it fits
the consumer's `[Finite ι]`. The two residual Case-I inputs (the single realization `F₀` and the
matching-size independent subfamily `s` from `exists_independent_panelSupportExtensor`) remain — the
genuinely-geometric assembly. Green, build warning-clean + lint clean, checkdecls clean, axioms
{propext, Classical.choice, Quot.sound}. Folded into the `def:rigidity-matrix` node's `\lean{...}`
pin (device-plumbing for an existing node, not a new node).

**Route-(a) decision RESOLVED + Case-I `hglue` capstone landed (2026-06-03).** The route a/b
question the hand-off flagged as "where the decision finally bites" resolves in favour of **route
(a) with a degenerate (constant) affine path**. Key observation: Case I's witness realization is
*constructed directly* by `exists_independent_panelSupportExtensor` (a basis choice on `⋀²`, Phase
17/21), not reached by perturbation, so the device can run on the **constant** path `F t = F₀` with
`b = 0`. The bilinearity obstruction (panel rows quadratic along a real line through normal-space)
never bites because no real line is traversed — the device reads off the corank at the one hand-built
realization, which is all Case I's block-triangular gluing needs. Three new declarations after
`hglue_of_genericityDevice` in `Molecular/AlgebraicInduction.lean`:
- `hspan_const_of_span_eq` — the `hspan` of the constant family: for any family `a` spanning
  `rigidityRows F₀`, `span (range (fun i => a i + t • 0)) = span (rigidityRows F₀)` at every `t`
  (`smul_zero`/`add_zero`).
- `hcoord_const` — discharges the device's `hcoord` for the constant family from `hspanrows`
  (`span (range a) = span (rigidityRows F₀)`), via `hcoord_of_rigidityRows_affine`.
- `hglue_of_realization` — the **consumer-facing Case-I capstone**: from a single realization `F₀`,
  a *finite* family `a` spanning its rigidity rows, an independent subfamily `s` (size = the
  contraction's inductive rank via `hmatch`), produces the `hglue` inequality
  `dim Z(F₀) ≤ D + dim Z_s` at `F₀` itself — all affine-path plumbing discharged.

The index `ι` is kept abstract + `[Finite]` (the engine needs a finite index; the
finite-dimensional row space admits a finite spanning subfamily). The residual per-consumer work is
now purely combinatorial-geometric (exhibit `F₀`, the finite spanning `a`, and the matching-size
independent `s` from the contraction realization + rigid block) — **no path construction remains**.
Green, build warning-clean + lint clean, axioms {propext, Classical.choice, Quot.sound}. Folded
into the `lem:genericity-device` node's `\lean{...}` pin (consumer-facing API, not a new node);
statement + proof prose updated to record the constant-path route-(a) resolution.

**`hcoord` bridge landed (2026-06-03) — step (i) reduced to a pure-geometry obligation.**
`hcoord_of_rigidityRows_affine` (before `genericityDevice` in `Molecular/AlgebraicInduction.lean`)
discharges the device's `hcoord` hypothesis from the strictly more workable input a consumer can
produce: an affine functional family `t ↦ a i + t • b i` whose *span* equals `span (rigidityRows
(F t))` at every `t` (`hspan`). Two-line proof — `rw [hspan t,
infinitesimalMotions_eq_dualCoannihilator]` (Phase 18 coannihilator coordinatization +
`dualCoannihilator` respecting span equality under `rw`). This isolates the step-(i) obligation to
its geometric core: a consumer now needs only to exhibit such an `a, b` with `hspan` (an
*equality of spans*, no `dualCoannihilator` bookkeeping), and the device's analytic content + the
arithmetic `hglue_of_genericityDevice` bridge are already in place. The residual genuinely-open
piece is unchanged — *constructing* `a, b`: the panel rows depend bilinearly on the normals, so the
affine path must be chosen so the row functionals (not the normals) come out affine (route (a),
Phase-8 single-scalar trick), or the engine generalized to a multivariate Zariski-open form (route
(b)). Green, build warning-clean + lint clean, axioms {propext, Classical.choice, Quot.sound}.
Folded into the `lem:genericity-device` node's `\lean{...}` pin (consumer-facing API, not a new
node).

**Case I `hglue` wiring landed (2026-06-03), route-(a) call made.** Two new
declarations after `genericityDevice` in `Molecular/AlgebraicInduction.lean`:
`exists_good_realization` (the device's **generic-point form** — the finite
bad set's complement is nonempty in `ℝ`, so a *single* good realization at the
witnessed corank exists, via `Set.Finite.infinite_compl`) and
`hglue_of_genericityDevice` (the **Case-I block-triangular bridge**: at the
good realization, the rank-match `#s = D(|V|−1) − dim Z_s` collapses the
device's absolute `dim Z ≤ D|V| − #s` to Case I's relative
`hglue : dim Z ≤ D + dim Z_s`; `mul_sub` + `omega`). **The route call: route
(a)** — the genericity content is entirely in `hcoord` + `hindep` (the affine
coordinatization + the witnessed independent subfamily); the residual is
isolated as the `hmatch` hypothesis (the corank `#s` equals the contraction's
inductive rank `D(|V|−1) − dim Z_s`). This is the genuinely-open geometric
piece — *constructing* the affine path and the witness subfamily of the
matching size from the contraction realization — now isolated cleanly from the
arithmetic, which this commit fully discharges. Green, build warning-clean +
lint clean, axioms {propext, Classical.choice, Quot.sound}. Folded into the
`lem:genericity-device` node's `\lean{...}` pin (consumer-facing API of the
device, not a new node).

**Abstract genericity device landed (2026-06-03) — `lem:genericity-device`
GREEN.** `CombinatorialRigidity.Molecular.genericityDevice` (end of
`Molecular/AlgebraicInduction.lean`) composes the two Phase-21b bricks into
the device's consumer-facing **codimension shape**: given a one-parameter
family of frameworks `F : ℝ → BodyHingeFramework k α β` whose null spaces are
coordinatized by a single affine functional family `a b : ι → Dual ℝ (α →
ScrewSpace k)` (`hcoord : ∀ t, (F t).infinitesimalMotions = (span (range
(fun i => a i + t • b i))).dualCoannihilator`, the per-`t`
`infinitesimalMotions_eq_dualCoannihilator`) and a subfamily `s` LI at one
realization `t₀`, the bad-`t` set `{t | D|V| < #s + dim Z(F t)}` is finite —
i.e. `dim Z(G,p_t) ≤ D|V| − #s` for cofinitely many `t`. Three-line proof:
`finrank_dualCoannihilator_along_affine_path_cofinite` (engine) +
`finrank_screwAssignment` (`finrank (α→ScrewSpace k) = D|V|`) + `hcoord`.
Green, build warning-clean + lint clean, axioms {propext, Classical.choice,
Quot.sound}. The blueprint node `lem:genericity-device` flips green (`\lean` +
`\leanok`), restated in the dual codimension form it now formalizes.

**Scoping finding (the API gap, now pinned): the panel rows are NOT affine
in a single scalar.** The engine (`Rank.lean` bricks) is genuinely affine-only
(`a i + t • b i`, degree ≤ 1, via the one-variable Gram-det polynomial). But
`panelSupportExtensor n_u n_v = complementIso (n_u ∧ n_v)` is *bilinear* in the
normals, so a generic line through panel-coordinate space gives a row family
that is **quadratic**, not affine, in `t`. The abstract device fixes the
target shape (`hcoord` takes the affine family as a hypothesis); the residual
per-consumer wiring must either (a) present each consumer's rows as an affine
family along a *chosen* path (the single-scalar restriction route that worked
for Phase 8's `exists_uniform_rowIndependent_placement`), or (b) generalize
the engine to a multivariate Zariski-open form. This is the genuinely open
piece — see *Hand-off*.

**RigidityMatrix coordinatization landed (2026-06-03), connecting the
analytic engine to the consumers.** Step (i) of the hand-off is done:
`F.infinitesimalMotions` is now expressed as the `dualCoannihilator` of
the span of an explicit row-functional family on the screw-assignment
space `α → ScrewSpace k`. Four new declarations in
`Molecular/RigidityMatrix.lean` (beside the basis-free hinge-row block):
`screwDiff u v` (the relative-screw evaluation `S ↦ S u − S v`, a
`LinearMap`), `hingeRow u v r := r ∘ₗ screwDiff u v` (one coordinatized
row of `R(G,p)`), `rigidityRows F` (the set of all such rows over links ×
hinge-row-block elements), and the load-bearing identity
`infinitesimalMotions_eq_dualCoannihilator : F.infinitesimalMotions =
(span ℝ F.rigidityRows).dualCoannihilator` (via
`Submodule.coe_dualCoannihilator_span` + `hingeConstraint_iff_hingeRowBlock`).
This is exactly the shape
`finrank_dualCoannihilator_along_affine_path_cofinite` consumes — the
remaining step is the affine path through panel-coordinate space (steps
(ii)/(iii); see *Hand-off*). Green, build+lint clean, axioms {propext,
Classical.choice, Quot.sound}. Folded into the existing
`def:rigidity-matrix` node's `\lean{...}` pin (forward-mode plumbing for
that node, not a new node); `lem:genericity-device` stays red.

**Analytic engine landed in both span (rank) and coannihilator
(codimension) form (2026-06-03).** The reuse-to-assess is resolved
(see *Decisions made* below): the device reuses the Phase-6/8 Gram-det
polynomial-root-set machinery, but at the *rank* level rather than the
full-rank (LI) level the Phase-8 lemmas stop at. Two bricks now sit in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` (upstream-eligible, beside
their LI-form sibling):
- `LinearIndependent.le_finrank_span_along_affine_path_cofinite` — the
  *rank* form: finrank of the span of an affine vector family is
  cofinitely bounded *below* by any rank witnessed once.
- `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  — the *codimension/null-space* dual: the common kernel (packaged as
  the `dualCoannihilator` of the span of an affine functional family)
  has finrank cofinitely bounded *above* by `finrank V − #s`, via the
  complementary-dimension identity `finrank coann + finrank span =
  finrank V` (`Subspace.finrank_dualCoannihilator_eq` +
  `Subspace.finrank_add_finrank_dualAnnihilator_eq` +
  `Subspace.dual_finrank_eq`). This is the exact shape the consumers
  carry (each is a `dim Z(G,p) ≤ …` upper bound on a null-space dim,
  the codimension reading of `rank R ≥ …`).
Both green, build warning-clean + lint clean, axioms {propext,
Classical.choice, Quot.sound}. The `lem:genericity-device` node stays
red (this is infrastructure, not yet the device's API); the analytic
engine is now complete in the consumer-facing shape — what remains is
the RigidityMatrix coordinatization that connects `infinitesimalMotions`
to a `dualCoannihilator` of a panel-parametrized functional family (see
*Hand-off*).

## Architectural choices made up front

- **Forward-mode, node beside the consumers.** A single
  `lem:genericity-device` node in `algebraic-induction.tex` (its own
  `sec:molecular-algebraic-induction-genericity` subsection, before
  Case III) that the four Phase-21 consumers `\uses`. If the device's
  Lean grows past a handful of lemmas, split it into its own
  `.lean` + `.tex` per the one-file-per-molecular-phase convention.
- **Discharge the consumers' explicit hypotheses.** Each Phase-21 node
  is GREEN-modulo-21b with the device's conclusion taken as a named
  hypothesis (`hglue`/`hspan`/`hub`/`hgen`). The device must produce
  exactly those: this fixes the device's *target statement* before its
  *proof strategy* — pin the API the consumers already expect.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`
(`sec:molecular-algebraic-induction-genericity`). Tracked here for
hand-off convenience.

- [x] `lem:genericity-device` — Claim 6.4/6.9, codimension form:
  `genericityDevice` (`Molecular/AlgebraicInduction.lean`). Along an affine
  functional family coordinatizing the null spaces, a witnessed corank
  bounds `dim Z(G,p_t) ≤ D|V| − #s` cofinitely. Green; thin composition of
  the two bricks below + `finrank_screwAssignment`. (The per-consumer wiring
  — presenting the *panel* rows as such an affine family despite their
  bilinear dependence on the normals — is the residual open piece; see
  *Hand-off*.)
- [x] `LinearIndependent.le_finrank_span_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — the rank-form analytic
  core: `finrank` of the span of an affine vector family is cofinitely
  bounded below by any rank witnessed once. Green; mirror lemma (no
  blueprint node).
- [x] `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — the codimension dual:
  the common kernel (`dualCoannihilator` of the span of an affine
  functional family) has `finrank` cofinitely bounded *above* by
  `finrank V − #s`. The consumer-facing shape (`dim ker ≤ value`).
  Green; mirror lemma (no blueprint node).
- [x] RigidityMatrix coordinatization (step (i),
  `Molecular/RigidityMatrix.lean`): `screwDiff`, `hingeRow`,
  `rigidityRows`, and `infinitesimalMotions_eq_dualCoannihilator`
  (`Z(G,p) = (span rigidityRows).dualCoannihilator`). Green; folded
  into the `def:rigidity-matrix` node's `\lean{...}` pin (no new node).

- [x] `exists_good_realization` + `hglue_of_genericityDevice`
  (`Molecular/AlgebraicInduction.lean`): the device's generic-point form
  (`∃ t, dim Z(F t) ≤ D|V| − #s`) and the Case-I block-triangular bridge
  (route (a): `hmatch` rank-match collapses it to `hglue`). Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (no new node).

- [x] `hcoord_of_rigidityRows_affine` (`Molecular/AlgebraicInduction.lean`):
  step-(i) bridge — discharges the device's `hcoord` from an affine functional
  family whose span equals `span (rigidityRows (F t))` at every `t` (`hspan`),
  via `infinitesimalMotions_eq_dualCoannihilator`. Reduces the per-consumer
  `hcoord` obligation to an *equality of spans*. Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (no new node).

- [x] `finrank_hingeRowBlock` (`Molecular/RigidityMatrix.lean`): per-edge row-count brick —
  `finrank ℝ (hingeRowBlock e) = screwDim k − 1` when `supportExtensor e ≠ 0` (transversal hinge),
  the basis-free `(D−1) × D` block-row count. The brick that counts the rigidity rows of a rigid
  block (source of the matching-size independent subfamily for Case-I `hindep`/`hmatch`). Green;
  folded into `def:hinge-row-block`'s `\lean{...}` pin (no new node).

- [x] `linearIndependent_hingeRow` (+ glue `screwDiff_surjective`, `hingeRow_eq_dualMap`)
  (`Molecular/RigidityMatrix.lean`): the Case-I `hindep` brick — for a genuine edge `u ≠ v`, an LI
  family of hinge-row-block functionals induces an LI family of rigidity rows `hingeRow u v (r i)`,
  via surjectivity of `screwDiff u v` + dual-map injectivity + `LinearIndependent.map'`. Turns
  independent supporting extensors of a rigid block (`exists_independent_panelSupportExtensor`,
  through the `(D−1)`-dim hinge-row block) into the independent rigidity-row subfamily
  `hglue_of_realization` needs. Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin (glue
  lemmas skipped per the blueprint skip-glue rule).

- [x] `exists_independent_rigidityRows_of_edge` (`Molecular/RigidityMatrix.lean`): per-edge
  independent-rows brick — a single transversal hinge `e = uv` (`u ≠ v`, `supportExtensor e ≠ 0`)
  yields `D − 1` LI rigidity rows in `F.rigidityRows`. Composes `finrank_hingeRowBlock` (count) +
  `linearIndependent_hingeRow` (lift) through the new mirror lemma
  `Submodule.exists_linearIndependent_fin_of_finrank_eq` (basis-coercion in abstract-field form,
  avoiding the `whnf` blow-up on the exterior-power dual). The per-edge unit of Case-I
  `hindep`/`hmatch`. Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin (mirror lemma
  skipped).

- [x] `linearIndependent_hingeRow_star` (`Molecular/RigidityMatrix.lean`): the cross-hinge `hindep`
  step — for a star of edges at a common body `v` with distinct other endpoints, per-hinge LI row
  families remain jointly LI, via the pin-a-body / disjoint-support count
  (`Fintype.sum_sigma` + `Finset.sum_eq_single` + `Fintype.linearIndependent_iff`). The substantive
  cross-hinge combination the hand-off flagged; `linearIndependent_hingeRow`'s single-edge argument
  does not extend (distinct `screwDiff`). Green; folded into `def:rigidity-matrix`'s `\lean{...}` pin
  (no new node).

- [x] `exists_finite_spanning_rigidityRows` (`Molecular/RigidityMatrix.lean`): input (2) of
  `hglue_of_realization` — a finite family `a : Fin n → Dual ℝ (α → ScrewSpace k)` with
  `span (range a) = span F.rigidityRows`, from finite-dimensionality of the dual (`α` finite ⇒
  screw-assignment space finite-dim ⇒ dual finite-dim ⇒ every submodule FG) via
  `Submodule.fg_iff_exists_fin_generating_family`. Green; folded into `def:rigidity-matrix`'s
  `\lean{...}` pin (no new node).

- [x] `hspan_const_of_span_eq` + `hcoord_const` + `hglue_of_realization`
  (`Molecular/AlgebraicInduction.lean`): the **route-(a) constant-path** discharge.
  `hcoord_const` gives the device's `hcoord` for the constant family `F t = F₀`
  (`b = 0`) from any finite family spanning `rigidityRows F₀`; `hglue_of_realization`
  composes it into `hglue_of_genericityDevice` to land Case I's `hglue` inequality at
  a single hand-built realization `F₀` (witness from
  `exists_independent_panelSupportExtensor`, no path construction). Green; folded into
  `lem:genericity-device`'s `\lean{...}` pin (`hcoord_const`, `hglue_of_realization`).

The consumer-side discharge targets (each currently a named hypothesis
in the Phase-21 Lean, to be supplied by the device):
- [~] `hglue` for Case I — block-triangular generic gluing
  (`finrank Z ≤ D + finrank (pinnedMotionsOn s)`). **Route-(a) capstone done**
  (`hglue_of_realization` via constant path `hcoord_const` /
  `hspan_const_of_span_eq`): the `hglue` inequality holds at a single hand-built
  realization `F₀`, all affine-path plumbing discharged. The finite spanning row family `a`
  (`hspanrows`) is now also discharged generically by `exists_finite_spanning_rigidityRows` for any
  `F₀`. The `hindep` *bridge* is now also in hand (`linearIndependent_hingeRow`): per genuine edge,
  independent extensors → independent rigidity rows. Residual is purely combinatorial-geometric —
  exhibit the realization `F₀` and the matching-size independent subfamily `s` from the contraction
  realization + rigid block (combine `linearIndependent_hingeRow` across the block's hinges for
  `hindep`, count via `finrank_hingeRowBlock` for `hmatch`); no path construction remains.
- [ ] `hspan` for Case II — each base-`v`-pinned motion lands in the two
  new edges' panel-support spans (false pointwise; holds by the
  rank/dimension count, via `exists_independent_panelSupportExtensor`).
- [ ] `hub`/`hgen` for Prop 1.1 — the generic-rank reconciliation
  (`hgen` = Thm 5.5 pushed through the device).
- [ ] the projective assembly of `lem:cycle-realization` (its four Lean
  pieces are green; only the cited CW82/Whiteley99 projective assembly
  is non-Lean).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Reuse-to-assess resolved: rank-form of the Phase-8 Gram-det
  machinery, not a fresh perturbation.** The cycle-genericity *existence*
  (independent supporting extensors) was already purely
  exterior-algebraic in Phase 21 (`exists_independent_panelSupportExtensor`,
  a basis choice on `⋀²`, no perturbation). What remains — the device's
  actual content — is *generic-max-rank attainment*: each consumer
  hypothesis (`hglue` rank-`≤`, `hspan` span-membership, `hub`/`hgen`)
  fails pointwise but holds at a generic point. That *is* the Phase-8
  polynomial-root-set mechanism (`finite_setOf_…_along_affine_path`),
  but the Phase-8 lemmas stop at the full-rank/LI case; the device needs
  the `finrank ≥ r` lower-bound case. So: **reuse the mechanism, lift it
  to rank form**. First brick:
  `LinearIndependent.le_finrank_span_along_affine_path_cofinite` — a
  maximal LI subfamily witnessing `finrank ≥ #s` at `t₀` stays LI
  cofinitely (the LI lemma on the subfamily) and an LI subfamily of size
  `#s` forces full-span `finrank ≥ #s`. Mirror-directory, upstream-
  eligible, beside its LI sibling; no blueprint node (mirror lemma).
- **Dualize the analytic engine once, into the consumer-facing
  codimension shape.** Every consumer hypothesis (`hglue`/`hgen`/`hub`)
  is an *upper* bound on a null-space dimension (`dim Z(G,p) ≤ …`), the
  codimension reading of `rank R ≥ …`, not a span lower bound. Rather
  than re-derive the rank-nullity flip at each consumer, the dual is
  taken once as a mirror lemma:
  `finrank_dualCoannihilator_along_affine_path_cofinite`. The kernel of
  an affine functional family is the `dualCoannihilator` of the span of
  the functionals (`Submodule.coe_dualCoannihilator_span`), and span +
  coann have complementary finrank at *every* `t`, so the span brick's
  "≥ #s cofinitely" becomes "coann ≤ finrank V − #s cofinitely"
  verbatim. Conclusion stated additively (`finrank V < #s + finrank
  coann`) to avoid `ℕ`-subtraction.
- **Coordinatize `R(G,p)` as a functional family, not a coordinate
  matrix.** Step (i): the rows are `hingeRow u v r = r ∘ₗ screwDiff u v`
  on `α → ScrewSpace k` (`screwDiff = proj u − proj v`), one per
  link × hinge-row-block element; `rigidityRows` is their set, and
  `infinitesimalMotions_eq_dualCoannihilator` reads `Z(G,p)` off as
  `(span rigidityRows).dualCoannihilator`. This keeps the screw space the
  graded-piece element (no `⋀^k ≅ ℝ^D` basis forced) and matches the
  coannihilator brick's shape exactly. Folded into `def:rigidity-matrix`
  (forward-mode plumbing for an existing node, not a new node), parallel
  to the two Rank.lean bricks being node-free mirror lemmas.
  Elaboration gotcha (`proj − proj` stuck): TACTICS-QUIRKS § 30.
- **The abstract device is `genericityDevice`: one lemma, `hcoord` carries
  the affine family.** Rather than wire the device inseparably into the
  first consumer, it lands as a standalone framework-facing lemma whose
  `hcoord` hypothesis *receives* the affine functional family
  `t ↦ a i + t • b i` coordinatizing each `(F t).infinitesimalMotions`.
  This fixes the device's target shape (the consumer-facing
  `dim Z ≤ D|V| − #s` cofinitely) before committing to a wiring shape, and
  isolates the genuinely-open piece (building the affine family from
  *panel* normals) as the consumer's obligation, not the device's. The
  device proof is then a 3-line composition of the two bricks +
  `finrank_screwAssignment`. Why this and not "wire Case I first": the
  panel rows are *bilinear* (degree-2) in the normals, so there is no
  single affine path to feed Case I's `hglue` without first choosing a
  restriction — the assessment the hand-off flagged. Landing the abstract
  device makes that assessment explicit and unblocks all four consumers
  uniformly once the affine-presentation route is chosen.

## Blockers / open questions

- **Reuse-to-assess: RESOLVED** (see *Decisions made*). The device
  reuses the Phase-8 Gram-det polynomial-root-set mechanism, lifted to
  rank form, in both the span and codimension shapes. Both bricks
  landed.
- **The abstract device + the full Case-I `hglue` route are landed.**
  `genericityDevice` (codimension form), the arithmetic wiring
  (`hglue_of_genericityDevice` + `exists_good_realization`), and now the
  **route-(a) constant-path capstone** (`hglue_of_realization` via
  `hcoord_const` / `hspan_const_of_span_eq`) are all green. **The route a/b
  decision is RESOLVED: route (a) with a degenerate constant path.** The
  bilinearity caveat (a generic line through normal-space gives a quadratic row
  family) is *sidestepped, not solved* — because Case I's witness realization is
  constructed directly by `exists_independent_panelSupportExtensor` (a `⋀²` basis
  choice, not perturbation), no real line is traversed, so the device runs on the
  constant path `F t = F₀` (`b = 0`) and reads off the corank at the one
  hand-built realization. Route (b) (multivariate Zariski-open generalization)
  is no longer needed for Case I; it may still be the cleaner option if a future
  consumer genuinely requires a non-constant path.
- **The single open piece for Case I is now purely combinatorial-geometric**:
  supplying `hglue_of_realization`'s inputs — the single realization `F₀`, a
  *finite* family `a` spanning `rigidityRows F₀`, and an independent subfamily `s`
  of the matching size `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` +
  `hmatch`) — from the contraction realization plus the rigidly-placed block
  `V(H)`. No affine-path construction remains.

## Hand-off / next phase

**The abstract device `lem:genericity-device` (`genericityDevice`) is now
GREEN** (see *Current state*): all three of the device's reusable pieces
land — the rank-form engine + its codimension dual (`Rank.lean` bricks),
the coannihilator coordinatization (`infinitesimalMotions_eq_dualCoannihilator`),
and now their composition into the consumer-facing `dim Z(F t) ≤ D|V| − #s`
cofinite bound, with the affine functional family carried as the `hcoord`
hypothesis. What remains is the **per-consumer wiring**, now isolated as a
single well-understood obligation (see *Blockers*): build, for each consumer,
an affine functional family `a i + t • b i` discharging `hcoord` for that
consumer's framework, then apply `genericityDevice` and pick a good `t` off
the finite bad set.

**Earlier-2026-06-03 milestones (superseded by the route-(a) resolution below):** the device's
arithmetic wiring (`hglue_of_genericityDevice` + `exists_good_realization`, isolating `hmatch`),
the `dualCoannihilator` plumbing discharge (`hcoord_of_rigidityRows_affine`, reducing `hcoord` to
an equality of spans), and the then-open route a/b question (bilinear panel rows ⇒ quadratic along
a line). All folded into the resolution below.

**Route-(a) decision RESOLVED + Case-I `hglue` capstone landed (2026-06-03).** The affine-path
question is closed: route (a) with a *constant* path (`hcoord_const` / `hspan_const_of_span_eq` /
`hglue_of_realization`). The bilinearity obstruction is sidestepped because Case I's witness
realization is hand-built by `exists_independent_panelSupportExtensor`, so no real line through
normal-space is traversed — the device reads off the corank at the one realization. See *Current
state* and *Blockers*.

**Input (2) — the finite spanning row family `a` — is now landed generically**
(`exists_finite_spanning_rigidityRows`, see *Current state*): for *any* realization `F₀` it supplies
a finite `a : Fin n → Dual ℝ (α → ScrewSpace k)` with `span (range a) = span (rigidityRows F₀)`, so
no per-consumer construction of `a`/`hspanrows` is needed anymore.

**Per-edge row-count brick landed (2026-06-03):** `finrank_hingeRowBlock` (`finrank (hingeRowBlock
e) = D − 1` for a transversal hinge) — the first piece of the row-counting needed for Case-I's
`hindep`/`hmatch`. See *Current state*.

**Smallest next concrete commit: supply `hglue_of_realization`'s *remaining* inputs for Case I (the
geometric construction).** From the contraction realization (`G/E(H)` at its inductive
`RankHypothesis`) plus the rigid block `V(H)` placed rigidly, exhibit:
1. the single realization `F₀` (a `BodyHingeFramework`/`PanelHingeFramework`-via-`toBodyHinge`), and
2. an independent subfamily `s` of the finite spanning family `a` (from
   `exists_finite_spanning_rigidityRows`) with `#s = D(|V|−1) − dim Z_s` (`hindep` + `hmatch`), the
   independent rigidity rows coming from `exists_independent_panelSupportExtensor` through the
   hinge-row block — each transversal hinge contributing `D − 1` rows (`finrank_hingeRowBlock`, now
   green).
No affine-path construction and no finite-spanning-family construction remain. This is the
genuinely-geometric Case-I assembly (KT §6.2/6.5); likely more than one commit — assess once `F₀` is
in hand and `s` is being matched to the corank. The per-edge and cross-hinge sub-bricks toward (2)
are now landed: `linearIndependent_hingeRow` (independent supporting extensors → independent
`hingeRow u v r` per edge), `exists_independent_rigidityRows_of_edge` (one transversal hinge ⇒
`D − 1` LI rigidity rows in `rigidityRows`), and now `linearIndependent_hingeRow_star` (the
cross-hinge combination: rows from *distinct* hinges at a common pinned body, distinct other
endpoints, are jointly LI by the pin-a-body / disjoint-support count). **Next sub-brick: extend the
star combination to a rigid block whose hinges span *multiple* bodies** — the star handles edges
sharing one endpoint `v`; the genuine rigid block is a cycle/spanning-tree where the
`m ≤ D` extensor-independence of `lem:cycle-realization` + `exists_independent_panelSupportExtensor`
general position controls the cross-body interaction (`eq_zero_of_mem_span_singleton_of_sum_eq_zero`
is the existing screw-space telescoping core). Then match `#s = D(|V|−1) − dim Z_s` (`hmatch`) using
the `D−1` per-edge count against the contraction's inductive rank, and exhibit `F₀`. The other
consumers (`hspan` for Case II, `hgen` for Prop 1.1) reuse the same constant-path chain
(`hcoord_const` → device) with an analogous per-consumer bridge; the device's *target statements*
are fixed (the named hypotheses in `AlgebraicInduction.lean`).

**Also consumed by Phases 22–23** (Case III candidate-framework
genericity, Claims 6.11/6.12), so building the device standalone pays
forward; for Case III's share it bottoms on Lemma 2.1 (Phase 17 green).
