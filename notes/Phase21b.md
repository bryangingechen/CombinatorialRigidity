# Phase 21b — Genericity device + realization-layer re-plan (work log)

**Status:** in progress (opened 2026-06-03; realization layer re-planned 2026-06-04).

Sub-phase scoped out of Phase 21 on 2026-06-03 (user decision, risk #4/#7),
the **analytic sibling** of the Phase-21a meet sub-phase. Two things live here
now: (1) the genuinely-new analytic crux of Katoh–Tanigawa's algebraic
induction — Claim 6.4/6.9, the **genericity device** (rigidity-matrix entries
are polynomials in the panel coordinates, so a single good realization lifts to
a generic one) — which is **GREEN**; and (2) the **realization layer** of
Theorem 5.5 (the producers exhibiting a rigid panel framework for each
inductive case), which a 2026-06-04 spike found was built on a **mis-defined
motive** and is being **re-planned** around the corrected one.

Program-level plan, reuse map, citations: `notes/MolecularConjecture.md`
*Phase 21b*. Scope-out rationale + node-by-node consumer split: `DESIGN.md`
*Genericity device …* + *Forward-mode reduction chains* + *Realization motive
must be V(G)-relative …*. Forward-mode dep-graph:
`blueprint/src/chapter/algebraic-induction.tex`
(`sec:molecular-algebraic-induction`). Lean is in
`CombinatorialRigidity/Molecular/AlgebraicInduction.lean` + mirror bricks under
`CombinatorialRigidity/Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`.

## Current state

**The device is GREEN; the realization layer is RED and re-planned (2026-06-04).**
Two spike findings (both verified in Lean) reshaped the plan:

1. **The realization motive was unsatisfiable for the inductive graphs.**
   `HasFullRankRealization k G` unfolds to `RankHypothesis 0`, the *absolute*
   null-space equality `dim Z(G,p) = D` over **all** of `α → ScrewSpace`. That
   equals infinitesimal rigidity only when `G` **spans** `α` — a body in
   `α ∖ V(G)` carries no hinge constraint, hence is a free non-trivial motion
   (verified: a 1-line lemma, an isolated body gives a non-trivial motion). But
   `minimal_kdof_reduction` (the recursion `theorem_55` runs on) reduces to
   graphs with **strictly fewer vertices on the same fixed `α`**, which do not
   span it. So `theorem_55`'s premises `hbase`/`hsplit`/`hcontract` are
   unsatisfiable for `card α ≥ 3` (concrete counterexample: the double edge on
   `{u,v}` inside a 3-body `α` is minimal-0-dof with `|V| = 2` but has no rigid
   realization). `theorem_55` is green only as a conditional over unsatisfiable
   hypotheses. `theorem_55_base`'s `hcover : ∀ w, w = u ∨ w = v` ("`α = {u,v}`")
   is the exposed symptom.

   **Fix (user decision, rank-form):** carry the realization motive in the
   **`V(G)`-relative rank form** `rank R(G,p) = D(|V(G)|−1)` — equivalently
   `finrank (span rigidityRows) = D·(V(G).ncard − 1)`, equivalently "every
   infinitesimal motion is constant on `V(G)`". This is **`α`-independent**
   (isolated bodies contribute no rigidity rows / `rank = D·card α − dim Z`),
   composes through the induction, and **resurrects the block-constancy
   machinery** (which was vacuous only because of the global-`α` rigidity).

2. **The Case-I closure carrier targeted unsatisfiable hypotheses.** The retired
   `hasFullRankRealization_ofParam_of_contraction` /
   `isInfinitesimallyRigid_of_rigid_subgraph_of_block_internal` took as
   hypotheses that two subgraphs `G_H, G_c ≤ G` are *each* infinitesimally rigid
   **over the whole `α`** — false for a proper `H` (same isolated-body argument).
   Under the relativized motive the legs ("`H` realizes its rank", "`G/E(H)`
   realizes its rank") are the **satisfiable** inductive hypotheses, and the
   producer is a **device-direct** composition (B0 + splice-seed + device), not a
   closure over unsatisfiable rigidity inputs.

The device itself (`exists_good_realization` + `exists_good_realization_const`,
on the route-(a) `exists_…_polynomial` engine) is unchanged and green; it is
*motive-independent* (a generic-rank statement). The **B0 keystone** —
coordinatizing the `ofParam`/panel-normal rows as `MvPolynomial` so the device
can be *applied* to a varying realization — was spiked and is feasible/clean:
mathlib's `exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti` +
`Matrix.det_fin_two` give a `⋀²` coordinate of `normalsJoin n₁ n₂` as the
bilinear minor `n₁ᵢn₂ⱼ − n₁ⱼn₂ᵢ` (verified to compile); `complementIso` is a
fixed `LinearEquiv` (stays degree-2); the annihilator spanning family
`{Cᵢeⱼ* − Cⱼeᵢ*}` is linear in `C`.

## Architectural choices made up front

- **Forward-mode, nodes beside the consumers** (unchanged). The realization
  spine + device live in `algebraic-induction.tex`'s
  `sec:molecular-algebraic-induction`.
- **The motive is `V(G)`-relative (rank form).** `def:rank-hypothesis` carries
  `rank R(G,p) = D(|V(G)|−1) − k'`. Recommended Lean carrier: an
  `IsInfinitesimallyRigidOn (s : Set α)` predicate ("motions constant on `s`")
  with `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.toBodyHinge.
  IsInfinitesimallyRigidOn V(G)`; the rank-equality form is the bridge. This
  reuses the block-constancy bricks (resurrected) and `theorem_55_base`'s `key`.
- **Realization is device-direct on the full parent**, not via the (vacuous)
  `withGraph`-subgraph-rigid carrier. The device proves the *full parent* rigid
  (it spans `α`); the per-leg work is the genericity-free splice seed.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`. Tracked
here for hand-off. All `[x]` Lean bricks are axiom-clean {propext,
Classical.choice, Quot.sound}.

**GREEN and motive-independent (retained verbatim):**
- [x] `lem:genericity-device` — `exists_good_realization{,_const}` on the
  multivariate engine `exists_finrank_dualCoannihilator_polynomial` (route (a),
  four mirror bricks: `MvPolynomial.exists_eval_ne_zero`,
  `Matrix.exists_linearIndependent_rows_specialize`,
  `exists_le_finrank_span_polynomial`,
  `exists_finrank_dualCoannihilator_polynomial`).
- [x] Panel layer `def:panel-support-extensor`, `def:panel-hinge-framework`
  (+ `IsGeneralPosition`, moment-curve `withMomentNormals`/`ofParam`).
- [x] All four Lean pieces of `lem:cycle-realization` (base, dim-bound,
  panel-independence reduction, existence) + `lem:cycle-realization-rigid`.
- [x] `R(G,p)` coordinatization: `infinitesimalMotions_eq_dualCoannihilator`,
  `rigidityRows`/`hingeRow`/`screwDiff`, `exists_independent_rigidityRows_of_forest`,
  `exists_finite_spanning_rigidityRows`, `finrank_screwAssignment`.
- [x] `def:framework-with-graph`, `lem:motions-mono-of-graph-le`,
  `def:pinned-motions-on`, `lem:pinned-motions-on-mono`,
  `lem:pinned-motions-on-rank-bound` (the genericity-free block-pin lower bound
  + `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`, the
  block-triangular glue — genuine, reusable under the relativized motive).
- [x] `Graph.endsOf`, `pinnedMotionsOn_withGraph_eq_of_block_internal` (genuine,
  no rigidity hypothesis), the Case-II `withNormal`/`hnew`/edge-substitution
  graph bricks (`lem:case-II-rank-lift`, `lem:splitoff-edge-substitution`).

**RED — realization spine, re-stated against the relativized motive (`\lean` kept
where the name will be re-pinned, `\leanok` dropped):**
- [ ] `def:rank-hypothesis` — re-pin to the `V(G)`-relative rank form.
- [ ] `lem:theorem-55-base` — re-prove the 2-vertex base relative (drop `hcover`).
- [ ] `thm:theorem-55` — re-run the recursion against the relativized motive.
- [ ] `lem:case-I`, `lem:case-II` — accounting iffs, re-stated rank-side.
- [ ] `prop:rigidity-matrix-prop11` — depends on the re-stated `theorem_55`.

**RED — realization producers (no `\lean` yet; the genuine build):**
- [ ] `lem:rows-polynomial-in-normals` (**B0, keystone**) — coordinatize the
  panel-normal rows as degree-2 `MvPolynomial`, packaging the device's
  `g`/`c`/`φ`/`hg` (`hcoord` = green `infinitesimalMotions_eq_dualCoannihilator`).
- [ ] `lem:case-I-splice-seed` — one placement `p₀` with `D(|V(G)|−1)`
  independent parent rows, block-triangular from the two IH legs
  (genericity-free).
- [ ] `lem:case-I-realization` — compose B0 + splice-seed + device ⇒
  `HasFullRankRealization`.
- [ ] `lem:case-II-realization` — the shallower 1-extension producer (one
  re-inserted body, `+(D−1)` rows, KT 6.12).
- [ ] `lem:case-III` — deferred to Phases 22–23.

**TO RETIRE (vacuous Lean, now blueprint-unreferenced):**
`hasFullRankRealization_ofParam_of_contraction`,
`isInfinitesimallyRigid_of_rigid_subgraph_of_block_internal`,
`isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph` (takes
`withGraph`-rigid, vacuous; the relativized analogue takes `IsInfinitesimallyRigidOn`),
`pinnedMotionsOn_eq_bot_of_block_internal_rigid` (takes `G_c` rigid, vacuous;
`hpin` should come from the *contraction* `G/E(H)` rigid, not `G − E(H)`),
`isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot`,
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid` /
`hasFullRankRealization_ofParam_of_pinnedMotionsOn` /
`hasFullRankRealization_of_pinnedMotionsOn` (absolute-motive producers).
Delete (or relativize) as their replacements land — do **not** leave them as
green decoys.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The realization motive must be `V(G)`-relative.** The absolute null-space
  form `dim Z = D` is α-dependent and unsatisfiable for non-spanning inductive
  subgraphs. Carry the rank form `rank R = D(|V(G)|−1)`. → `DESIGN.md`
  *Realization motive must be V(G)-relative*.
- **Producer hypotheses must be satisfiable, not just type-correct.** The
  retired Case-I carrier and the absolute base case smuggled unsatisfiable
  rigidity/coverage hypotheses; they typecheck and even prove (vacuously) but
  can never be discharged. → blueprint honesty gate (producer scrutiny).
- **B0 coordinate bilinearity is mathlib-supported** (no new hard mirror):
  `exteriorPower.basis_repr_apply` + `ιMultiDual_apply_ιMulti` +
  `Matrix.det_fin_two`. The device parameter is the panel **normals**
  (`σ = α × Fin(k+2)` or moment-param `α`), entries degree-2.
- **The Case-I splice seed is genericity-free.** Block-triangular row
  independence (KT 6.3 + pin-a-body Lemma 5.1 column split) from the two IH
  legs; genericity (the device) only lifts `p₀` to a generic point afterward.
- **Coordinatize `R(G,p)` as a functional family** (carried forward): rows are
  `hingeRow u v r`; `Z = (span rigidityRows).dualCoannihilator`. QUIRKS §30/§32/§33.

### Promoted
- *Forward-mode + linear reduction chain → single-use wrapper sprawl; build the
  keystone first.* → `DESIGN.md` *Forward-mode reduction chains*.
- *A `\leanok`/producer node may not carry a load-bearing hypothesis no node
  discharges — and the hypothesis must be **satisfiable**, not merely
  type-correct.* → `blueprint/CLAUDE.md` *the honesty gate* + *producer scrutiny*.
- *An absolute (ambient-type) rigidity/rank motive over a fixed body type is
  unsatisfiable for non-spanning subgraphs; realization motives in a
  vertex-reducing induction must be carried relative to `V(G)`.* → `DESIGN.md`
  *Realization motive must be V(G)-relative*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive.* →
  TACTICS-QUIRKS § 33.

## Blockers / open questions

- **Motive relativization is the gating commit.** Nothing downstream
  (producers) composes until the realization motive is `V(G)`-relative. Hand-off
  item 1.
- **Accounting iffs (`lem:case-I`/`lem:case-II`) are nullity-side, α-dependent.**
  They are true relative statements but do not directly serve the non-spanning
  producers; re-state rank-side (or bridge) as the producers need them. Assess
  on contact whether to re-state or keep + bridge.
- **`prop:rigidity-matrix-prop11`'s `hub`** (genericity-free upper bound, the
  Phase-19-partition count `D + def ≤ dim Z`) is still an untracked obligation
  carried as a hypothesis. Independent of the motive fix.
- **Case III** (`lem:case-III`) deferred to Phases 22–23.

## Hand-off / next phase

**For the `coordinate-phase` orchestrator:** the items below are an ordered
single-commit sequence; do them top to bottom, re-reading this section after
each commit (the building subagent updates it). Each commit lands Lean + flips
its blueprint node's `\leanok` (or adds green infra) + updates this file. The
device is green and `B0`'s coordinate core is validated, so this is build work,
not research. **Do not** re-introduce the retired vacuous lemmas.

1. **Relativize the realization motive + base case** (flips `def:rank-hypothesis`,
   `lem:theorem-55-base`, `thm:theorem-55`). Introduce
   `BodyHingeFramework.IsInfinitesimallyRigidOn (s : Set α) := ∀ S,
   IsInfinitesimalMotion S → ∀ u ∈ s, ∀ v ∈ s, S u = S v`; re-pin
   `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.toBodyHinge.
   IsInfinitesimallyRigidOn V(G)` (rank-equality bridge:
   `IsInfinitesimallyRigidOn V(G) ↔ finrank (span rigidityRows) = D·(V(G).ncard−1)`).
   Re-prove `theorem_55_base` relative — its existing `key : S u = S v` already
   gives constancy on `V(G) = {u,v}`; **drop the `hcover` hypothesis**. Re-run
   `theorem_55` (the recursion `exact minimal_kdof_reduction …` is
   motive-agnostic; only the case-premise *shapes* change). Keep the nullity
   `RankHypothesis` for the accounting iffs for now. *This is the gating commit;
   it may be bounded further (e.g. predicate + base in one commit, recursion in
   the next) at the builder's discretion.*

2. **Re-state the Case-I / Case-II accounting** (`lem:case-I`, `lem:case-II`)
   against the relativized motive — rank-side block-triangular addition (KT 6.3
   for Case I, the `+(D−1)` column-op count for Case II), reusing the
   genericity-free block-pin lower bound and the device's reverse bound. Assess
   whether to re-state or keep-and-bridge the existing nullity iffs.

3. **B0 — `lem:rows-polynomial-in-normals`** (the keystone; likely 2–4 commits,
   builder decomposes). Build the device inputs for the panel-normal family:
   `g` = the rigidity-row functionals, `c` = their degree-2 `MvPolynomial`
   coordinates (via the validated `normalsJoin` minor + `complementIso` linear +
   the `{Cᵢeⱼ*−Cⱼeᵢ*}` annihilator family), `φ` = a basis coordinate iso,
   `hg` = the eval identity, `hcoord` = green
   `infinitesimalMotions_eq_dualCoannihilator`. First sub-commit: lift the
   validated `⋀²`-coordinate bilinearity to a `supportExtensor`-coordinate-as-
   `MvPolynomial` lemma. Seed point `p₀` = moment-curve normals (reuse
   `isGeneralPosition_ofParam` + `exists_independent_rigidityRows_of_forest`).

4. **`lem:case-I-splice-seed`** — construct `p₀` on `G` with `D(|V(G)|−1)`
   independent parent rows: transport the IH realizations of `H` and `G/E(H)`
   onto `G` and certify block-triangular row independence (genericity-free, via
   pin-a-body Lemma 5.1's column split). The genuine geometric content of Case I.

5. **`lem:case-I-realization`** — compose B0 + splice-seed + device ⇒
   `HasFullRankRealization k G`. Discharges `theorem_55`'s `hcontract`.

6. **`lem:case-II-realization`** — the shallower 1-extension producer: re-insert
   the degree-2 body `v` with a general-position panel normal (KT 6.12), `+(D−1)`
   rows; discharges `hsplit`. Parallel to 4–5 but single-body.

7. **`prop:rigidity-matrix-prop11`** — re-close against the re-stated
   `theorem_55`; brick `hub` (Phase-19 partition count) — independent, may be
   done any time.

**Process lessons (don't repeat).** (a) Build the keystone / validate the
target shape *before* growing a reduction chain (`DESIGN.md` *Forward-mode
reduction chains*). (b) A producer hypothesis must be **satisfiable**, not just
type-correct — check it against a concrete small instance (the retired Case-I
carrier and the absolute base case both failed this). (c) For a vertex-reducing
induction, the realization motive must be carried relative to `V(G)`, not
absolute over the ambient body type.

**Session note.** `origin/master` was inadvertently pushed once an earlier
session; commits since are local. Match author `bryangingechen@gmail.com`; do
**not** push without asking.
