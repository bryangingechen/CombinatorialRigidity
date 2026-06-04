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
Lean is in `CombinatorialRigidity/Molecular/AlgebraicInduction.lean`
(beside the consumers) + mirror bricks under
`CombinatorialRigidity/Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`.

## Current state

**The multivariate genericity device is GREEN (2026-06-04). The realization layer
is honestly RED (blueprint-honesty audit, 2026-06-04).** `lem:genericity-device` is
rebuilt on the genuine multivariate engine and re-pinned green; the *accounting*
consumers (`lem:case-I`, `lem:case-II`, `thm:theorem-55`,
`prop:rigidity-matrix-prop11`) take the device's genericity inputs as explicit
hypotheses and are green for what they state (iffs / equality-assemblies).

**Audit correction (this commit).** The earlier hand-off claimed
`lem:case-I-realization` was green and "the one remaining red node is Case III" —
this was the premature-green anti-pattern. The Lean carrier
`hasFullRankRealization_ofParam_of_contraction` takes the *two splice rigidity
outputs* (`hHrig`: block subgraph `G_H ≤ G` rigid; `hcrig`: block-internal
contraction subgraph `G_c ≤ G` rigid) on the **same** `ofParam G ends param` witness
`p` as hypotheses. No Lean lemma constructs such a `p`, and the now-green device does
*not* build it (it only lifts an attained rank to a generic point). So
`lem:case-I-realization` is now **red** (`\leanok` dropped; `\lean{...}` kept — the
closure carrier resolves), depending on a new red node
`lem:case-I-splice-placement` (∃ `p` on which both subgraphs are rigid). A
**parallel hole was found in Case II**: there is an accounting iff
(`rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`) but **no
`HasFullRankRealization` producer** discharging the `hsplit` premise of `theorem_55`
— all four producers in the file are Case-I-shaped. A new red node
`lem:case-II-realization` (construct the re-inserted body's panel normal making
`hspan` hold, then land full rank) now tracks it. `prop:rigidity-matrix-prop11`'s
`hub` (genericity-free upper bound) is also a still-untracked Phase-19-partition
obligation — left as an explicit hypothesis, but the device-section prose now states
the device underwrites only the `hgen` half, not `hub`.

The genuine remaining red work on the chapter is therefore: the Case-I splice
placement, the Case-II 1-extension realization, and the deferred Case III
(`lem:case-III`, Phases 22–23) — **not** just Case III.

The device is `exists_good_realization` (multivariate keystone) +
`exists_good_realization_const` (constant-family closure the Case-I chain consumes)
in `AlgebraicInduction.lean`, both axiom-clean. They compose the multivariate
engine `exists_finrank_dualCoannihilator_polynomial` (route (a), landed `86f1221`)
with the coannihilator coordinatization `infinitesimalMotions_eq_dualCoannihilator`
and `finrank_screwAssignment` (`finrank (α → ScrewSpace k) = D|V|`). The device's
`hcoord` expresses `(F p).infinitesimalMotions` as the coannihilator of a
polynomial-coordinate functional family `g p` (panel coordinates `p : σ → ℝ` the
`MvPolynomial` vars, degree-2 rigidity entries the coefficients `c`); the conclusion
is `∃ p, #s + dim Z(F p) ≤ D|V|`.

**Wrapper chain consolidated (partial, Hand-off 2 mostly done this commit).** The
affine-special-case device + bridges (`genericityDevice`,
`hcoord_of_rigidityRows_affine`, `hspan_const_of_span_eq`, `hcoord_const`, the
affine `exists_good_realization`, the intermediate `hglue_of_genericityDevice`)
are *removed*: the constant-family path is now packaged once in
`exists_good_realization_const`, and `hglue_of_realization` folds in the old
`hglue_of_genericityDevice` arithmetic directly. The surviving Case-I chain is
`exists_good_realization{,_const}` → `hglue_of_realization` →
`hglue_of_independent_rigidityRows` → `hglue_of_forest` (each a genuine reduction,
no longer single-use affine plumbing).

**Route (a) analytic core (commit `86f1221`, unchanged)** — four upstream-eligible
mirror bricks (axiom-clean): `MvPolynomial.exists_eval_ne_zero`
(`…/MvPolynomial/Funext.lean`), and in `…/Matrix/Rank.lean`:
`Matrix.exists_linearIndependent_rows_specialize`,
`exists_le_finrank_span_polynomial`, `exists_finrank_dualCoannihilator_polynomial`.

The full inventory of landed green bricks — the `R(G,p)` coannihilator
coordinatization, the rigid-block forest linear-algebra, general position /
moment-curve / `ofParam`, the realization-motive producers, the
block-pin↔rigidity bridges, the `endsOf` graph selector — is in the
*Lemma checklist*.

## Architectural choices made up front

- **Forward-mode, node beside the consumers.** A single `lem:genericity-device`
  node (its own `sec:molecular-algebraic-induction-genericity` subsection) that
  the Phase-21 consumers `\uses`. The Lean has grown into new mirror files; if
  it grows further, split into its own `.lean`/`.tex`.
- **Discharge the consumers' explicit hypotheses.** Each Phase-21 node is
  GREEN-modulo-21b with the device's conclusion taken as a named hypothesis
  (`hglue`/`hspan`/`hub`/`hgen`). The device must produce exactly those — this
  fixes the device's *target statement* (the consumer API) before its proof.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`
(`sec:molecular-algebraic-induction-genericity`); tracked here for hand-off.
All `[x]` bricks are axiom-clean {propext, Classical.choice, Quot.sound}.

**Blueprint nodes:**
- [x] `lem:genericity-device` — **GREEN**. Genuine multivariate Claim 6.4, pinned to
  `exists_good_realization` + `exists_good_realization_const`.
- [x] `lem:case-I` — the accounting iff (green; device dep green). Takes `hglue`.
- [x] `lem:case-II` — the accounting iff (green; device dep green). Takes `hspan`.
- [ ] `lem:case-I-realization` — **RED** (`\leanok` dropped this commit). The
  `HasFullRankRealization`-closure-under-contraction *carrier*
  (`hasFullRankRealization_ofParam_of_contraction` +
  `isInfinitesimallyRigid_of_rigid_subgraph_of_block_internal`) is proven, but it
  consumes the splice placement as two rigidity hypotheses, so the node depends on:
- [ ] `lem:case-I-splice-placement` — **RED, new node** (no `\lean`). ∃ a single `p`
  (KT 6.2/6.6) on which both the rigid block `G_H` and the block-internal contraction
  `G_c` are infinitesimally rigid. The genuine Case-I geometric construction; 5-brick
  decomposition (B1–B5) in *Hand-off* item 1 — only B5 flips this node + `lem:case-I-realization`.
- [ ] `lem:case-II-realization` — **RED, new node** (no `\lean`). The
  `HasFullRankRealization` *producer* for the 1-extension, discharging `theorem_55`'s
  `hsplit`. Construct the re-inserted body's general-position panel normal making
  `hspan` hold; no such producer exists in Lean yet (only the accounting iff).

**Analytic core — multivariate (genuine Claim 6.4, route (a)):**
- [x] `MvPolynomial.exists_eval_ne_zero` (`…/MvPolynomial/Funext.lean`) — nonzero
  `MvPolynomial σ ℝ` ⇒ non-vanishing point (contrapositive of `MvPolynomial.funext`).
- [x] `Matrix.exists_linearIndependent_rows_specialize` — polynomial-entry matrix:
  LI rows at `p₀` ⇒ `∃ p`, LI rows (bad set = zero locus of Gram-det poly).
- [x] `exists_le_finrank_span_polynomial` — vector rank-`#s` `∃`-form, abstract `W`.
- [x] `exists_finrank_dualCoannihilator_polynomial` — codimension dual,
  `∃ p, #s + dim coann ≤ finrank V`; **the engine the device is built on.**

**Analytic core — affine/univariate (special case, no longer used by the device):**
- [x] `…le_finrank_span_along_affine_path_cofinite` / `…finrank_dualCoannihilator_along_affine_path_cofinite`
  (`…/Matrix/Rank.lean`) — `{bad t}.Finite` form; the univariate predecessor, kept
  as a mirror but no longer consumed (the device is multivariate).

**Device + Case-I chain (`AlgebraicInduction.lean`) — multivariate (consolidated):**
- [x] `exists_good_realization` (multivariate keystone), `exists_good_realization_const`
  (constant-family closure), `hglue_of_realization` (folds the old affine
  `hglue_of_genericityDevice` arithmetic), `hglue_of_independent_rigidityRows`,
  `hglue_of_forest`. The affine device + bridges (`genericityDevice`,
  `hcoord_of_rigidityRows_affine`, `hspan_const_of_span_eq`, `hcoord_const`,
  `hglue_of_genericityDevice`) were removed.

**`R(G,p)` coordinatization & rigid-block rows (`RigidityMatrix.lean`):**
- [x] `screwDiff`/`hingeRow`/`rigidityRows` + `infinitesimalMotions_eq_dualCoannihilator`
  — `Z(G,p) = (span rigidityRows).dualCoannihilator`.
- [x] `finrank_hingeRowBlock` (per-edge count `D−1`), `linearIndependent_hingeRow`,
  `exists_independent_rigidityRows_of_edge`, `linearIndependent_hingeRow_star`,
  `linearIndependent_hingeRow_forest`, `exists_independent_rigidityRows_of_forest`
  (assembled `|J|·(D−1)` LI rows), `exists_finite_spanning_rigidityRows`.

**Graph-side / geometric (`Induction.lean`, `AlgebraicInduction.lean`):**
- [x] `Graph.endsOf` (+ `isLink_endsOf`, `endsOf_eq_or_swap`) — canonical endpoint
  selector `ofParam` consumes (reusable; replaces inline `exists_isLink_of_mem_edgeSet`).
- [x] `IsGeneralPosition` + `supportExtensor_ne_zero_of_isGeneralPosition`;
  `momentCurve` + `withMomentNormals` + `isGeneralPosition_withMomentNormals`
  (dimension-free general position at an injective `param`);
  `ofParam` + `isGeneralPosition_ofParam` (from-scratch constructor).
- [x] `…_iff_pinnedMotionsOn_of_generalPosition`, `ofParam_rankHypothesis_iff_pinnedMotionsOn`
  — Case-I iff with purely-combinatorial signature `(G, ends)` + forest data + `hmatch`.

**Realization-motive producers + bridges (`AlgebraicInduction.lean`):**
- [x] `hasFullRankRealization_ofParam_of_pinnedMotionsOn` (`hpin`+`hmatch` form),
  `…_of_isInfinitesimallyRigid` (rigidity form), `hasFullRankRealization_of_pinnedMotionsOn`
  (internalizes injective `param` via mirror `Countable.exists_injective_real`).
- [x] `pinnedMotionsOn_eq_bot_of_isInfinitesimallyRigid` (+ `finrank_…`) — `hpin`
  from rigidity; `isInfinitesimallyRigid_of_le_withGraph` (graph-side leg);
  `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` (rigidity-producing
  converse); `isConstantOnBlock_of_isInfinitesimalMotion_of_rigid_subgraph`
  (`hblock` brick) + `isInfinitesimallyRigid_of_rigid_subgraph_of_pinnedMotionsOn_eq_bot`;
  `pinnedMotionsOn_withGraph_eq_of_block_internal` + `…_eq_bot_of_block_internal_rigid`
  (`hpin` from contraction rigidity).

**Consumer discharge targets (named hypotheses, supplied by the device):**
- [~] `hglue` (Case I) — all non-geometric inputs discharged; residual is the
  splice (Hand-off 3), bottoming on the multivariate device.
- [ ] `hspan` (Case II), `hub`/`hgen` (Prop 1.1) — reuse the device with a
  per-consumer bridge; target statements fixed in the Lean.
- [ ] projective assembly of `lem:cycle-realization` (four Lean pieces green;
  only the cited CW82/Whiteley99 projective assembly is non-Lean).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Coordinatize `R(G,p)` as a functional family, not a coordinate matrix.**
  Rows are `hingeRow u v r = r ∘ₗ screwDiff u v`; `Z(G,p) =
  (span rigidityRows).dualCoannihilator`. Keeps the screw space the graded-piece
  element (no `⋀^k ≅ ℝ^D` basis forced). Elaboration gotcha (`proj − proj`
  stuck): TACTICS-QUIRKS § 30. `ext`-on-`Module.Dual`: TACTICS-QUIRKS § 32.
- **Dualize the analytic engine once into the codimension shape.** Every consumer
  hypothesis is an upper bound `dim Z ≤ …` (codimension reading of `rank R ≥ …`).
  Taken once as the `…dualCoannihilator…` lemmas, stated additively to avoid
  `ℕ`-subtraction.
- **The device's *target statement* (consumer API) is fixed before its proof.**
  The device lands with `hcoord` *receiving* the functional family — this pinned
  the consumer-facing shape early, validated against the consumer API before the
  multivariate proof was wired in.
- **The constant family IS a valid multivariate family.** Route (a)'s "no real
  line is traversed" reading survives the multivariate rebuild: a single hand-built
  realization `F₀` is the constant family `F p = F₀` over `σ := Unit`, with
  polynomial coords the constants `c i j = C (φ (a i) j)` (`hg` = `eval_C`). This is
  `exists_good_realization_const`, the form the Case-I chain consumes — the
  multivariate keystone subsumes the old affine constant-path bridges.
- **`rw` over a `Submodule` equation under `finrank ℝ ↥(…)` trips the motive** —
  flip the equation and rewrite the hypothesis. → TACTICS-QUIRKS § 33.

### Promoted
- *Forward-mode + linear reduction chain → single-use wrapper sprawl; build the
  keystone first.* → `DESIGN.md` *Forward-mode reduction chains*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive; flip and
  rewrite the hypothesis.* → TACTICS-QUIRKS § 33.
- *Hypothesis laundering: a `\leanok` node may not carry a load-bearing hypothesis
  with no `\uses`-node discharging it (surfaced by `lem:case-I-realization`'s
  premature green).* → `blueprint/CLAUDE.md` *Static checks before commit → the
  honesty gate* (per-commit) + `CLEANUP.md` §A step 1 (safety net).

## Blockers / open questions

- **Device: RESOLVED.** `lem:genericity-device` green on the multivariate engine
  `exists_finrank_dualCoannihilator_polynomial` (route (a)); consolidation of the
  old affine chain done in the same commit.
- **Case-I realization carrier: closure proven, placement OPEN.** The
  `HasFullRankRealization`-closure-under-contraction carrier is landed, but it
  consumes the splice placement as two rigidity hypotheses. `lem:case-I-realization`
  is therefore **red** (honesty audit); the construction is tracked by the new node
  `lem:case-I-splice-placement`.
- **Case-II realization producer: MISSING (new red node).** Case II has only the
  accounting iff; no Lean lemma produces `HasFullRankRealization` for the 1-extension
  (`theorem_55`'s `hsplit`). Tracked by `lem:case-II-realization`.
- **Prop 1.1 `hub`: untracked genericity-free gap.** `rigidityMatrix_prop11` takes
  `hub` (genericity-free upper bound, "still to be bricked from Phase-19 partition
  machinery") as a hypothesis. The device underwrites only `hgen`. Left as a hypothesis
  for now; device-section prose states this explicitly.

## Hand-off / next phase

The device is green; the realization layer is honestly red. Three red obligations
remain (Case III aside). **Item 1 is the next work, but it is NOT a single commit** —
it decomposes into a 5-brick sequence (planned 2026-06-04); only the last brick flips
a node.

1. **Case-I splice placement** (`lem:case-I-splice-placement`, red node). *Produce* the
   `hHrig`/`hcrig` the landed carrier `hasFullRankRealization_ofParam_of_contraction`
   consumes: a single `ofParam G ends param` on which both the rigid block `G_H` and
   the block-internal contraction `G_c` are infinitesimally rigid. **The genuine crux
   is the witness-transfer gap:** the IH (`theorem_55`'s `hcontract`, ~line 1805) hands
   realizations of `H` and `G/E(H)` as *separate* `HasFullRankRealization` witnesses on
   *different* families; the carrier needs both rigid on *one* `ofParam` witness.
   Bridging that — lifting "rigid on some witness" to "rigid on the common moment-curve
   family at a generic `param`" — is the new content; the device only lifts an attained
   rank to a generic point, so two legs need the *intersection* of two Zariski-open
   rigid loci. Brick sequence (statements in the Lemma checklist):
   - **B1** `exists_param_isInfinitesimallyRigid_withGraph` — single-leg witness→`ofParam`
     transfer for a generic `param` (the hard engine; may itself split). *Not single-commit.*
   - **B2** `Graph.spliceEnds` (+ link lemmas) — endpoint selector: block hinges along the
     forest, boundary hinges to the contracted vertex `r` (thin over `endsOf`). *Single commit.*
   - **B3** `G_H`/`G_c` + `≤ G` + `hblk` block-internality bookkeeping (deletion form of
     `G/E(H)`; watch `deleteEdges` simp, QUIRKS §27). *Single commit.*
   - **B4** `exists_param_isInfinitesimallyRigid_two_withGraph` — the *simultaneous* merge:
     one generic `param` rigidifies both legs (re-run `exists_linearIndependent_rows_specialize`
     on the concatenated two-leg row family). *Borderline; absorbs the hard content if B1 doesn't.*
   - **B5** `exists_splice_placement_of_contraction` (THE NODE) — assemble B2/B3, feed the two
     IH realizations through B4, apply the carrier. *Single commit (glue); flips both
     `lem:case-I-splice-placement` and `lem:case-I-realization` green.*

   **Main risk:** the non-constant multivariate path through `exists_good_realization` may
   not have been exercised yet (consumers so far used only `…_const`); B1 surfaces any gap.
   Secondary: matching `G_c`'s deletion presentation to the `rigidContract`/`collapseTo` form
   the IH produces (possible `withGraph`-transport brick B3b). Keystone-first (DESIGN.md
   *Forward-mode reduction chains*) argues for landing B1's engine first.
2. **Case-II 1-extension realization** (`lem:case-II-realization`, new red node). The
   missing `HasFullRankRealization` *producer* discharging `theorem_55`'s `hsplit`:
   construct the re-inserted body's general-position panel normal `n` making the
   accounting iff's `hspan` hold, then land full rank via
   `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`. Parallel to item 1.
3. **Prop 1.1 `hub`** (genericity-free upper bound). Brick the Phase-19-partition
   count that gives `D + def(G̃) ≤ dim Z(G,p)` for *every* realization, discharging
   `rigidityMatrix_prop11`'s remaining hypothesis. Independent of items 1–2.

**Process lesson (don't repeat).** The single-use affine wrapper chain (now
collapsed) came from formalizing a *linear reduction* one hypothesis-discharge per
commit in forward mode. The fix: build the **keystone** (the multivariate device)
and validate the consumer API against it *first*, then collapse the affine bridges
into the constant-family closure. Promoted to `DESIGN.md` *Forward-mode reduction
chains*; also relevant to Phases 22–23.

**Also consumed by Phases 22–23** (Case III genericity, Claims 6.11/6.12); the
multivariate device pays forward (Case III bottoms on Lemma 2.1, Phase 17 green).

**Session note.** `origin/master` was inadvertently pushed once this session
(the local-only convention was otherwise kept; commits since are local). Match
author `bryangingechen@gmail.com`; do **not** push without asking.
