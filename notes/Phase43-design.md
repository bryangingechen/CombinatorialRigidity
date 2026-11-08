# Phase 43 — PENCIL-NATURAL: design (cross-phase plan)

**Status:** in progress (opened 2026-11-07 with the PI), sub-lettered: a simpler pencil proof,
with no main result's statement to change. **43a** READS closed the same day (`notes/Phase43a.md`):
the three fresh reads held, and each layer's inputs from them are in §2. No sub-phase is open.
The later layers open one at a time, each at the PI's word (§1, D5). Next: LIFT3's open, with the
PI's choice of N1a first or N1c whole (§3).

This file is the phase's entry point: the target (§0), the PI's decisions (§1, verbatim), the
layers by stable code (§2) and the open questions (§3). The recon record stays in
`notes/PencilNatural.md`, cited by section: the proof as it stands (§2), the verdicts N1–N6 with
their sizes (§3), the recon's brief (§4) and the intuitions I1–I4 (§5).

## 0. Target

Make the proof of the pencil realization theorem simpler and its cases more natural, in every
dimension, and then explain it in the blueprint: a road map in the manner of KT §1.1. The main
results (`pencil_realization_theorem`, `pencilPair_of_nonempty`,
`Graph.graded_pencil_conditioned_pair`) keep their statements. What changes is the route:
- the `d = 3` generic conjunct comes from the every-dimension lift (N1c), so every dimension has one
  shape: A the reduction, B the main-component induction, C the lift;
- the reduction is restated on five structural cases (N2);
- the `d = 3` coverage loses two short-chain rows (N3, Theorem S′).
What the recon ruled out (N3's other rows, N4, N5, N6) is `notes/PencilNatural.md` §3.

## 1. The PI's decisions (verbatim)

**PI, 2026-11-07, on N2's call (a), whether the reduction may stop mirroring KT Theorem 4.9:** "I
think we should be free to diverge from KT Theorem 4.9, but if it plays a similar role in the proof
as KT Theorem 4.9 does in the KT proof, then it's worth a reference (perhaps just in a remark or in
surrounding glue text)."

**PI, 2026-11-07, on N2's call (b), `lem:pencil-min-degree-rigid`, after asking why it would
retire:** "Let's keep it off the route for now; perhaps we could move it into a separate appendix."
The blueprint's `\appendix` holds only `retrospective.tex` today.

**PI, 2026-11-07 (a second session), D1–D5**, deferred from the first, after a synthesis of the
verdicts. Each was chosen from the options offered; the chosen label is quoted, then what it was
offered as:
- **D1:** "N1c (Recommended)": the reduction proved once, for every `d` (about −4.6k Lean lines,
  17 files, 15 nodes); `pencil.tex` stops proving `d = 3` on its own terms.
- **D1, the old route:** "Collapse to a remark (Recommended)": the explicit `d = 3` generic
  constructions leave, Lean and nodes, for one short remark naming the route and why C replaces it.
- **D2:** "Yes, before N3's build (Recommended)": the fresh read of Theorem S′.
- **D3:** "Both now": the premise check and the flatness reading, in parallel, before any N1 work.
- **D4:** "Bank them, geng allowed (Recommended)": the probes committed with README rows, nauty's
  `geng` the second exception to stdlib-only Python.
- **D5:** "Open as Phase 43 (Recommended)": in this session, sub-lettered, each sub-phase opened
  at the PI's word.

## 2. The layers, by stable code

In order. A letter is minted when a layer opens.

- **READS** (43a, closed 2026-11-07; all three held). Three read-only fresh reads, in parallel: Theorem S′ (N3, D2); the premise
  check, that `sec:pencil-d-generic` uses no `d = 3` generic node as a premise (N1, D3); and N6's
  flatness reading, every planar-rigid set flat on the main component (D3). With them, the probes
  of `notes/PencilNatural.md` §4 banked (D4). Gates LIFT3 (the premise check: no cycle, 43a) and
  SPRIME (S′).
- **LIFT3** (N1c). `HasGenericPencilRealization K 3 G` by `liftAttains_of_simple 0`, then the
  reduction proved once for every `d`, and `pencilPair_of_nonempty` as the `m = 1` case of
  `Graph.graded_pencil_conditioned_pair`. The explicit `d = 3` route collapses to a remark (D1).
  N1a, its first slice, may land alone. The premise check (43a) found no cycle: C's 17 roots
  close over 458 nodes, all 348 of `thm:pencil-generic-step`'s among them, only through two
  cross-reference edges; cut, 441, none a `d = 3` generic node, and the Lean kernel closure has
  no `d = 3` generic declaration (`notes/pencil-natural/premise_closure.py`,
  `PremiseClosure.lean`). Its inputs for the build:
  - **Edges.** `pencil-d.tex:6673` (`thm:pencil-d-generic`'s proof) and `:6755`
    (`cor:pencil-d-conditioned-pair`'s) to `thm:pencil-conditioned-pair-nonempty`: removed, then
    reversed (N1a needs only `:6673`). No other edge changes.
  - **Kept, restated.** `lem:pencil-generic-steer` (a) and its parametrization, and
    `lem:pencil-rigid-good-ear` (3 of 5 pins), are C's premises; so are
    `lem:pencil-feasible-hub-conditions`, `lem:pencil-x0-planes-separate`,
    `def:pencil-two-ear-graph`, `lem:pencil-x0-conjunct-three` and `lem:pencil-condition-linear`.
    `Arms.lean` keeps `exists_contragredient_linearEquiv` (`Grade/LiftCutEdge.lean`);
    `Grade/LiftWitness.lean`'s unused `Pencil.Pair` import goes first.
  - **Counts.** N1c deletes 13 nodes wholly and 3 in part (the recon: 15). Its prose falls at 12
    labels of `sec:pencil-d-lift` and `sec:pencil-d-generic`, 8 of them under N1a, and at 7
    `\cref`s in `sec:pencil-d-reduction` (the recon: about 17).
- **NORMAL** (N2). `thm:pencil-reduction` on five structural cases: a loop; at most two bodies; not
  2-edge-connected; non-simple; simple and 2-edge-connected. Cases (iv) and (v) merge;
  `lem:pencil-min-degree-rigid` leaves the route for an appendix (§1 (b)); KT Theorem 4.9 cited in a
  remark (§1 (a)). After LIFT3, which leaves one caller.
- **SPRIME** (N3). Theorem S′, which S′'s fresh read confirmed (43a): open-ear-two and the
  split-off leave the `d = 3` coverage. It revises the 42f record (`notes/Phase42-design.md` §1,
  "in `P³` both are load-bearing") to name the sense: used by Phase 40's route, not needed. The
  read's inputs for the build:
  - **The move.** Not `exists_chain_or_core` at `ℓ = 1`: Theorem S itself,
    `Graph.IsX0Graph.exists_additiveCoreAt` (only consumer `exists_additiveCore`,
    `CoverageTheoremS.lean`), with its blocking hypothesis `¬ ChainUsableAt` losing the `k = 2`
    merged-equality and `k = 1` split-off disjuncts; its conclusion unchanged. In the body, `hk2`
    becomes a case on a `k = 2` chain with non-adjacent ends (NEW-1, then NEW-2), and the
    `def > 0`, all-`k = 1` branch calls `exists_core_of_deficiency_three_pos`. `ChainUsable(At)`
    and `X0Reduces` lose the two disjuncts and constructors. About 130 lines become 150.
  - **NEW-1** (`Induction/SparseDeficiency.lean`): at a sparse `G`, non-adjacent `a ≠ b` with
    the two-orbit bound failing lie in a rigid `Z`, `|Z| ≥ 3`; the body of
    `deficiencyMerged_two_add_two_le_of_three_le`, extracted (net about +6;
    `lem:deficiency-two-body-chain` restated). **NEW-2** (`Grade/TheoremS.lean`): a rigid
    `Y ⊆ V₁` gives a core avoiding `x₀`; `exists_additiveCoreAt_of_partitionDef_nonpos` less its
    first step (about +8; `lem:pencil-d-chain-core` gains the form).
  - **Sizes** (from line ranges, not a liveness walk). TeX net about −450 (−530 if
    `thm:pencil-d-theorem-s` folds into a `d = 3` S′): `sec:main-component-splitoff` (330 lines,
    with `lem:pencil-curve-limit`), `thm:pencil-x0-open-ear-two`,
    `lem:deficiency-one-body-chain-d`, two table rows and
    `rem:pencil-x0-theta`'s `k = 2` step. Lean about −1,100, +40–90: `SplitOff.lean` (748),
    open-ear-two in `MainComponent/Short.lean`, two `SparseDeficiency.lean` bounds, and code only
    the split-off uses (`Ear.lean`'s `finrank_span_rigidityRows_eq_add_of_motions`, `Bridge.lean`'s
    `finite_setOf_finrank_lt_of_curve`, `Mathlib/Data/Matrix/Mul.lean`). The deletion gate must
    catch dead names in docstrings of `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`,
    `Mathlib/Algebra/MvPolynomial/Polynomial.lean` and `Induction/Operations.lean`.
- **EXPO**. The road map (`notes/PencilNatural.md` §5), with the A/B/C structure as it stands after
  the layers above, I1–I4 as corrected, and the flatness reading, which its read confirmed once
  stated precisely (43a). Last. The read's inputs:
  - **(F).** At every main picture of `G`, every height is one affine function on a planar-rigid
    set `W`, so the points of `W` lie in one plane, the panel of each body of `W` (`d = 3`; in
    the polar form, one concurrency point). At `d ≥ 4` each of the `d − 2` heights is affine on
    `W`: the bodies share the plane `Π_v`, not one panel. It composes five landed lemmas
    (`lem:pencil-contract-standing-rigid`, `thm:pencil-jj-equality`,
    `lem:pencil-lifting-space-affine`, `lem:pencil-lifting-restrict`,
    `lem:pencil-condition-linear`); "main" rather than "general" needs
    `lem:pencil-polynomial-section`'s argument, by hand. No proof uses it: a remark with no pin.
  - **Degeneracy.** The general configuration is degenerate exactly when a planar-rigid set holds
    two members of one closed hub-neighbourhood. `K_{2,3}` is planar-rigid (`def₂ = 0`), so
    `lem:pencil-x0-two-hubs-obstruction` is an instance; the doubled triangle (three hubs, each
    pair joined by two paths through one body; 9 bodies) is one the lemma misses, feasible and
    attaining. A planar-rigid set with no such pair is a triangle or a hub with pendant
    triangles; `lem:pencil-rigid-good-ear`'s two shapes match: a degree-two body between two hubs
    (degenerate, so removed and re-added off the main component) and a pendant triangle
    (harmless). So flatness says why the generic
    conjunct leaves the main component in every dimension (C lifts nondegenerate `P³`
    realizations), and sharpens N6's NO-GO.
  - **The draft remark** (the reader's, for after the `K_{2,3}` paragraph of
    `sec:main-component-statements` or the road map): `G[W]` meets the standing hypotheses; its
    lifting space at a general picture has dimension three, so is the affine heights; every
    height of `G` restricts to one of `G[W]`, so `W`'s points lie in one plane, each body's panel;
    two members of one closed hub-neighbourhood in `W` then have dependent normals. The `K_{2,3}`
    paragraph's "some set of at least two of them is planar-rigid" understates: all five are.

## 3. Open questions

- Whether LIFT3 lands as one sub-phase or two (N1a first): the PI's, at its open. The premise
  check unblocks both; its constraints on LIFT3 are at its item in `notes/Phase43a.md`.
- Whether SPRIME keeps Theorem S′ general in `n`, as `thm:pencil-d-theorem-s` is (it holds at
  every `n ≥ 3`, but is used only at `d = 3`), or folds it and `def:pencil-d-usable-chain` into a
  `d = 3` S′: decided at SPRIME's open.
