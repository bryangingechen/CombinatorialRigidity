# Phase 43 — PENCIL-NATURAL: design (cross-phase plan)

**Status:** in progress (opened 2026-11-07 with the PI), sub-lettered: a simpler pencil proof,
with no main result's statement to change. **43a** READS closed 2026-11-07 (`notes/Phase43a.md`):
the three fresh reads held, and each layer's inputs from them are in §2. **43b** LIFT3 closed
2026-11-08 (`notes/Phase43b.md`): the `d = 3` theorem is the case `d = 3` of the theorem in every
dimension, and the reduction's cases are proved once. **43c** NORMAL and SPRIME, one sub-phase at
the PI's word, opened 2026-11-08 (`notes/Phase43c.md`): the reduction on five structural cases,
then Theorem S′ at `d = 3`. EXPO opens after it, at the PI's word (§1, D5).

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

**PI, 2026-11-08, at LIFT3's open,** answering design doc §3's first open question ("Whether
LIFT3 lands as one sub-phase or two (N1a first)"). Question put: "Phase 43 design doc §3 leaves
LIFT3's shape to you at its open: N1a first as its own sub-phase, or N1c whole as one sub-phase
(43b)?" Chosen: "N1c whole as 43b (Recommended)" — offered as: "One sub-phase: N1a first slice,
then N1b and N1c. About −4.6k Lean lines, 17 files, 15 nodes; the d=3 route collapses to a remark
(D1)." Not chosen: "N1a alone as 43b".

**PI, 2026-11-08, after 43b's close,** asked whether anything needed discussing before 43c, was
offered four points, each with a recommendation, and answered them by number. The points as put,
in short, then the PI's words:
1. NORMAL had shrunk under LIFT3 (one caller, which already sends cases (iii)–(v) to one
   argument; the reduction would lose `n` and `hD`, and its simple two-edge-connected case its
   induction hypothesis), so: "make 43c NORMAL plus SPRIME, with NORMAL as slice 1", or NORMAL
   alone. **"Agreed, let's fold it into 43c then."**
2. `lem:pencil-min-degree-rigid` loses its last user under NORMAL: (a) a new short appendix
   chapter of results off the route, the Lean and the green node kept (recommended); (b) an aside
   in `pencil.tex`; (c) delete. **"Yes, that sounds like what I had in mind."**
3. KT Theorem 4.9 (contraction of rigid subgraphs and splitting off at degree two) has its
   counterpart in the main-component induction, not in the restated reduction: drop "cf. KT
   Theorem 4.9" from the reduction's title, put the 4.9 remark where its content is (the coverage
   or EXPO's road map), and keep one glue sentence that the reduction plays only the role of 4.9's
   outer induction. **"Sounds good."**
4. The open FRICTION entry on `check-phase-note.py --selftest` (red between sub-phases): approve
   its proposed fix and land it with 43c's open. **"Yes, let's fix it with the open."**

Then: "Let's do the opening commit of 43c with any fixes / clarifications recorded, and then hand
off to a fresh coordinate-phase session."

**PI, 2026-11-08, the same session,** answering §3's open question, which folding SPRIME into
43c brought forward. Question put: "Folding SPRIME into 43c means its open question gets answered
now (design doc §3). Theorem S′ (a core when no chain is usable) is stated today in every
dimension (thm:pencil-d-theorem-s, with def:pencil-d-usable-chain), but only d = 3 uses it; the
d ≥ 4 coverage uses 'long chain or core' instead. Keep S′ general in d, or fold it into a d = 3
statement?" Chosen: "Fold into d = 3 (Recommended)" — offered as: "One statement and one proof of
S′ in main-component.tex. thm:pencil-d-theorem-s, def:pencil-d-usable-chain, the d = 3 bridge
lemma and the formalization note go (about 80 TeX lines beyond SPRIME's −450). pencil-d.tex's
chains section loses its 'this core exists in every dimension' contrast sentence. A little more
Lean churn (specializing working code)." Not chosen: "Keep general in d".

**PI, 2026-11-08, a third session (the 43c coordinator's), reviewing SPRIME's pin,** whose one
choice taken in the PI's absence kept S′'s TeX proof on its own `d = 3` argument through
`lem:deficiency-core-bound`, rather than citing `lem:pencil-d-maximal-rigid-core` throughout as
the Lean does (which leaves `lem:deficiency-core-bound` with no user). The PI asked: "was there an
opportunity for extra simplification using the maximal-rigid-core lemma? If so, I'd go with
that." Told yes, and that the `d = 3` node and its two Lean pins (no Lean user) would then go, the
PI asked: "Would those results be independently interesting? If so we could put them in an
appendix like we have been for some others, but if not then we can lose them." Answered: no, they
are exactly the case `d = 3` of `lem:deficiency-core-bound-d`, which stays (the maximal-rigid-core
lemma uses it), so deleting them loses no result. So S′'s proof cites the maximal-rigid-core lemma,
and `lem:deficiency-core-bound` and its two declarations are deleted (`notes/Phase43c.md` item 4).

## 2. The layers, by stable code

In order. A letter is minted when a layer opens.

- **READS** (43a, closed 2026-11-07; all three held). Three read-only fresh reads, in parallel: Theorem S′ (N3, D2); the premise
  check, that `sec:pencil-d-generic` uses no `d = 3` generic node as a premise (N1, D3); and N6's
  flatness reading, every planar-rigid set flat on the main component (D3). With them, the probes
  of `notes/PencilNatural.md` §4 banked (D4). Gates LIFT3 (the premise check: no cycle, 43a) and
  SPRIME (S′).
- **LIFT3** (43b, opened and closed 2026-11-08; N1c; `notes/Phase43b.md`). **Verdict: done as
  planned**, in four slices and the close. `HasGenericPencilRealization K 3 G` is
  `liftAttains_of_simple 0` (`x0Gen`); `pencilPair_of_nonempty` is the `m = 1` case of
  `Graph.graded_pencil_conditioned_pair`; the reduction's cases are proved once, in
  `sec:pencil-d-reduction`; the explicit `d = 3` route is one remark after `thm:pencil-d-generic`'s
  proof (D1). 91 declarations and 15 nodes went, none came, and no main result's statement
  changed. The premise check (43a) found no cycle (`notes/pencil-natural/premise_closure.py`,
  `PremiseClosure.lean`). The build's inputs (the edges, the kept premises, the counts) are in
  `git show dc26fbfd:notes/Phase43-design.md`, §2.
- **NORMAL** (N2; 43c's slice 1, opened 2026-11-08, `notes/Phase43c.md`). `thm:pencil-reduction`
  on five structural cases: a loop; at most two bodies; not 2-edge-connected; non-simple; simple
  and 2-edge-connected. Cases (iv) and (v) merge; `lem:pencil-min-degree-rigid` leaves the route
  for a new appendix chapter, its Lean kept (§1 (b), and 2026-11-08 item 2); "cf. KT Theorem 4.9"
  leaves the reduction's title for one glue sentence, the remark itself EXPO's (§1 (a), and
  2026-11-08 item 3). LIFT3 left `thm:pencil-reduction` one caller,
  `Graph.graded_pencil_realization_theorem` (`Grade/Reduction.lean`,
  `thm:pencil-d-realization-theorem`), which already hands cases (iii)–(v) to one argument; so the
  restated reduction loses `n` and `hD`, its simple case takes no induction hypothesis, and it
  moves beside that caller (spike `notes/pencil-natural/NormalSpike.lean`).
- **SPRIME** (N3; 43c's slices after NORMAL, `notes/Phase43c.md`). Theorem S′, which S′'s fresh
  read confirmed (43a): open-ear-two and the split-off leave the `d = 3` coverage. It revises the
  42f record (`notes/Phase42-design.md` §1, "in `P³` both are load-bearing") to name the sense:
  used by Phase 40's route, not needed. **S′ is stated at `d = 3` only** (the PI, 2026-11-08, §1):
  `thm:pencil-d-theorem-s` and `def:pencil-d-usable-chain` fold into the `d = 3` nodes, and "the
  move" below, written for the general form, is read at `n = 3` with `exists_additiveCoreAt`,
  `ChainUsableAt` and `chainUsable_iff_chainUsableAt_three` deleted. **Verdict at the pin
  (2026-11-08):** S′ holds as Lean, the main results re-checked in the kernel (`SprimeSpike.lean`);
  a walk cuts slices A, B, C, the sizes and §2's misses (`notes/Phase43c.md` items 3–5). The read's
  inputs for the build:
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
  - **From LIFT3** (43b's close). `thm:pencil-x0-generic-attains` stays as `sec:main-component`'s
    summary, off the realization theorem's route, its role prose a hypothesis to revisit, not a
    settled exposition; `x0Dist` and `x0Gen` keep no Lean consumer. The old `d = 3` route's one
    home is the remark after `thm:pencil-d-generic`'s proof. Each `d = 3` sentence of
    `sec:pencil-d-reduction` reads its case at `d = 3` with no deleted node behind it, and may be
    cut.
  - **From NORMAL** (43c's open). The KT Theorem 4.9 remark, where its content is: the
    main-component induction's contraction and degree-two steps, in the coverage or in the road
    map (§1, 2026-11-08 item 3); the reduction keeps one glue sentence. Which chapter
    `thm:pencil-reduction` lives in (`pencil.tex`; its only user is in `pencil-d.tex`).

## 3. Open questions

- *Closed 2026-11-08:* whether LIFT3 lands as one sub-phase or two (N1a first). One, 43b, with
  N1a its first slice: the PI's entry of that date, §1.
- *Closed 2026-11-08:* whether SPRIME keeps Theorem S′ general in `n`, as
  `thm:pencil-d-theorem-s` is, or folds it and `def:pencil-d-usable-chain` into a `d = 3` S′.
  Folded: the PI's entry of that date, §1.
