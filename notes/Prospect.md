# PROSPECT — study, simplify, generalize the formalized molecular-conjecture proof (planning note)

**Status:** survey complete + adjudication round 1 done (2026-07-10);
**grouping 1 opened as Phase 31** (work log `notes/Phase31.md`);
groupings 2–4 queued in adjudicated order (ROADMAP *Queued post-program
phases*, "PROSPECT (continuation)"); grouping 5 (G2 planar) dropped by
the Phase-31 sizing recon (the G2 entry below). This note stays the survey record
+ phase-order home for the continuation. Same editing discipline as
phase notes (≤8-line entries, lift cross-cutting lessons).

## What this phase is

User-proposed (2026-07-10): with the molecular conjecture now a formal
object, study the proof for **simplifications** and **generalizations**
— the Phase-30 (RELAX) mold, where a compiler-witnessed recon settled a
question that would have been hard to trust informally. Scope rule set
by the user: results already in the literature but not formalized here
are in scope **when close to the formalized surface**. This note is the
survey record: a graded candidate inventory, the compressed recon
findings backing each grade, and the open recon questions a track's
first dispatch should settle.

## Candidate inventory (graded)

### Tier 1 — recommend: bounded work on a verified route

- **S1 — RECLASSIFIED at adjudication (2026-07-10): the d=3 line is
  retained on purpose; the track reduced to documentation, landed.**
  The survey read the zero-caller d=3 family (the `theorem_55_d3`-style
  wrappers; the `case_III_candidate_dispatch` chain) as dead weight; the
  user's standing decision is that it stays — the three-candidate
  dispatch is simpler than the chain transport and is the form KT give
  at §6.4.1, so it backs the worked-case exposition, in Lean as in the
  blueprint. That this wasn't clear from the text was the real defect:
  the `lem:case-III-candidate-dispatch-d3` fmlnote (`case-iii.tex`) now
  states the retention explicitly, and `notes/Phase23-cleanup.md`
  deferred item 1 is closed by adjudication. Optional phase rider:
  matching one-line retention notes in the d=3 decls' Lean docstrings
  (docs-only, but rebuilds the molecular tree — bundle with the next
  Lean-touching commit).
- **R1 — DONE (Phase 31, 2026-07-10).** The time-boxed speculative
  proof-restructuring recon over the five user-proposed seed questions.
  Verdict in *R1 recon verdict* below: one GO (merge the `|V| = 3`
  triangle base into the cycle brick — R1-3), two NO-GOs with grounded
  refutations (R1-1, R1-2), one already-banked (R1-4), one NEEDS-SPIKE
  that sharpens the queued G1 recon (R1-5), plus one incidental
  zero-caller cleanup. The GO candidate awaits user adjudication
  (`notes/Phase31.md` *Blockers*).
- **S2. Phase-30 residual: the general-position rationality conjunct.**
  `exists_generalPosition_polynomial` (`AlgebraicInduction/PanelHinge.lean`)
  and `exists_generalPosition4_polynomial` (`Molecule/GeneralPosition4.lean`)
  still carry a live-but-everywhere-discarded rationality conjunct
  (`notes/Phase30.md` *Deliberately out of scope*). Folding it in is the
  one live RELAX follow-on; small, same sweep discipline as slice (e).
- **L1. Jacobs' conjecture, now an unconditional theorem** (the survey's
  best genuinely-new target): *G² is M-independent iff G² is Laman* —
  Jackson–Jordán 2008 Thm 5.4 derives it from the rank formula we have
  as `SimpleGraph.molecule_rank_formula`; the missing inputs are their
  Thm 5.3 (G² Laman ⇒ |E(G²)| ≤ 3|V|−6−def(G̃), ~1.5pp counting) and
  Lemma 5.2 (G² Laman ⇒ max degree of G ≤ 3). Self-contained on the
  formalized surface; medium cost.
- **L2. The degree-1 rank formula** (JJ 2008 Lemma 4.2): explicit
  `r(G²)` for graphs with degree-1 vertices (trees: `2|V|−5+|V₁|`;
  general: reduction to the ≥2-core). This is the *correct* form of
  "weaken Cor 5.7's min-degree hypothesis" — see K2 below. Short
  induction on top of `molecule_rank_formula`.

### Tier 2 — attractive, medium-to-large; open with a recon

- **G1. Field generality of the core Thm 5.5/5.6 chain.** Survey
  verdict: **no essentially-real step.** Zero topology/analysis in
  `Molecular/` (KT "Lemma 5.2 semicontinuity" is formalized as algebraic
  span-monotonicity, `RigidityMatrix/Basic.lean`); the two ℝ chokepoints
  are proof-local with field-general statements: (i) three
  Gram-Schmidt-proved decls in `Molecular/MeetHodge.lean`; (ii) the
  Gram-determinant lemma
  `linearIndependent_rows_iff_det_mul_transpose_ne_zero`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`, ordered-field-only), whose
  field-general maximal-minor twin already sits in the same file and
  powers a parallel engine. Rest is mechanical ℝ→K over ~30 files.
  Precedent: Whiteley 1988 proves the matroid-union layers over any
  infinite field; a field-general KT Thm 5.5/5.6 appears to be **new**.
  Cost: moderate refactor + two bounded reworks. Excludes the molecule
  application layer (K4).
- **G3. The generic / "almost all realizations rigid" lift**, via the
  Jackson–Jordán 2010 *coordinate* route (their Thms 5.2, 6.4, 7.2,
  8.1/8.2), which deliberately avoids Whiteley 1988's variety-
  irreducibility machinery. Upgrades the existence-form Tay (Phase 15),
  body-hinge (Phase 16), and molecular statements to "every generic
  realization"; JJ 2010 p.13 notes the combination with the (now-proved)
  conjecture sharpens Cor 5.7 to all generic G² realizations. Deferred
  since Phases 15/16 (`body-bar.tex`, `body-hinge.tex` remarks). Medium.
  Caveat: JJ's genericity layer runs on algebraic independence over ℚ —
  the device Phase 30 eliminated; recon whether the product route
  substitutes (below).
- **G2 — SETTLED at the Phase 31 sizing recon (2026-07-10): FALSE at
  `D = 3`; planar track DROPPED** per the adjudicated rule (*Hand-off*
  item 5). `K_{2,3}` refutes `exists_adjacent_degree_two_pair` at
  `n = 2`, verified exhaustively against the `Deficiency.lean` bodies:
  minimal `0`-dof (`2·K_{2,3}` is exactly `(3,3)`-sparse with
  `2|E| = 3(|V|−1) = 12`, so `E(G̃)` is the unique base), no proper
  rigid subgraph (every proper induced subgraph on `≥ 2` vertices has
  `def ≥ 1`), yet its degree-2 vertices (the 3-side) are pairwise
  non-adjacent. So no smarter count exists (KT's Lemma 4.6 is genuinely
  `d = 3`), and Case III obstructs twice (`chainData_extract` separately
  needs `n ≥ 3`): a planar phase would mean formalizing the JJ
  pin-collinear route — a new program, not a Case-III adaptation.
- **S3 — RECLASSIFIED at Phase 31 (2026-07-10): already formalized in
  Phase 20; the deferral claim was stale.** The full tightness equality
  (`|X−e| = D(|V(X)|−1)` exactly) and the `G[V(X)]`-rigid conclusion
  landed as `Graph.circuit_induces_isTight` /
  `Graph.circuit_induces_isRigidSubgraph`
  (`Molecular/Induction/Operations.lean`), pinned green on
  `lem:circuit-induces-rigid` in `molecular-induction.tex` since Phase 20
  — including the vertex-induced-subgraph-from-edge-set construction
  (`Graph.inducedSpan`/`Graph.fiberSpan`) this survey read as the
  "genuinely unbuilt piece". The stale surfaces were the `deficiency.tex`
  `lem:circuit-rigid` proof remark (said "deferred with
  `thm:def-eq-corank`") and the `Deficiency.lean` file-header docstring
  (said "an early-Phase-20 deliverable") — both fixed this commit to
  cross-reference the landed node instead. No Lean work needed.

### Tier 3 — parked (real but low value or off-theme)

- KT Lemma 4.2 / `lem:forest-surgery-unsplit` (+ forest-surgery route to
  KT 4.4): sound, redundant with the live deficiency-count route
  (`molecular-induction.tex`, `notes/Phase20.md`).
- Lee–Streinu follow-ons (component pebble game §5, `(k,ℓ)`-tight
  Henneberg §6, block/redundancy classification): self-contained
  algorithmic formalization, off the molecular theme (`notes/Phase9.md`).
- Inductive characterizations alongside existing proofs (Henneberg for
  Laman, Tay's Henneberg-type body-bar construction — Nixon–Ross survey
  Thms 2.5, 9.2); matroid-theoretic reframing of Laman (ROADMAP §
  *Mathematical roadmap* preamble). Alternative framings of complete
  results.

### Killed / walled off (with the reason on record)

- **K1. Multigraph Conjecture 1.2.** Verified false *in the project's
  meet-based hinge model* (parallel edges forced to share a hinge line;
  KT Lemma 5.3's coincident-panel double-edge realization inexpressible)
  — `notes/Phase23-cleanup.md`, blueprint
  `fmlnote:molecular-conjecture-multigraph`. Any multigraph
  strengthening means a different hinge encoding, i.e. a re-architecture,
  not a generalization pass.
- **K2. Weakening Cor 5.7's min-degree-≥2 in place.** The hypothesis is
  essential: it feeds only the square-graph dictionary
  (`Molecule/Dictionary.lean` — injectivity *and* surjectivity of the
  screw-velocity iso need ≥2 neighbors to pin a body's screw at 3
  non-collinear points), and the formula is false without it (single
  edge: `r(G²) = 1` vs `3·2−6−def ≤ 0`; a degree-1 body carries an
  uncounted hinge-rotation dof). The literature's fix is L2. General
  position and connectivity are non-issues (internal witness; no
  connectivity hypothesis exists).
- **K3. KT §7 open problems**: the explicit rank function of *subgraphs*
  of G², and the general 3-D combinatorial bar-joint characterization.
  Genuinely open (KT say so; Nixon–Ross concur); the Phase-24 scope
  guard stays up.
- **K4. Field-generalizing the molecule application (Phases 24–26).**
  Genuinely ℝ³-bound physics (cross-product screw model, inner-product
  bar constraints, `EuclideanSpace ℝ (Fin 3)` general position); not a
  sensible target. G1's scope is the core chain only.

## Open recon questions (each track's first dispatch)

- **G1:** spike the two chokepoints — reprove one `MeetHodge.lean` decl
  metric-free, and reroute the genericity engine onto the maximal-minor
  twin — before sanctioning the ~30-file mechanical sweep.
- **G2 — answered (2026-07-10):** false at `D = 3` (`K_{2,3}`; the G2
  entry above). The Case-III degeneration is essential at `d = 2`; the
  planar track drops from the queue.
- **G3:** can the Phase-30 product route replace JJ 2010's
  algebraic-independence-over-ℚ genericity layer, or does the "almost
  all" form genuinely need alg-indep back? (Bears on whether RELAX's
  simplification survives the strengthening.)
- **L1:** dependency check of JJ 2008 Thm 5.3 + Lemma 5.2 against the
  formalized sparsity/Laman surface (Phase 1–2 API vs. their counting).

## R1 recon verdict (2026-07-10; Phase 31)

Graded answers to R1's five seed questions, from a source-grounded pass
over the induction skeleton (`Graph.minimal_kdof_reduction_all_k` and
its five producers), the Case-I/II/III producer bodies, and
`retrospective.tex`'s wrong-turns inventory. No Lean changed.

- **R1-1 (four-case collapse: the Lemma-6.5 arm vs Case III) — NO-GO.**
  The preconditions are disjoint: the 6.5 arm fires under `∃ H,
  IsProperRigidSubgraph`, Case III under its negation — and the chain
  extractor (`chainWalk_trichotomy`) consumes `hnoRigid` essentially,
  for both the degree-2 supply and the short-cycle exclusion. The counts
  differ in exactly the way the retrospective's `+(D−1)`-vs-`+D` episode
  records: 6.5 re-inserts `v` with a full `D`-row block
  (`case_I_realization_h65_gen`), Case III gets only `D−1` free rows and
  needs the Claim-6.11/6.12 machinery. The genuine sharing is already
  banked at brick level (`linearIndependent_sum_pinned_block` + the
  N7b/L8c row suite serve both arms).
- **R1-2 (absorb Case II into Case I's block-triangular splice) —
  NO-GO.** Same premise disjointness (`hnoRigid` is a Case-II
  *hypothesis*), plus a structural block `CaseII.lean`'s own header
  records: the Case-I splice consumes a subgraph `H ≤ G`, but Case II's
  inductive object `G_v^{ab}` is not `≤ G` (`e₀ ∈ E(G_v^{ab}) ∖ E(G)`);
  Case II instead runs on the `panelRow(e₀) = panelRow(e_b) +
  panelRow(e_a)` span identity, which has no Case-I analogue.
- **R1-3 (chain/cycle dichotomy) — GO, one small slice: merge the
  `|V| = 3` triangle base into the cycle brick.** The dichotomy itself
  is not uniformizable (the cycle is a terminal base case, the chain
  feeds the IH; the extractor's cycle disjunct *is* confirmed vacuous at
  `d = 3` — an emitted cycle is spanning, so `m = |V| ≥ 4 > 3 = n`,
  `CycleData.vertexSet_ncard`'s documented mechanism). But the triangle
  base is the `m = 3` cycle: `cycle_realization` is the line-by-line
  general-`m` generalization of
  `hasGenericFullRankRealization_of_triangle` (its own docstring), its
  internals need only `3 ≤ cy.m` (the `_hV4`/`_hk1` binders are unused;
  their "`hcycle`-slot interface" rationale lapsed at the Phase-23h A1
  rewire), and KT state Lemma 5.4 at `3 ≤ |V| ≤ D` — the merge is *more*
  source-faithful than the current split. Work: a `K₃ → CycleData`
  constructor (simple + min-degree-2 via `two_le_degree_of_isKDof_zero`
  + `|V| = 3` force `G = C₃`), rewire the producer's triangle arm
  (`case_III_hsplit_producer_all_k`), drop the stale unused binders,
  restate the blueprint pair (`lem:triangle-realization` folds into
  `lem:cycle-realization`), and retire-or-retain the triangle stack
  (`theorem_55_triangle` / `exists_triangle_normals` / the T4 assembly —
  each has a cycle-stack sibling; retention is an S1-style exposition
  call). Est. 1–2 commits.
- **R1-4 (Phase-30 alg-indep removal → simpler nested-IH shape) —
  NO-GO: already banked.** KT eq. (6.22)'s nested IH is already in the
  post-RELAX shape (`exists_nested_rankPolynomial_lower_all_k`: the
  nested rank exposed as one polynomial factor in the single
  `exists_eval_ne_zero` product shot, RELAX slices (a)/(d)); the motive
  pair `(G.Simple → GP) ∧ bare` is forced by KT's own two-mode
  conclusion (non-simple graphs genuinely lack general-position
  realizations, and Lemma 6.2 consumes the bare conjunct), so no
  conjunct is removable. Nothing further for the removal to unlock.
- **R1-5 (`MeetHodge.lean` metric-free) — NEEDS-SPIKE (= the queued G1
  chokepoint spike; not opened here).** Sharpenings for that spike:
  (i) `finrank_toDualPerp_pair_eq` is cheaply metric-free (kernel
  intersection of two independent functionals has codimension 2) — the
  easy third of the file; (ii) the real chokepoint is
  `complementIso_extensor_mem_range_map_subtype`, whose metric-free
  route is GL-equivariance-up-to-determinant replacing the current
  O(n)-equivariance (the target is a membership/proportionality, hence
  scalar-blind), retiring the Gram–Schmidt helper
  `exists_orthonormalBasis_span_pair_eq`; (iii) named field-generality
  risk: over a non-ordered field the normal pair's span can meet its own
  `toDual`-perp (isotropic normals), degenerating any frame-extension
  argument — a hand-checked `ℂ`, `k = 1` example suggests the
  *statement* survives while that proof route does not; (iv) independent
  payoff even over ℝ: `MeetHodge.lean` is a separate file only for the
  PiL2-import `whnf` regression (TACTICS-QUIRKS § 59), so metric-free
  folds it into `Meet.lean`.
- **Incidental (cleanup-grade) — RETIRED (adjudicated, 2026-07-10).**
  `Graph.minimal_kdof_reduction_full` (`Molecular/Induction/ForestSurgery/Reduction.lean`)
  had zero callers and a stale docstring ("used by
  `theorem_55_minimalKDof_k_all_k`'s Case-III producer" — that route
  runs on `minimal_kdof_reduction_all_k` since Phase 22i); not
  blueprint-pinned. User chose retirement over the docstring fix;
  landed in `notes/Phase31.md` *Decisions made*.

No phase-queue re-ordering implied: R1-3 is a bounded slice adjudicable
into Phase 31 or its own follow-up; R1-5's findings feed the
already-queued G1 recon unchanged; R1-1/2/4 close their questions.

## Survey record (compressed; 2026-07-10)

Four parallel read-only recons; findings above carry their pointers.
Residual uncertainty flags worth keeping: (a) the S1 liveness trace was
grep-based, not `lean_references`-exhaustive; (b) the G2 chain-extractor
floor (`cd.d = n`, position-2 access ⇒ n ≥ 3) was inferred from
docstrings + `omega` obligations, not the `ChainData` structure body;
(c) the `D ≥ 6` tightness question (G2) was explicitly not settled;
(d) G1's cost estimate is a signature-level judgment, not an attempted
refactor. Two already-discharged items surfaced by the sweep are
*evidence for this phase's premise*, not work: the formalized KT Lemma
4.1 over-quantification erratum + balanced-packing gap fill
(`retrospective.tex`, `notes/Phase20.md`), and the multigraph finding
(K1).

## Citations (verified for this note)

- Jackson, Jordán, *The generic rank of body–bar-and-hinge frameworks*,
  Eur. J. Combin. **31** (2010), 574–588. (Front matter of the `.refs`
  copy; theorem numbers from the survey read of that copy.)
- Jackson, Jordán, *Pin-collinear body-and-pin frameworks and the
  molecular conjecture*, Discrete Comput. Geom. **40** (2008), 258–278.
  (`.refs` copy is the EGRES TR-2006-06 preprint — title/authors
  verified there; journal coordinates per KT 2011's bibliography.)
- Nixon, Ross, *One brick at a time: a survey of inductive constructions
  in rigidity theory*, arXiv:1203.6623; in *Rigidity and Symmetry*,
  Fields Inst. Commun. **70** (2014). **The `.refs` copy was misnamed
  as "theran-2012"** (real Nixon–Ross front matter verified); renamed
  locally to `nixon-ross-2013-inductive-constructions-survey.pdf`.
- Jackson–Jordán 2008 (Combinatorica **28**), Katoh–Tanigawa 2011 (DCG
  **45**), Whiteley 1988 (SIAM J. Disc. Math. **1**), Whiteley 2005
  (Phys. Biol. **2**): already project-canonical (ROADMAP *References*);
  the specific theorem numbers used above (JJ 2008 Thms 3.4, 4.1, 4.3,
  5.3, 5.4, Lemmas 4.2, 5.2; Whiteley 1988 Thm 4, Prop 6, Lemma 7,
  Cor 9) were verified against the `.refs` copies during the survey.

## Hand-off / next step

Adjudication round 1 (2026-07-10): S1 reclassified (retention
intentional; documentation landed); the other tracks confirmed
reasonable; R1 added at the user's suggestion. **Recommended phase
grouping**, opened one at a time with re-adjudication at each boundary
(the tier list above is sorted by confidence, not into phases; this is
the phase order):

1. **Opened as Phase 31 (2026-07-10; `notes/Phase31.md`):** S2 + S3 +
   R1 + the G2 sizing recon. Everything bounded; the two recons produce
   the information that shapes the rest of the queue; simplifications
   land before generalizations so G1's tree-wide sweep runs once, on
   the proof's final shape.
2. **Second — the new-math phase:** L1 (Jacobs) + L2 (degree-1
   formula). Consumes the rank-formula *statement*, not proof
   internals, so R1 restructurings can't invalidate it; swap with 1 if
   new mathematics should lead.
3. **Third: G1 field generality**, recon-first (the two chokepoint
   spikes), after any R1 restructuring lands.
4. **Fourth: G3 generic lift**, after G1 — build the genericity layer
   once, over the final carrier; its recon is the product-route
   substitution question.
5. **G2 planar — DROPPED (2026-07-10):** the sizing recon refuted
   `exists_adjacent_degree_two_pair` at `D = 3` (`K_{2,3}`; the G2
   entry), so the track drops per this item's pre-registered rule.

Each later grouping's opening commit mints its number per
`PHASE-BOUNDARIES.md` *When this commit opens a phase* and seeds its
`notes/PhaseN.md` from the entries here. Phases are **not pre-divided**:
if one runs long, sub-letter it at the seam when the split arrives
(codes-until-open discipline). Likely seams, should they be needed:
G1 at chokepoint-spikes vs. the mechanical ℝ→K sweep; G3 at the
body-bar layer vs. the molecular layer; Phase 31's R1 memo spawning
adjudicated follow-up slices.
