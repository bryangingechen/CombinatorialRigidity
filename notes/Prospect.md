# PROSPECT — study, simplify, generalize the formalized molecular-conjecture proof (planning note)

**Status:** queued (codename **PROSPECT**; number minted on open).
Survey complete (2026-07-10, four parallel read-only recons); **awaiting
user adjudication of tracks** before the phase opens.
**Audience:** the user (track selection) + the opening agent. Same
editing discipline as phase notes (≤8-line entries, lift cross-cutting
lessons).

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

- **S1. Molecular dead-code sweep + d=3-line retirement.** The Phase
  24–26 consumers use the general-`d` spine at `k = 2`; the d=3-specific
  line is zero-caller dead weight in two groups: thin wrappers defined
  *as* instances of the general line (`theorem_55_d3`,
  `rankHypothesis_of_theorem_55_d3`, `case_III_realization`,
  `case_I_dispatch`, …) and the orphaned original d=3 Case-III machinery
  (`case_III_candidate_dispatch`, ~420 lines in
  `Molecular/AlgebraicInduction/CaseIII/Realization.lean`, + its
  d=3-only feeders in `RigidityMatrix/Claim612.lean`). Subsumes the
  deferred sweep of `notes/Phase23-cleanup.md`. Gates: repoint the ~5
  blueprint nodes still pinning dead decls (`lem:case-III-claim612`
  family — the d=3 worked-case exposition should survive as prose);
  re-confirm liveness with `lean_references` (survey traced by grep).
  **Exclusions verified live:** `PanelHingeFramework.molecular_conjecture`
  (general-`n` headline) and `Molecular/Meet.lean` (general-`k` infra).
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
- **G2. The planar case (n = 2, D = 3).** The statement
  `molecular_conjecture (n := 2)` is well-formed and classically true
  (Jackson–Jordán's pin-collinear paper solved d=2 pre-KT; `.refs` has
  the TR). The `3 ≤ n` floor is purely a proof-route restriction, and
  **Case III is the sole obstruction**: `Graph.chainData_extract` needs
  a chain with an interior vertex (n ≥ 3), and
  `Graph.exists_adjacent_degree_two_pair`'s counting `nlinarith` needs
  `D ≥ 6` — whether that lemma is even *true* at `D = 3` is the open
  recon question. Salvageable-but-new-combinatorics; cost unknown until
  the recon.
- **S3. Full KT Lemma 3.4** (rigid-tightness *equality*,
  `|X−e| = D(|V(X)|−1)`): only the upper-bound/basis form is formalized;
  the blocker recorded in `deficiency.tex` (needs `thm:def-eq-corank`)
  has since gone green, so the missing direction is now cheap; the
  genuinely unbuilt piece is a vertex-induced-subgraph-from-edge-set
  construction (`notes/Phase19.md`). Small strengthening; also fixes the
  stale blueprint remark.

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

- **S1:** `lean_references`-grade liveness re-check + the exact
  blueprint-pin repoint list before any deletion commit.
- **G1:** spike the two chokepoints — reprove one `MeetHodge.lean` decl
  metric-free, and reroute the genericity engine onto the maximal-minor
  twin — before sanctioning the ~30-file mechanical sweep.
- **G2:** is `Graph.exists_adjacent_degree_two_pair` true at `D = 3`
  (smarter count) or false (Case-III degeneration essential)? Decides
  adapt-Case-III vs. formalize-the-pin-collinear-route.
- **G3:** can the Phase-30 product route replace JJ 2010's
  algebraic-independence-over-ℚ genericity layer, or does the "almost
  all" form genuinely need alg-indep back? (Bears on whether RELAX's
  simplification survives the strengthening.)
- **L1:** dependency check of JJ 2008 Thm 5.3 + Lemma 5.2 against the
  formalized sparsity/Laman surface (Phase 1–2 API vs. their counting).

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

The user adjudicates the tiers (which tracks, what order). Then the
opening commit mints the phase number per `PHASE-BOUNDARIES.md` *When
this commit opens a phase*, seeds `notes/PhaseN.md` from the chosen
tracks' entries here, and this note flips to a thin pointer at that work
log. Recommended opening slice if the user wants a default: **S2** (the
smallest verified-route item) or **S1** (bounded, already
inventory-backed); L1 is the flagship if the phase should lead with new
mathematics.
