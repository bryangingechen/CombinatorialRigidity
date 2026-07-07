# Phase 25 — projective duality + the molecule modelling equivalence: layer design recon

**Status: CLOSED** — Phase 25 closed 2026-07-06 with all 12 chapter nodes
green; the closed recon arcs below are compressed to cited verdicts per
`notes/CLAUDE.md` *One canonical home per content type* (the blow-by-blow is
in git history; the landed proofs are the Lean sources + the chapter prose).
**Still live for Phase 26:** §2.2 (the Cor-5.7 assembly plan), §2.6 (the
statement shapes Phase 26 consumes), and flags F4/F5 in §5.

**Source-verified, 2026-07-06** (at the recon): KT §1.2 (pp. 650–651), the
p. 671 reconciliation, §5.1 (the `c`-map and *nonparallel*, p. 668), §5.2
(Theorems 5.5/5.6, pp. 669–670); Crapo–Whiteley 1982 §3.6 (pp. 68–69);
Jackson–Jordán 2008 (Conjectures 2.1/2.2, Theorems 4.1/4.3 and their §3
machinery).

---

## 0. What Phase 25 delivered, in one paragraph

KT §1.2 / p. 671: in `ℝ³` the chain *bar-joint of `G²` ↔ molecular
(hinge-concurrent body-hinge) of `G` ↔ panel-hinge of `G`* lets the
panel-hinge rank theorem (Thm 5.6, Phase 23) speak about the 3-dimensional
generic bar-joint rank of the square graph (Phase 24's `genericRank`),
producing Corollary 5.7: `r(G²) = 3|V| − 6 − def(G̃)` for `G` simple of min
degree ≥ 2 (Jackson–Jordán's statement; KT resolve the conjecture feeding
it). Phase 25 owns the two links of the chain, **delivered at the
rank/motion-space level** (§2); Phase 26 assembles.

---

## 1. OD-25-1 — the projective-invariance route (`thm:projective-invariance`)

**Verdict (landed as designed).** Crapo–Whiteley 1982 §3.6's proof is
exactly "a projective transformation (or polarity) induces an invertible
linear map on the screw space; applying it bodywise carries motions to
motions" — CW extend the same sentence verbatim to correlations/polarities.
That formalizes as the **extensor-transport family**
(`BodyHingeFramework.mapExtensor` + `infinitesimalMotions_mapExtensor` and
its finrank/`RankHypothesis`/rigidity/genuine-hinge corollaries, plus the
per-edge nonzero-rescaling sibling `infinitesimalMotions_scaleExtensor`) —
`Molecule/ProjectiveInvariance.lean`, dimension-general. Deliberately NOT a
theory of projective transformations acting on bar-joint frameworks: no
consumer in the program needs one (Thm 5.6 landed projective-move-free; the
p. 671 use is the polarity).

**§1.3 The polarity was already in tree:** `panelSupportExtensor n₁ n₂ =
complementIso (normalsJoin n₁ n₂)` (the 21a/22f meet layer), and under KT
§5.1's convention the panel `Π(v) = {x : x·c(v) + 1 = 0}` has homogeneous
coordinates `(c(v), 1)` = the homogenized pole. So the p. 671 duality is the
transport at `Λ := complementIso` (wrapped into a `ScrewSpace 2 ≃ₗ
ScrewSpace 2` = `screwComplementIso`, `Molecule/Duality.lean`) — no new
duality machinery.

---

## 2. OD-25-2 — the `G²` dictionary at rank level (the central verdict)

### 2.1 Why the realizability-iff shape is a dead end for Cor 5.7

**Verdict (verified against JJ 2008, unchanged).** The step from the
iff-level Molecular Conjecture (JJ Conjecture 2.1) to the rank formula (JJ
Conjecture 2.2 = KT Cor 5.7) is JJ 2008 Theorem 4.3 (p. 10), an induction on
`def(G)` consuming their Theorem 4.1 (the unconditional upper bound
`r(G²) ≤ 3|V| − 6 − def(G)`, via independent 2-thin covers — Lemma 3.1
quoted from [5, Lemma 3.2] and Theorem 3.4 (brick partitions) from [10]),
plus ear attachment, Claim 4.4, and vertex-addition rank lemmas (their
Lemma 3.3, Franzblau's Lemma 4.2(a)). Reaching Cor 5.7 that way means
formalizing the better part of two further JJ papers.

### 2.2 The rank-level route (Phase 26's assembly plan — LIVE)

KT p. 671: Thm 5.6 is a *rank* statement, strictly stronger than the def-0
iff. With the two Phase-25 links carrying motion-space dimensions, Cor 5.7
falls out arithmetically:

- **(≥, attainment)** `exists_molecular_rankHypothesis_generalPosition`
  (Thm 5.6 general-position form + polarity transport + pole bridge) gives a
  molecular realization at `dim Z = 6 + def(G̃)` with centres in general
  position up to order 4; the dictionary
  (`molecular_finrank_motions_eq_square_ker`) exhibits a bar-joint placement
  `c` of `G²` with `dim ker R(G², c) = 6 + def`, i.e. rank `3|V| − 6 − def`;
  `genericRank` dominates the rank at any placement (matroid glue, Phase 26).
- **(≤, upper bound)** at a placement simultaneously generic (Phase 24) and
  in general position (`exists_isGenericPlacement_isGeneralPositionPlacement`),
  `genericRank = rank R(G², p)` (`genericRank_eq_finrank_span`); the
  dictionary run in reverse identifies `dim ker R(G², p)` with `dim Z` of the
  molecular framework on `p` (genuine hinges from injectivity); the landed
  genericity-free lower bound `D + def(G̃) ≤ dim Z`
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`) closes
  `genericRank ≤ 3|V| − 6 − def`. **This replaces JJ's whole §3–4.**

### 2.3 The dictionary iso Φ

**Verdict (landed).** The §2.3 trace (Φ : S ↦ (v ↦ vel_{S v} (c v)); the
four ground bricks — skew, line characterization, three-non-collinear kill,
body determination with the sharp coplanar-`K₄` counterexample forcing
order-**4** general position; well-definedness via every `G²`-edge lying in
a closed-neighbourhood clique; injectivity via min degree ≥ 2; surjectivity
via per-clique `∃!` screws) is now canonical in
`Molecular/Molecule/{ScrewVelocity,Dictionary}.lean` and the
`thm:molecular-iff-square-bar-joint` / `lem:screw-determination` chapter
prose; exposition-ledger entry `done`
(`notes/BlueprintExposition.md` §`molecule-modelling.tex`). The
binding-clause check held: `affineSubspaceExtensor ![c u, c v] = extensor
![homogenize (c u), homogenize (c v)]` is the same object the §1.3 polarity
produces from panel normals with last coordinate 1, so the two links compose
with no translation layer. **F5:** Whiteley's [35] (*The equivalence of
molecular rigidity models…*, manuscript 2004) is unpublished; the proof is
the project's own reconstruction from KT's p. 650 sketch + JJ 2008 §2.1,
attributed via \cite{whiteley1999} + JJ 2008 as citable anchors.

### 2.4 The ≥ leg: the general-position form of Thm 5.6 (W6)

**Verdict (landed, route as designed with one substitution).**
`exists_rankHypothesis_isGeneralPosition4` (`Molecule/Theorem56.lean`):
from `RankHypothesis (def)` extract the exact independent-row count, turn it
into a rank polynomial, multiply by the order-four general-position
avoidance polynomial (`exists_generalPosition4_polynomial`,
`Molecule/GeneralPosition4.lean` — last-coordinate variables × leading
square minors, nonzero at moment-curve normals by Vandermonde), and evaluate
at an algebraically-independent-over-ℚ seed; the rank is pinched between the
witnessed count and the genuine-hinge deterministic bound. Two deviations
from the sketch: the avoidance factors are leading *minors* (not
sums-of-squares), and the seed comes from the CaseII
algebraic-independence-seed idiom (not `exists_eval_ne_zero`). The **F1
fix** (the base producer's `ends` failing `hends` on re-added edges) is the
sibling link-recording producer
`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (`Theorem55.lean`).
KT compress this entire strengthening into the word "nonparallel" (p. 671);
exposition-ledger entry `done`.

### 2.5 The ≤ leg: general-position generic placements (W5)

**Verdict (landed).** `SimpleGraph.IsGeneralPositionPlacement` +
`exists_isGenericPlacement_isGeneralPositionPlacement`
(`GeneralPositionPlacement.lean`): Phase 24's interpolation re-run with a
second finite bad-`t` family (one per `≤4`-subset, witnessed at the moment
curve), intersecting both cofinite sets.

### 2.6 Statement shapes Phase 26 will consume — LIVE

Phase 25's two endpoint theorems, as landed:

- **the dictionary** (`Molecular/Molecule/Dictionary.lean`):
  `molecular_finrank_motions_eq_square_ker` — for `G` simple of min degree
  ≥ 2, a `Graph`-carrier `G'` shadowing it (`hshadow : ∀ u v, u ≠ v →
  ((∃ e, G'.IsLink e u v) ↔ G.Adj u v)`, `hends` recording links), and `c`
  in general position up to order 4:
  `finrank (molecularOfCentres G' ends c).infinitesimalMotions
   = finrank (ker (G.square.RigidityMap c))`.
- **the panel ↔ molecular rank carry** (`Molecular/Molecule/Modelling.lean`):
  `exists_molecular_rankHypothesis_generalPosition` — `∃ ends c,
  (molecularOfCentres G ends c).RankHypothesis (G.deficiency 3) ∧` the
  order-four general-position side conditions on `c`.

Phase 26 owns: `SimpleGraph.square`'s `genericRank` glue
(rank-at-a-placement ≤ `genericRank`, via a matroid base transported through
`genericRigidityMatroid_indep_iff`), the `β`-label supply for Thm 5.6
(`hcard : 6(|α| − 1) < |β|`), the carrier bridge (**F4**: `hshadow` vs a
small `SimpleGraph → Graph` constructor — the dictionary is stated so either
works), and the Cor 5.7 statement (additive form; attribute the formula to
Jackson–Jordán 2008, conjecture-resolution to KT).

---

## 3. Leaf decomposition (record — all landed)

All at `d = 3` (`k = 2`) except W1/W2 (dimension-general for free). File
map: `notes/Phase25.md` *Decisions made*.

| # | Leaf | Landed as |
|---|---|---|
| W1 | screw-velocity API | `Molecule/ScrewVelocity.lean` |
| W2 | extensor transport (`thm:projective-invariance`) | `Molecule/ProjectiveInvariance.lean` |
| W3 | square graph | `SquareGraph.lean` |
| W4 | dictionary iso Φ | `Molecule/Dictionary.lean` |
| W5 | general-position placements | `GeneralPositionPlacement.lean` |
| W6 | Thm 5.6, general-position form | `Molecule/{GeneralPosition4,Theorem56}.lean` |
| W7 | dual correspondence + endpoints | `Molecule/{Duality,Modelling}.lean` |

Build order ran as designed: {W2, W3, W5} independent → W1 → W4; W6
independent; W7 last. The two cruxes (W1, W4) carried the genuinely new
geometry; everything else composed on landed machinery.

## 4. Phase-cut and chapter verdicts

**Held.** Single integer phase (7 build slices + the recon, one day); the
chapter's 12 nodes were re-cut to rank-level shapes at the recon and all
went green without a further restate.

## 5. Open decisions / honest flags — final states

- **(F1)** answered + fixed during W6: the base genuine producer's `ends`
  did not record links on re-added edges; fixed by the sibling
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (§2.4).
- **(F2)** bypassed: W1 brick (4) took the explicit cross-product
  `ω`-construction, so no bar-joint triangle-rank lemma was needed.
- **(F3)** settled: the real inner product on `EuclideanSpace ℝ (Fin 3)` is
  `ofLp a ⬝ᵥ ofLp b`; Φ crosses the PiLp boundary with `toLp`/`ofLp`
  (FRICTION idiom).
- **(F4)** **still open, deferred to Phase 26's open** (§2.6): the
  `hshadow`-vs-carrier-bridge choice.
- **(F5)** recorded: Whiteley [35] unpublished; the dictionary proof is the
  project's own reconstruction (§2.3; exposition-ledger entry `done`).
