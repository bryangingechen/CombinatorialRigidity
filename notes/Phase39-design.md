# Phase 39 — PENCIL opening recon (R1–R3 design record)

**Status: live recon record** (the `notes/<topic>-design.md` pattern,
`notes/CLAUDE.md` *One canonical home per content type*). Written by the
2026-07-23 opening-recon design pass against `notes/Phase39.md`'s
*Opening recon questions*. Once the phase's build (or close) decisions
land in `notes/Phase39.md`, closed arcs here compress to verdicts.

Methods used: KT primary source (`.refs/`
katoh-tanigawa-2011-molecular-conjecture.pdf; page pointers verified
against the printed headers this session), landed definition bodies
(files cited per claim), a typechecked statement spike (`lake env
lean`, scratch only, 2026-07-23 — the candidate Lean shapes below are
transcribed from it verbatim), and exact-rational rank experiments on
the d = 3 body-hinge model (method in §R2; scripts were scratch-only,
the configurations and results are recorded below).

## Verdict summary

- **R1 — CONFIRMED, statement pinned.** The panel-side pencil statement
  needs the Phase-35 containment model (`HasCoplanarPanelRealization`)
  plus a per-body concurrency pin through a homogeneous point; the meet
  model cannot express it (coincident panels are *forced* for some
  graphs, see the collapse finding). The two sides are projectively
  dual on-stratum via the landed `screwComplementIso`, modulo one new
  transport lemma (first buildable leaf). The stratum is satisfiable
  for every spanning multigraph. **Surprise:** for some graphs (K4,
  K3,3, the 3-path theta on 5 vertices) the molecular pencil stratum
  *collapses* to the all-atoms-coplanar locus — and the planning note's
  "all-atoms-coplanar is known rank-deficient" is **false in the
  body-hinge model for those graphs** (it is a bar-joint-side fact;
  see §R2). No refutation arises from the collapse.
- **R2 — conjecture survives every test.** Exact-rational rank
  experiments: pencil-generic realizations attain the full target rank
  on every graph tested, including graphs with four degree-3 bodies at
  the tight minimal-0-dof count (subdivided K4) and five degree-4
  bodies (subdivided K5), and including the forced-coplanar graphs.
  The deep all-atoms-coplanar locus is rank-deficient exactly when
  `2|E| < 3|V| − 3`, with deficit `(3|V| − 3) − 2|E|` in every run —
  so "generic-in-stratum" bookkeeping is genuinely needed for sparse
  graphs, as the planning note anticipated.
- **R3 — KT's route does NOT survive verbatim; the conjecture is not a
  warmup.** The per-case ledger (§R3): Lemma 6.2 and Lemma 6.8 / Case
  II survive with pencil-pinned hinge choices; Lemma 6.13's Claim-6.12
  extensor-span argument fails by **exactly one dimension** (span 6 →
  5, numerically confirmed) when both chain ends have degree ≥ 3; the
  Case-I connecting-hinge glue (Lemma 6.3/Claim 6.4) and even the outer
  Theorem-5.6 strip-and-extend layer break *earlier*, because the
  containment-freedom KT spends there ("any line in the panel meet")
  is consumed by cross-body point incidences the pencil pin adds.
  A grounded refutation was **not** found; a proof needs new
  mathematics in three named places (§Decomposition).

**Recommendation.** The phase should not proceed on the "warmup, no
new carrier material" premise. Either (a) proceed with the pinned
statement and the §Decomposition plan, treating the three open cores
as research-scale obligations, or (b) close the phase with this recon
as its deliverable (statement pinned + numerically supported + route
obstruction mapped), leaving the conjecture open. **User adjudication.**

---

## R1 — statement and satisfiability

### The pinned statement (informal)

Fix d = 3 (grade k = 2, `D = screwDim 2 = 6`). A **pencil panel
realization** of a spanning multigraph `G` is a body-hinge framework
`F` on `G` together with, per body `v`, a nonzero homogeneous *normal*
`n_v ∈ K⁴` and a nonzero homogeneous *point* `q_v ∈ K⁴` with
`q_v ⬝ n_v = 0`, such that every link's supporting extensor is nonzero,
lies in both endpoint panels (`n_u^⊥`, `n_v^⊥`), **and passes through
both endpoint points** (`q_u`, `q_v`). The **pencil conjecture**: every
spanning multigraph has a pencil panel realization attaining the
deficiency rank, i.e. `F.RankHypothesis (G.deficiency 3)` — the exact
analogue of `theorem_55_6_multigraph_d3` with the realization predicate
strengthened.

Molecular reading (`G²`/bond-star form): there exist `ends` and centres
`c` with `(molecularOfCentres G ends c).RankHypothesis (G.deficiency
3)` and, at every atom `v`, a plane through `c v` containing all of
`v`'s neighbours (bond-star coplanarity). Concurrency is automatic on
this side; only the coplanarity conjunct is added relative to the
landed `exists_molecular_rankHypothesis_generalPosition`
(`Molecular/Molecule/Modelling.lean`) — but note that theorem's
general-position conjunct (`SimpleGraph.IsGeneralPositionPlacement`,
no 4 coplanar atoms) is **incompatible** with the pencil stratum
(a degree-3 bond-star coplanarity *is* four coplanar atoms), so the
pencil molecular statement drops it; consequences for the `G²`
dictionary are in §R2 (*the coplanar caveat*).

### Candidate Lean shapes (typechecked spike, 2026-07-23)

The following typechecked against the landed carriers with `lake env
lean` (no errors/warnings); signatures are honest, names tentative:

```lean
/-- Projective dual of `ExtensorInPanel`: the screw element passes
through the homogeneous point `q`. -/
def ExtensorThroughPoint {k : ℕ} (C : ScrewSpace K k) (q : Fin (k + 2) → K) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → K,
    C.val = extensor p ∧ q ∈ Submodule.span K (Set.range p)

def HasPencilPanelRealization {k : ℕ} (G : Graph α β) (F : BodyHingeFramework K k α β)
    (normal : α → Fin (k + 2) → K) (point : α → Fin (k + 2) → K) : Prop :=
  HasCoplanarPanelRealization G F normal ∧
  (∀ v ∈ V(G), point v ≠ 0) ∧
  (∀ v ∈ V(G), point v ⬝ᵥ normal v = 0) ∧
  (∀ e u v, G.IsLink e u v →
    ExtensorThroughPoint (F.supportExtensor e) (point u) ∧
    ExtensorThroughPoint (F.supportExtensor e) (point v))
```

Target statement: `∀ G` spanning (multigraph, fresh-edge-supply binder
as in `theorem_55_6_multigraph`), `∃ F normal point,
HasPencilPanelRealization G F normal point ∧ F.RankHypothesis
(G.deficiency 3)`.

Design notes on the shape (each a deliberate choice, revisitable):

- `ExtensorThroughPoint` mirrors `ExtensorInPanel`'s witness shape
  (`Molecular/RigidityMatrix/Basic.lean:291`) including its
  built-in decomposability and its degenerate `C = 0` admissibility;
  nonzero-ness rides the realization's separate conjunct, as there.
  Since the realization forces `C ≠ 0`, `span (range p)` is the
  well-defined support of `C` and the predicate is honest.
- The `point v ⬝ᵥ normal v = 0` incidence is *forced* at any body with
  a genuine hinge (the hinge's 2-dim span contains `q_v` and sits in
  `n_v^⊥`); including it as a conjunct makes isolated bodies honest
  and the stratum self-dual on the nose.
- Concurrency of two coplanar lines is projectively automatic, so the
  pin only bites at bodies of degree ≥ 3 — as the planning note said —
  *and* the homogeneous `point` correctly admits concurrency points at
  infinity (two parallel hinge lines in a panel), which the affine
  reading would miss.

### Containment model confirmed necessary

Two independent confirmations of the planning note's suspicion:

1. **Forced coincidence.** For K4 the panel-side pencil conditions
   force every panel to contain all four points `q_v`, hence (points
   spanning a plane) all four panels *coincide* — expressible only in
   the containment model (`rem:coplanar-conventions` freedom, KT Lemma
   5.3's coincident-panel trick, `notes/Phase35.md`).
2. **Two-body multigraph.** Two bodies with 3 parallel edges: distinct
   panels force all three hinges equal to the meet line (rank ≤ 5 < 6
   = target), while the coincident-panel pencil (common plane, common
   point, three distinct pencil lines) attains 6: the spans of two
   distinct lines' extensors already intersect trivially, so the
   stacked `C_i^⊥` row spaces fill `K⁶`. (Same mechanism as KT Lemma
   5.3, p. 670, with the pencil pin satisfied for free.)

### Projective duality on-stratum

The landed polarity `screwComplementIso`
(`Molecular/Molecule/Duality.lean:69`) already carries the framework
transport (`molecularOfCentres_mapExtensor_screwComplementIso`,
`Duality.lean:110`) and the extensor-level identity
`screwComplementIso_lineExtensor` (join of poles ↦ meet of panels).
The pencil stratum is **self-dual**: the polarity swaps
`(normal, point) ↦ (point, normal)` per body. What is missing is one
predicate-transport lemma (first buildable leaf, W0 in
§Decomposition):

```
ExtensorThroughPoint C q ↔ ExtensorInPanel (screwComplementIso C) q
```

(and its inverse-direction sibling), buildable from the landed
join=meet duality `extensor_join_proportional_complementIso_meet`
(`Molecular/Meet.lean:1876`) and the `panelSupportExtensor` containment
facts (`Molecular/AlgebraicInduction/PanelLayer.lean:664`). With it,
the molecular-side and panel-side pencil statements transport into one
another along the landed `BodyHingeFramework.mapExtensor` machinery
exactly as the Phase-25 duality did for the unpinned statements.

### Satisfiability — and the collapse finding

The stratum is nonempty for **every** graph: the totally-coincident
witness (all panels one plane `Π`, all points one `q ∈ Π`, hinges
distinct lines of that one flat pencil) satisfies
`HasPencilPanelRealization` for any `G` (nowhere near target rank, but
satisfiability per se is trivial). Molecular side: any placement with
all atoms coplanar and distinct satisfies bond-star coplanarity.

**The collapse finding (new; constrains what "generic in stratum" can
mean).** For graphs with rich degree-≥3 adjacency the *whole* molecular
pencil stratum degenerates:

- **K4**: bond-star coplanarity at any vertex = all four atoms
  coplanar. Stratum = all-coplanar locus exactly.
- **K3,3**: the three stars of one side force the other side's plane
  and vice versa; away from collinear-triple degeneracies the stratum
  is again the all-coplanar locus.
- **theta(2,2,2)** (two degree-3 vertices joined by three length-2
  paths): the two stars share all three interior atoms; both hub atoms
  are forced into the interior atoms' plane — all-coplanar again.
- Any 3-regular graph containing a triangle collapses (the star of a
  triangle vertex contains the triangle).

By contrast, for sparse graphs (the minimal-`k`-dof regime KT's
induction actually walks, average degree < 2.4), degree-3 vertices are
separated by degree-2 chains, each star imposes one independent
codimension, and the stratum is far larger than the all-coplanar locus
— there "generic in stratum" is meaningful and the all-coplanar locus
is genuinely *deeper* (and rank-deficient, §R2). The pinned statement
is existential, so the collapse does not change the statement; it
kills any hope of a *uniform* "pencil-generic ⇒ full rank" claim
(false for sparse graphs' coplanar locus, vacuous-but-true for K4's).

## R2 — truth sanity (exact-rational rank experiments)

Method: molecular model over ℚ. Hinge extensor for edge `uv` =
`ĉ_u ∧ ĉ_v` (Plücker in Λ²ℚ⁴, `ĉ = (c,1)`); motions = `{S : V → ℚ⁶ |
S_u − S_v ∈ span C_e}`; `rank R = rank A − |E|` for the stacked system
`S_u − S_v − t_e C_e = 0`. Exact fraction Gaussian elimination (no
floating point). Pencil-stratum samples parametrized directly (star
planes chosen, neighbours placed inside them); several independent
random samples per configuration. Targets = `6(|V|−1) − def(G̃)`,
cross-checked against fully-generic-placement baselines (which realize
the target by the landed `molecular_conjecture` / Tay count).

| configuration | rank | target `6(|V|−1)` |
|---|---|---|
| K4 generic | 18 | 18 |
| K4 all-coplanar (= its entire pencil stratum) | **18** | 18 |
| K3,3 generic | 30 | 30 |
| K3,3 all-coplanar (= its pencil stratum) | **30** | 30 |
| theta(2,2,2) generic | 24 | 24 |
| theta(2,2,2) all-coplanar (= its pencil stratum) | **24** | 24 |
| theta(3,3,2) generic baseline (7 vertices, 8 edges, two deg-3 hubs) | 36 | 36 |
| theta(3,3,2) pencil-generic, 5 samples | **36** | 36 |
| theta(3,3,2) all-coplanar (deep stratum) | 34 | 36 |
| subdivided K4 (16 vertices, 18 edges — tight `5|E| = 6(|V|−1)`, four deg-3 bodies) generic | 90 | 90 |
| subdivided K4 pencil-generic, 3 samples | **90** | 90 |
| subdivided K4 all-coplanar (deep) | 81 | 90 |
| subdivided K5 (25 vertices, 30 edges, five deg-4 bodies) generic | 144 | 144 |
| subdivided K5 pencil-generic, 2 samples | **144** | 144 |

Findings:

1. **The conjecture survives every test**, including the first
   interesting cases the phase note asked for (degree-3 bodies:
   theta(3,3,2), subdivided K4) and beyond (degree-4: subdivided K5;
   forced-coplanar dense graphs: K4, K3,3, theta(2,2,2)).
2. **The planning note's negative-data claim is corrected.**
   "All atoms in one common plane is rank-deficient" is a
   **bar-joint-side** fact (a coplanar placement of `G²` is flexible;
   e.g. coplanar K4 bar-joint rank 5 < 6) — it is *false* for the
   body-hinge molecular framework when `2|E| ≥ 3|V| − 3` (K4, K3,3,
   theta(2,2,2) all attain full target *on* the coplanar locus). The
   Whiteley `G²` dictionary does not apply there: the landed dictionary
   route consumes `IsGeneralPositionPlacement` (no four coplanar
   atoms), which every pencil placement with a degree-≥3 atom violates.
   **Consequence:** PENCIL is a body-hinge statement; no `G²`/bar-joint
   corollary follows from it without new dictionary work at degenerate
   placements (out of scope).
3. **Where the coplanar locus *is* deficient, the deficit is exactly
   the spline count.** Writing all hinge extensors into
   `W = Λ²(plane) ≅ K³`, motions decompose as 3 (transversal) + the
   space of per-vertex affine functions on the plane agreeing across
   each edge's line (a vertex-based Maxwell-lifting space); counting
   gives rank deficit ≥ `(3|V| − 3) − 2|E|` when positive, and every
   run met it with equality (theta(3,3,2): 2; subdivided K4: 9).
   This grounds the "generic-in-stratum only" bookkeeping: for sparse
   graphs the deep coplanar locus really is bad, and any pencil proof
   must stay away from it.

Caveat: numerics are recon evidence, not proof; samples cover the
parametrized open part of the stratum's incidence variety (star planes
free, neighbours inside), which is the component the conjecture is
about.

## R3 — which KT case breaks

Notation: KT pointers are to the `.refs` copy (printed page headers);
landed pointers to `Molecular/AlgebraicInduction/`. The induction
maintains, per KT, a *generic nonparallel* realization for simple
graphs (§5.1, p. 668) — the landed formalization reworks that device
into seed-polynomial genericity (Phase 21b/22). A pencil analogue must
carry its own in-stratum genericity; that cross-cutting obligation is
listed once in §Decomposition and omitted from the per-case ledger.

**Ledger** (pencil status of each KT case):

- **Base cases** (|V| = 2, p. 671; Lemma 5.3 pp. 669–670; Lemma 5.4
  cycles). **Survive.** Lemma 5.3's coincident-panel pair: choose the
  two distinct hinges through a common point of the shared panel —
  the pin is free (§R1 two-body example). Cycles are all-degree-2:
  the pencil condition is vacuous (concurrency of two coplanar lines
  is automatic); KT's realization is already pencil.
- **Not 2-edge-connected** (Lemma 6.1, p. 672;
  `case_cut_edge_realization_gen`). **Repairable, new positioning
  lemma.** The new cut hinge `Π₁(u) ∩ Π₂(v)` must pass through the
  endpoint pins `pt₁(u)`, `pt₂(v)` when those bodies have degree ≥ 3 —
  two incidence conditions between the two component realizations,
  satisfiable by repositioning one component (landed projective
  invariance gives the transport; freedom 15-dim vs 2 conditions) plus
  a nondegeneracy argument. Moderate, not structural.
- **Nonsimple / parallel-pair contraction** (Lemma 6.2, pp. 673–674;
  `case_I_realization_nonsimple_gen`). **Survives.** The two parallel
  hinges are chosen as two distinct lines through the merged body's
  pin `pt(v*)` inside the shared panel; every other body's hinge lines
  are untouched.
- **Case I, proper rigid subgraph** (Lemma 6.3 + Claim 6.4,
  pp. 674–675; Lemma 6.5, p. 676; `case_I_realization_all_k`,
  `case_I_realization_h65`). **Breaks structurally — first open
  core.** Each connecting edge `uv ∈ δ(V′)` gets hinge
  `Π₂(u) ∩ Π₁(v)`; the pencil pin demands it pass through *both*
  `pt₂(u)` and `pt₁(v)`, i.e. `pt₂(u) ∈ Π₁(v)` and `pt₁(v) ∈ Π₂(u)` —
  two incidences per connecting edge, unbounded in number, *not*
  producible by genericity (genericity makes them fail) nor by the
  15-dim relative repositioning. Keeping the contracted realization's
  connecting hinges unchanged instead forces, at any `V′`-body carrying
  ≥ 2 connecting edges, `pt₁(v) = pt₂(v*)` and `Π₁(v) = Π₂(v*)` — a
  coincidence cluster that demands a *prescribed-boundary* pencil
  realization of `G′` (new IH strengthening; not obviously false —
  the containment model tolerates coincidences and the dense-collapse
  numerics attain full rank — but new mathematics). The Lemma-6.5
  sub-case has an extra wrinkle: its free plane `Π°` must contain
  `line(pt(a), pt(b))`, which collides with the `Π° ⊉ Π(a) ∩ Π(b)`
  requirement exactly when `ab ∈ E` and `pt(a) ≠ pt(b)` both lie on
  the meet.
- **Case II, `k > 0` splitting** (Lemma 6.8, pp. 677–679, eq. (6.12);
  `case_II_realization_all_k`). **Survives with the pin.** The free
  hinge `L ⊂ Π(a)` becomes `L` in the pencil of `(pt(a), Π(a))` when
  `deg_G(a) ≥ 3` (note `pt(a) ∈ q(ab)`, so the re-inserted body `v`
  takes point `pt(a)` and panel `Π(a)`, and both its hinges pass
  through it); the (6.16) block-triangular rank count needs only
  `rank r(L) = D − 1`, true for any genuine line. Bodies `b` keep
  their hinge lines verbatim. KT's closing Lemma-5.2 nonparallel
  rotation would break the pin at `b`, but the containment-model
  formalization does not perform it — only the carried genericity
  conjunct (cross-cutting obligation) replaces it.
- **Case III, `k = 0`** (Lemma 6.10 pp. 680–691; general-`d` Lemma
  6.13 pp. 692ff; landed `case_III_candidate_dispatch` +
  `case_III_realization`, `CaseIII/Realization.lean`, with the span
  argument as `exists_complementIso_ne_zero_of_homogeneousIncidence`
  (+`_gen`), `RigidityMatrix/Claim612.lean`). **The span inequality is
  the precise casualty — second open core.** The three candidates'
  freedoms (6.42, p. 690) are `L ⊂ Π(a)`, `L′ ⊂ Π(b)`, `L″ ⊂ Π(c)`.
  Under the pin: `L` stays fully free (`v`, `a` are the chain's
  degree-2 interior — *the pinning the phase note worried about does
  not occur at the re-inserted bodies at all*), but `L′`, `L″` are
  pinned to the pencils of `(pt(b), Π(b))`, `(pt(c), Π(c))` whenever
  the chain ends `b`, `c` have degree ≥ 3. Claim 6.12's span (6.45)
  then degrades: a flat pencil's extensors span 2 (not the panel's 3),
  and the shared hinges `q(ab) ∈ Λ²Π̂(a) ∩ pencil(b)`,
  `q(ac) ∈ Λ²Π̂(a) ∩ pencil(c)` force
  `dim(Λ²Π̂(a) + pencil(b) + pencil(c)) ≤ 3 + 2 + 2 − 1 − 1 = 5 < 6`.
  Numerically confirmed on random incidence-respecting configurations:
  KT's unpinned span = 6, the pencil-pinned span = 5, always (and 4 if
  one pins all three). The escape hatch for the obstruction vector `r`
  (the Claim-6.11 redundancy row combination, eqs. (6.24)/(6.44)) is
  exactly 1-dimensional; whether `r` avoids it pencil-generically is
  open (the R2 numerics show the *rank* survives on every tested graph,
  so either some candidate always works or full rank arrives without
  any of the three 6×6 minors — the dispatch is sufficient, not
  necessary). General-`d` remark: Lemma 6.13's chain `v₀v₁…v_d` has
  degree-2 interior, so the same picture holds — only the two chain
  *ends* get pinned; the shortfall arithmetic in general `d` was not
  computed (PENCIL is a d = 3 question).
- **Outer Theorem-5.6 layer** (strip-and-extend, p. 670;
  `theorem_55_6_multigraph`, extension via
  `exists_extensor_in_two_panels_grade`). **Breaks — third open
  core.** A re-added edge `uv ∉ E(G′)` needs a hinge in
  `Π(u) ∩ Π(v)` through `pt(u)` *and* `pt(v)` — i.e.
  `line(pt(u), pt(v)) ⊆ Π(u) ∩ Π(v)`, the same cross-body incidences
  as Case I, which the stripped realization does not provide. KT's
  projective move (make all panel meets nonempty) is too weak. The
  pencil analogue must either prove the statement on the full graph
  directly or strip only edges whose re-addition is pencil-compatible.
  (The R2 numerics on K4 — full pencil rank with all six edges live —
  show the *statement* is fine; it is the strip *route* that dies.)

**Direct R3 answers.** (a) Lemma 6.13's extensor-span argument does
*not* survive as stated: not because the *new* (re-inserted) hinge is
pinned through the split body's point — it is not; degree-2 concurrency
is free — but because the two *chain-end* candidates' hinge choices
are pinned, shrinking Claim 6.12's span from 6 to 5. (b) The first
inequality that consumes panel-only freedom, in the order KT's proof
runs for a general multigraph, is already the Theorem-5.6 extension
step (p. 670); within the Theorem-5.5 induction it is Claim 6.4
(p. 675, the Case-I genericity glue); the deepest and sharpest is
Claim 6.12 / eq. (6.45) (pp. 690–691) with the quantified 1-dim
shortfall.

## Decomposition (if the phase proceeds)

Buildable now, in dependency order (W0–W2 are compiler-ready against
landed machinery; W3+ carry the open cores):

- **W0 — statement layer + self-duality.** Land
  `ExtensorThroughPoint`, `HasPencilPanelRealization` (spike shapes
  above), the predicate-transport lemma
  `extensorThroughPoint_iff_extensorInPanel_screwComplementIso` (from
  `extensor_join_proportional_complementIso_meet`), and the stratum
  self-duality
  (`mapExtensor screwComplementIso` carries pencil realizations to
  pencil realizations with `(normal, point)` swapped). Open the
  blueprint chapter on these nodes (per the phase-open deferral).
- **W1 — base cases.** Pencil Lemma 5.3 (two distinct pencil lines in
  a coincident panel; rank D via the landed span mechanics), pencil
  cycles (KT Lemma 5.4's realization is already pencil — check and
  wrap), the two-body/three-edge worked example as a nonvacuity
  witness (mirrors `AlgebraicInduction/Nonvacuity.lean`).
- **W2 — the two-pencil extension lemma.** The honest replacement for
  `exists_extensor_in_two_panels_grade`: a nonzero extensor in both
  panels and through both points exists **iff** `pt(u) ∈ Π(v) ∧
  pt(v) ∈ Π(u)` (+ degenerate/coincident cases) — stated with its
  true hypotheses, quantifying exactly the Case-I/outer-layer
  obligations rather than hiding them.
- **W3 — open core 1 (outer layer).** Pencil Theorem-5.6 analogue:
  either a pencil-compatible strip (strip only within stars, keeping
  re-added edges' endpoints hinge-adjacent), or restate the target on
  minimal-`k`-dof graphs first and add edges *inside* the induction.
  Needs a real idea; W2's iff shows exactly what must be arranged.
- **W4 — open core 2 (Case I glue).** Prescribed-boundary pencil
  realizations (the coincidence-cluster route) or an IH strengthened
  with boundary pencil data. Research-scale; numerically explorable
  first (the collapse-tolerant full ranks of K4/K3,3 suggest
  coincidence clusters are survivable).
- **W5 — open core 3 (Claim 6.12 shortfall).** Either a genericity
  argument keeping the obstruction vector `r` off the 1-dim escape
  line (new in-stratum genericity device — the cross-cutting
  obligation; note the landed seed-polynomial device parametrizes free
  normal coordinates, while the pencil stratum's `(normal, point)`
  seeds live on the incidence quadric `q ⬝ n = 0`, which is rationally
  parametrizable, so a polynomial device is plausible but new), or a
  fourth candidate construction supplying the missing dimension.
  Numerically explorable per-instance before committing to a route.

## Higher-`d` note (orientation only, per the phase-open decision)

The pencil stratum generalizes: hinges at a body contained in a
hyperplane *and* containing a common point; the polarity still swaps
the two conditions, so the stratum is self-dual at every `d`, and the
chain analysis carries over (only chain ends get pinned). The
between-strata hierarchy of `notes/IdeaBacklog.md` Tier A (hinges
in/through a common `j`-flat) meets the same three open cores; nothing
about `d > 3` looks easier. Not an R1–R3 deliverable; recorded to
close the "may note whether the question generalizes" flag.

## Citations (verified this session against the `.refs` copy)

- Katoh, Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011). Pointers read and verified this pass:
  §5.1 nonparallel/generic device p. 668; Lemma 5.2 p. 669; Lemma 5.3
  pp. 669–670; Theorem 5.5/5.6 and the strip-extend proof p. 670;
  molecular duality discussion + Corollary 5.7 p. 671; case split
  p. 671; Lemma 6.1 p. 672; Lemma 6.2 pp. 673–674; Lemma 6.3 + Claim
  6.4 pp. 674–675; Lemma 6.5 + Claim 6.6 p. 676; Lemmas 6.7/6.8,
  eq. (6.12), Claim 6.9 pp. 677–679; §6.4/Lemma 6.10 sketch
  pp. 680–682; Claim 6.11 p. 684; eqs. (6.29)/(6.30) p. 686;
  eqs. (6.31)–(6.33) p. 687; M₁/M₂/M₃ + eq. (6.42) + Claim 6.12
  p. 690; eqs. (6.44)/(6.45) + the four-point span proof p. 691;
  §6.4.2 Lemma 6.13 chain statement + eqs. (6.46)–(6.53) pp. 692–693.
- The Maxwell-lifting reading of the coplanar deficiency (§R2.3) is a
  classical parallel-drawing/lifting correspondence (Maxwell; see
  Whiteley, *Matroids and rigid structures*, in *Matroid Applications*,
  1992, for the standard treatment) — used here only as a counting
  heuristic confirmed numerically, not as a cited theorem.
