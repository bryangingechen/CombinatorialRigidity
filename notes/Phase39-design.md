# Phase 39 — PENCIL opening recon (R1–R3 design record)

**Status: live recon record** (the `notes/<topic>-design.md` pattern,
`notes/CLAUDE.md` *One canonical home per content type*). Written by the
2026-07-23 opening-recon design pass against `notes/Phase39.md`'s
*Opening recon questions*; extended by the 2026-07-24 **W3–W5 route
recon** (§W3–W5 route recon below — attack order, the W3 route verdict
with a refutation of candidate (a), the revised W4/W5 route analysis
with new discriminating numerics, and the W3 leaf decomposition with
typechecked signatures). Once the phase's build (or close) decisions
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
- **W3 — open core 1 (outer layer).** *Route settled 2026-07-24, see
  §W3–W5 route recon:* candidate (a) (pencil-compatible strip) is
  refuted; route (b′) — the induction restated on all spanning
  multigraphs, no strip, dispatch via the new min-degree-3 lemma —
  is adopted, with the leaf decomposition W3-L0…L7 pinned there.
- **W4 — open core 2 (Case I glue).** *Route reshaped 2026-07-24, see
  §W3–W5 route recon:* the coincidence-cluster (keep-hinges) route is
  refuted deterministically; the survivor is KT's Claim-6.4
  specialization architecture on the cross-incidence-constrained
  family, with the G′-block witness numerically confirmed (N3) and the
  joint-genericity device + witness generality as the remainder.
- **W5 — open core 3 (Claim 6.12 shortfall).** *Route settled
  2026-07-24, see §W3–W5 route recon:* the escape-line numerics (N2)
  confirm the genericity route — `r` misses the 1-dim line and all
  three candidates individually work, so the target is the
  single-candidate obligation `r ⬝ Λ²Π̂(a) ≠ 0` pencil-generically via
  the in-stratum genericity device (the cross-cutting obligation; the
  landed seed-polynomial device parametrizes free normal coordinates,
  while the pencil stratum's `(normal, point)` seeds live on the
  incidence quadric `q ⬝ n = 0`, rationally parametrizable — the N2
  sampler is the parametrization blueprint). No fourth candidate
  needed on current evidence.

## W3–W5 route recon (2026-07-24)

Commissioned by the coordinator per `notes/Phase39.md` *Hand-off*: settle
the attack order across the three open cores, pick W3's route, decompose
the first core into buildable leaves with pinned signatures. Methods:
KT primary source re-read (pp. 670, 674–675, 684, 690–691 against the
`.refs` copy), landed definition bodies (`Deficiency.lean`,
`Induction/Operations.lean`, `Induction/ForestSurgery/Reduction.lean`,
`AlgebraicInduction/Theorem55.lean`, `Molecule/Pencil.lean`), three new
exact-rational experiments (N1–N3 below, same model as §R2), and a
typechecked `lake env lean` signature spike (scratch, not committed; the
leaf shapes below are transcribed from it verbatim).

### Verdicts

1. **Attack order: W3 → W5 → W4.** W3 first because under the chosen
   route it is buildable *now* against landed machinery and its product
   is the induction skeleton that turns W4 and W5 from prose cores into
   pinned Lean interface-hypotheses (the project's carry-the-crux idiom).
   W5 second: its route is now numerics-confirmed (N2) and bounded — a
   single-candidate genericity argument — and it forces building the
   **in-stratum genericity device** in its simplest habitat. W4 third: it
   consumes that same device on *constrained* substrata plus a
   witness-generality question that is the genuine research remainder, so
   it benefits from everything W3/W5 settle.
2. **W3 route: candidate (a) is REFUTED; candidate (b) is adopted in a
   sharpened form (b′)** — *no strip at all*: restate the induction
   target on **all spanning multigraphs** and let KT's own case moves
   carry every edge. Details and the refutation below.
3. **W5: the genericity escape is CONFIRMED viable (N2).** On the exact
   Case-III habitat, the obstruction vector `r` misses the 1-dim escape
   line in every exact-rational sample — indeed **each of the three KT
   candidates works individually**, so the route is: prove
   `r ⬝ Λ²Π̂(a) ≠ 0` pencil-generically (candidate `M₁` alone, the fully
   unpinned one) via the in-stratum genericity device. No fourth
   candidate construction is needed on current evidence.
4. **W4: the keep-the-contracted-hinges route (this doc's earlier
   "coincidence cluster" suggestion) is REFUTED as a uniform mechanism**
   (deterministic motion count on a 6-body instance, below) — but KT's
   *actual* Claim-6.4 architecture (re-choose connecting hinges, prove
   the hybrid block's rank by an in-family specialization; KT p. 675)
   survives in **constrained-family form**, and its G′-block witness
   exists on the discriminating instance (N3, rank 18/18). W4's
   remainder: the constrained-family joint-genericity device + witness
   generality for arbitrary boundary patterns.

### W3 — why route (a) dies, and what (b′) is

**Route (a) as stated cannot start.** "Strip only within stars, keeping
re-added edges' endpoints hinge-adjacent" requires every removed edge's
endpoints to stay adjacent in `G′` — impossible in a simple over-braced
graph. Witness K4 (`def = 0`): its minimal-0-dof spanning subgraphs are
exactly its three 4-cycles (a 4-edge spanning subgraph is a 4-cycle or a
triangle-plus-pendant, and the latter has `def = 1`; 5- and 6-edge
subgraphs contain spanning 4-cycles, so their bases can avoid a whole
edge fiber — not minimal), and the two stripped diagonals' endpoints are
nonadjacent in the surviving cycle.

**The repair is also dead.** The natural repair — prescribe the W2
cross-incidences at the removed pairs on `G′`'s realization, then extend
by `exists_extensor_two_pencils` + motion monotonicity — *collapses
rank*. On K4: the four cycle edges' cross-incidences are forced anyway
(W2 necessity, `dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`),
so prescribing the two diagonal pairs makes **every panel contain all
four points**. If the homogeneous points span a 3-dim `W ⊆ K⁴`, every
(3-dim) panel contains `W`, hence *equals* `W`: all panels coincide and
every hinge extensor lies in the fixed 3-dim `Λ²W`. A C4 framework with
all four extensors in one `Λ²W` has motions of dim ≥ 6 + 3 − 2 = 7
(tree freedom 3, the one non-tree edge imposes only 2 conditions inside
`Λ²W`), so rank ≤ 24 − 7 = **17 < 18**; points spanning ≤ 2 dims force
all hinges equal (rank ≤ 5) or coincident-point degenerations that are
worse. N1 confirms: all-coplanar C4 rank = 17 in every sample (the
§R2 spline deficit `(3·4−3) − 2·4 = 1`), generic C4 = 18. Since
strip-extend transfers rank by motion monotonicity *alone* (re-added
edges contribute nothing — KT p. 670's own argument shape), a 17-rank
`G′` can never deliver an 18-rank K4. **Conclusion: on the pencil
stratum, re-added edges must contribute rank** (K4's own diagonals do:
its full pencil stratum attains 18, §R2), **so any route factoring
through "realize a proper spanning subgraph at full target rank, then
extend" is unsound. The extra edges must be carried through the
induction itself — route (b′).**

**Route (b′): the induction target is every spanning multigraph; the
strip disappears.** The keystone that makes KT's case dispatch total
*without minimality* is a new combinatorial lemma:

> **W3-L1 (min-degree-3 dispatch).** A loopless multigraph on ≥ 3
> bodies with every degree ≥ 3 has a proper rigid subgraph.
>
> *Proof route (elementary, against landed bricks):* pick a
> minimum-degree vertex `v` (degree `δ ≥ 3`). The handshake bound gives
> `|E| − δ ≥ δ(|V| − 2)/2 ≥ 3(|V| − 2)/2`, so the fibers of the edges
> avoiding `v` number `(D−1)(|E| − δ) ≥ (3(D−1)/2)(|V|−2) > D(|V|−2)`
> (true for `D > 3`), exceeding the sparsity cap on `V ∖ {v}` — the set
> is dependent in `M(G̃)` (`matroidMG_indep_iff`), hence contains a
> circuit, whose induced subgraph is rigid
> (`circuit_induces_isRigidSubgraph`, KT Lemma 3.4, landed), spans ≥ 2
> vertices (looplessness), and avoids `v` — proper. ∎

Consequences for the dispatch (all against landed vocabulary):

- *No proper rigid subgraph* ⟹ some vertex has degree ≤ 2; with 2EC
  (`two_le_degree_of_twoEdgeConnected`, landed) that degree is exactly 2
  — the chain-arm entry, with **no minimality hypothesis anywhere**.
- *Nonsimple* needs no arm of its own: a parallel pair on `{u,v} ⊊ V` is
  a proper rigid subgraph (`isKDof_zero_of_parallel_pair`, landed), so
  parallel classes route through the contract arm — which is where KT's
  Lemma 6.2 lives anyway (`case_I_realization_nonsimple`). The split arm
  gets simplicity for free (loopless + no parallel pair), mirroring the
  landed `simple_of_isMinimalKDof_of_noRigid` with looplessness supplied
  by the loop arm instead of minimality.
- *Minimality-vs-redundancy bookkeeping* drops out of the skeleton. Two
  facts sharpen the arms' burden (derived this recon from the circuit
  argument): for `k > 0`, "no proper rigid subgraph" *forces* minimality
  (a circuit's induced rigid span in a non-rigid graph is automatically
  proper), so the k>0 split arm (KT Case II — survives per §R3) sees
  exactly KT's minimal class; only the **k = 0 split arm** acquires a
  new residue class — rigid graphs with a *spanning* circuit and no
  proper rigid subgraph (e.g. C5, C6, which KT's minimal class already
  contains; plus their chorded variants if any survive the
  circuit-dispatch — likely none, open). That residue's split-off
  def-bookkeeping is part of the W5 arm's work and is flagged there.
- The contract arm needs the **minimality-free contraction bookkeeping**
  `def((G/E(H))̃) = def(G̃)` for proper rigid `H` (W3-L6a below) —
  extractable from the landed `contraction_isMinimalKDof` bricks (the
  matroid-contraction rank identity + `rank_add_deficiency_eq` are
  minimality-free; only the fiber-meeting half of
  `rigidContract_isMinimalKDof` consumed minimality).

**The (b′) motive and the GP caveat.** The reduction skeleton is
motive-generic (`P : Graph α β → Prop`), so it is *invariant* to how
W4/W5 resolve. But the wrapper's arm interfaces below are stated with
the **bare** existential motive `HasPencilRealization`, and — exactly as
in the landed program, where Theorem 5.5's motive is the conditioned
pair `(Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` —
the W4/W5 arms will almost certainly need the IH strengthened by a
**pencil-generic conjunct** (the constrained-family argument of W4
consumes in-family genericity, not bare existence). The final motive is
therefore expected to be a conditioned pair whose generic half is the
in-stratum genericity device's output; pinning it is the *first W5
deliverable*, and the bare-motive wrapper W3-L7 below is explicitly
provisional on that. (Do not treat W3-L7's interfaces as final.)

### W3 leaf decomposition (typechecked shapes, 2026-07-24 spike)

All signatures typechecked with `lake env lean` against the landed tree
(statements `sorry`-bodied in the scratch spike; names tentative):

```lean
/-- W3-L0: the `V(G)`-relative pencil motive (the `P` of the reduction);
mirrors `HasPanelRealization` (M2) at grade 2. -/
def HasPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    HasPencilPanelRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- W3-L1: the min-degree-3 dispatch lemma. -/
theorem exists_isProperRigidSubgraph_of_three_le_degree
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} {G : Graph α β}
    (hD : 4 ≤ Graph.bodyBarDim n) (hV3 : 3 ≤ V(G).ncard) (hloop : G.Loopless)
    (hdeg : ∀ v ∈ V(G), 3 ≤ G.degree v) :
    ∃ H : Graph α β, H.IsProperRigidSubgraph G n

/-- W3-L6a: minimality-free rigid-contraction deficiency bookkeeping. -/
theorem rigidContract_deficiency_eq
    [DecidableEq β] [Finite α] [Finite β] {H G : Graph α β}
    {n : ℕ} [NeZero (Graph.bodyHingeMult n)]
    (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H)) :
    (G.rigidContract H r).deficiency n = G.deficiency n

/-- W3-L2: the pencil reduction skeleton — KT's dispatch on ALL
multigraphs, measure lex (|V|, |E|), loop arm the only |E|-consumer. -/
theorem Graph.pencil_reduction
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n)
    {P : Graph α β → Prop}
    (hloop : ∀ G : Graph α β, (∃ e x, G.IsLoopAt e x) →
      (∀ G' : Graph α β, V(G').Nonempty →
        V(G').ncard < V(G).ncard ∨
          (V(G').ncard = V(G).ncard ∧ E(G').ncard < E(G).ncard) → P G') → P G)
    (hbase : ∀ G : Graph α β, G.Loopless → V(G).Nonempty → V(G).ncard ≤ 2 → P G)
    (hcut : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G)
    (hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, V(G).Nonempty → P G

/-- W3-L5: the base arm (≤ 2 bodies, every def; generalizes the landed
W1 parallel-pair producer to all parallel classes + the 1-body and
single-edge cases). -/
theorem hasPencilRealization_of_ncard_le_two [Finite α] [Finite β] {G : Graph α β}
    (hloop : G.Loopless) (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2) :
    HasPencilRealization K 3 G

/-- W3-L7 (PROVISIONAL bare-motive form — see the GP caveat): the
conditional pencil conjecture, arms as hypotheses. -/
theorem pencil_conjecture_of_arms [Infinite K]
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcontract : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        HasPencilRealization K 3 G') →
      HasPencilRealization K 3 G)
    (hsplit : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
      (∃ v ∈ V(G), G.degree v = 2) →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        HasPencilRealization K 3 G') →
      HasPencilRealization K 3 G)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
      HasPencilPanelRealization G F normal point ∧
      F.RankHypothesis (G.deficiency 3)
```

Remaining W3 leaves without spiked shapes (buildable, ordered): **W3-L4** (cut
arm, the §R3 "repairable" case). **W3-L4 is 3+ commits, not one** — decomposed in build:
- *transport* (LANDED 2026-07-24, `hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`,
  `Molecule/Pencil.lean`, node `lem:pencil-projective-transport`): the `K`-level projective
  repositioning of a pencil realization. **Correction to this doc's earlier claim** ("the landed
  `ProjectiveInvariance` transport" suffices): `thm:projective-invariance`
  (`Molecule/ProjectiveInvariance.lean`) is over `ℝ` and transports only `supportExtensor` along a
  screw automorphism — it does *not* carry `(normal, point)` nor work over general `K`. The pencil
  arm needs the `K`-level transport built on `GenericLift/HingeGeneric.lean`'s
  `screwEquivOfLinearEquiv`/`mapSupport`/`finrank_span_rigidityRows_mapSupport`, now landed.
- *nondegeneracy* (LANDED 2026-07-24, `exists_reposition_cross_incidences`, `Molecule/Pencil.lean`,
  node `lem:pencil-cut-nondegeneracy`): ∃ `g` (+ contragredient `h`) meeting the 2 cross-incidences.
  **Correction to this doc's earlier plan** (`[Infinite K]` genericity via
  `exists_linearEquiv_forall_last_ne_zero`): **no genericity needed** — an explicit
  two-independent-vectors-to-two frame construction (`exists_linearEquiv_basisFun_pair` composed via
  `g₁.symm.trans g₂`) works over any field, since each `n^⊥` is `≥ 3`-dim. The contragredient
  `g ↦ (g⁻¹)ᵀ` is built as the `≃ₗ` `exists_contragredient_linearEquiv` (`≃ₗ` sibling of Meet's
  `LinearMap` `contragredient`); helper `exists_perp_linearIndependent`.
- *rank-assembly infra* (LANDED 2026-07-24, `Molecule/Pencil.lean`, no node):
  `finrank_span_rigidityRows_cutEdge_eq` (minimality-free cut-edge rank equality) +
  `span_rigidityRows_eq_of_supportExtensor_agree` (side-span equality) — the minimality-free public
  re-derivations of Theorem55's `private` `cutEdge_finrank_assemble` / `span_rigidityRows_side_eq`.
- *assembly proper* (next / only remaining W3-L4 piece): the framework-construction +
  `HasPencilPanelRealization` proof + `|C|∈{0,1}` wiring, mirroring `case_cut_edge_realization_gen`
  (Theorem55.lean:1323) minimality-free, consuming transport + nondegeneracy + the rank infra.
  **Correction:** `exists_cut_decomposition_of_not_twoEdgeConnected` is **NOT** minimality-free
  (it needs `IsMinimalKDof`); the minimality-free route unfolds `¬TwoEdgeConnected` directly +
  `deficiency_eq_of_cutEdges_ncard_le_one` (which *is* minimality-free).
(**W3-L2a**, **W3-L0**, and **W3-L3** landed 2026-07-24: `Graph.simple_of_loopless_of_noRigid`
(`Induction/ReducibleVertex.lean`), `HasPencilRealization` +
`hasPencilRealization_of_isLoopAt` (`Molecule/Pencil.lean`) — see `notes/Phase39.md`.)

**First buildable commit: W3-L1** — motive-independent, pure
combinatorics on landed bricks, and every later W3 leaf sits on it.

### W5 route (second core): the escape-line numerics (N2)

New experiment, the "numerically explorable first" flag discharged. The
exact Case-III habitat: `G` = double-subdivided K4 (16 bodies, 18 edges,
`5|E| = 6(|V|−1)` tight, minimal 0-dof; hubs degree 3, every chain
hub–x–y–hub); split at an interior `v` adjacent to hub `b`, with `a` the
fellow interior and `c` the far hub (KT's chain `b–v–a–c`, both ends
degree 3 — exactly the §R3 shortfall case); `G′ = G^{ab}_v = G − v + ab`
(15 bodies, 17 edges, `5·17 = 85 = 6·14 + 1`, the one redundancy Claim
6.11 needs). Pencil-generic realizations of `G′` sampled exactly as in
§R2 (hub star-planes free, neighbours placed inside; `a` on the line
`Π(b) ∩ Π(c)`); rows per edge = an exact basis of `C_e^⊥ ⊆ ℚ⁶`.

Five independent exact-rational samples, all identical in outcome:

| quantity | value (5/5 samples) |
|---|---|
| rank `R(G′, q)` at pencil-generic `q` | **84** = 6·14 (the IH output holds on `G′`) |
| left nullity of the 85-row matrix | 1 (λ unique up to scale) |
| λ supported on the `ãb` rows (Claim 6.11 pencil analogue) | yes |
| KT eq. (6.44) `r = −Σ λ_{(ac)j} r_j(q(ac))` | verified |
| `dim(Λ²Π̂(a) + pencil(b) + pencil(c))` | **5** (the §R3 shortfall, re-confirmed) |
| `r ⊥ Λ²Π̂(a)` (candidate `M₁` fails)? | **no** — `M₁` works |
| `r ⊥ pencil(b)` (`M₂` fails)? | **no** — `M₂` works |
| `r ⊥ pencil(c)` (`M₃` fails)? | **no** — `M₃` works |

**Reading.** The 1-dim escape line is real (dim 5 < 6) but `r` misses it
pencil-generically — and not narrowly: every candidate works alone. The
W5 route is therefore **not** a fourth construction but a genericity
argument, and the cheapest target is candidate `M₁` alone: `L ⊂ Π(a)` is
*completely free* (the chain interior `v, a` have degree 2, §R3), so the
obligation is `r ⬝ Λ²Π̂(a) ≠ 0` pencil-generically. `r` is a rational
function of the stratum parameters wherever rank = 84 and the left
nullity is 1 (solve the linear system; both conditions hold at the
sampled seeds), so the failure locus is a proper closed condition and
the N2 samples are literal **seeds** for the in-stratum genericity
device. W5's Lean shape: a genericity-conditioned single-candidate
replacement for Claim 6.12, plus the device itself (the cross-cutting
obligation of §Decomposition, now with a concrete first consumer and
concrete seed constructions). Two flagged sub-obligations: (i) the
device must parametrize the *pencil* stratum (star planes free,
neighbours inside, `a`-type bodies on panel-meet lines — the N2 sampler
is the blueprint); (ii) the k = 0 split arm's non-minimal residue
(spanning-circuit graphs, §W3 above) needs its Claim-6.11 input
(`|B′ ∩ ãb| < 5`, KT Lemma 4.3(ii), p. 684) re-derived without
minimality or the residue class shown empty.

### W4 route (third core): cluster refutation + the constrained-family survivor (N3)

**The keep-hinges route is refuted deterministically.** Instance:
`G` = C4(1,2,3,4) + bodies `x, y`, with `x` and `y` each joined to
bodies 1 and 3 (6 bodies, 8 edges; `def = 0`, target 30). Case-I contraction of the C4 gives `{v*, x, y}` with two
parallel pairs; any rank-12 pencil realization of the contracted graph
forces the full coincidence cluster (both parallel-pair analyses of §R1
apply): `pt` and `Π` shared by all three bodies. Un-contracting while
*keeping* the connecting hinges forces bodies 1 and 3 (each carrying two
distinct connecting hinges through the shared point) into the same
`(pt*, Π*)`, whence **all eight hinges** of the glued framework pass
through `pt*` inside `Π*`: the extensor space is the 2-dim flat pencil,
motions have dim ≥ 6 + 5 − 3 = 8 (spanning-tree freedom 5, each of the
3 non-tree edges imposes 1 condition inside the pencil plane), rank
≤ 36 − 8 = **28 < 30**. No numerics needed; the cluster route cannot be
the uniform Case-I mechanism. (The conjecture itself is fine on this
instance: with all four star-coplanarity constraints, the direct pencil
stratum contains 3-dim-spanning all-coplanar-star configurations with
`2|E| = 16 ≥ 3|V| − 3 = 15` — the §R2 deficit is non-positive.)

**What survives: KT's own Claim-6.4 architecture, constrained.** KT
p. 675 does *not* keep the contracted realization's hinges: connecting
edges get **fresh** hinges `Π₂(u) ∩ Π₁(v)` (eq. (6.6)), and the hybrid
block's rank is proven by *specialization* — setting `Π₁(v) := Π₂(v*)`
for all `v ∈ V′` turns the hybrid into `(G/E′, p₂)` exactly, and
algebraic independence of the panel coefficients makes the generic
hybrid at least as good (Claim 6.4). The pencil analogue: connecting
hinges = W2 two-pencil hinges (`exists_extensor_two_pencils`), which
exist **iff** the cross-incidences hold (`exists_extensor_two_pencils_iff`)
— so the whole argument must run on the **constrained family**
`F = {(p₁, p₂) : pencil realizations of G′ and G/E′ with the
cross-incidences at every δ(V′) edge}`. The specialization
`(pt₁, Π₁)|_{∂V′} := (pt₂(v*), Π₂(v*))` *lies in F* (the contracted
realization's own hinges witness its cross-incidences) and gives the
hybrid block full rank, exactly as in KT. What KT gets for free and the
pencil case must earn: the `G′`-block also needs an **in-family
full-rank witness** (the family is not a product — the constraints
couple `p₁`'s boundary data to `p₂`).

**N3 (new experiment): the G′-block witness exists on the discriminating
instance.** For the instance above, the constraints on `p₁` reduce to:
`pt(1), pt(3)` in a common plane `Π*` and `Π(1), Π(3)` through a common
point `pt*`. Exact-rational sampling of that constrained C4 pencil
stratum (points of bodies 1, 3 placed in `Π*`; body 4's position solved
from the two linear through-`pt*` conditions): **rank 18 = D(|V′|−1) in
4/4 samples** (N1's baseline: the same C4 all-coplanar caps at 17, so
the constraint pattern genuinely matters and this one is survivable).

**W4's honest remainder** (research-scale, but now shaped): (i) the
joint-genericity device on the fiber-product family `F` (the same
in-stratum seed device as W5, on constrained substrata — hence W4 after
W5); (ii) witness generality: N3 covers the boundary pattern arising
from parallel-pair contractions (one common `(pt*, Π*)`); general
`δ(V′)` patterns couple each boundary body to *several* outside bodies'
data, and the witness question must be answered per-pattern or
uniformly (numerically explorable per-instance first, as before); (iii)
the IH interface: the constrained-family argument consumes in-family
*genericity* of the smaller realizations, not bare existence — the
conditioned-pair motive of the GP caveat above.

### Numerics index (this recon)

| # | experiment | result |
|---|---|---|
| N1 | C4 all-coplanar (deep locus), 4 samples + generic baseline | 17 vs 18 (deficit 1 = spline count) |
| N2 | escape line on `(dbl-subdiv K4)^{ab}_v`, 5 samples | rank 84 ✓, nullity 1 ✓, (6.44) ✓, dim S = 5, `r` misses the line; `M₁`,`M₂`,`M₃` all individually work |
| N3 | constrained-C4 witness (`pt(1),pt(3) ∈ Π*`, `Π(1),Π(3) ∋ pt*`), 4 samples | 18 = full target |

## W5 design pass (2026-07-24): motive pin, device design, leaf decomposition

Commissioned per `notes/Phase39.md` *Hand-off* (W3 complete as of
`pencil_conjecture_of_arms`; W5 next). Methods: landed definition bodies
(`PanelHinge.lean` motive pair, `Theorem55.lean` spine + producers,
`GenericityDevice.lean` engine, `GenericLift/PanelGeneric.lean` Phase-34
transfer device, `Molecule/Pencil.lean`, `Meet.lean` `complementIso`), a
typechecked `lake env lean` signature spike (scratch, not committed; the
shapes below are transcribed verbatim), three new exact-rational
experiments (N4–N6 below, same model as §R2, scripts scratch-only), and
the KT primary source (p. 684 re-verified this pass, see *Citations*).

### Verdicts

1. **The final conditioned-pair motive is PINNED** (typechecked shapes
   below): `PencilPair K n G := (PencilNondegFeasible K G →
   HasGenericPencilRealization K n G) ∧ HasPencilRealization K n G` —
   the generic half is the *stratum-nondegenerate* realization at the
   deficiency rank, and the conditioning is the stratum's own
   nondegenerate-satisfiability, **not** `G.Simple`.
   `Simple`-conditioning (the verbatim mirror of the landed
   `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization`)
   is **refuted deterministically**: at K4 every body's closed
   hub-neighbourhood (below) has 4 members, the stratum forces
   `pt_v ⬝ n_w = 0` for all four normals (own-panel incidence + the
   landed W2-necessity
   `dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`), so
   nondegenerate points do not exist at the simple graph K4 — a
   `Simple`-conditioned generic conjunct strong enough to serve the
   consumers is false there, and one weak enough to be true (bare
   existential + rank) **starves both consumers**: the W5 product-route
   consumption needs polynomial perturbation paths through the IH
   realization, and a bare full-rank point can sit on a branch (e.g.
   all-coplanar) no chart passes through. Feasibility-conditioning makes
   the conjunct vacuous exactly on the collapse graphs and self-scopes
   the known degenerations: a loop kills the adjacent-point-LI conjunct
   (the `loop ⟹ ¬Simple` mirror, so the loop arm's generic obligation is
   free), and a `≥ 2`-fold parallel class between two hubs kills the
   hub-normal-LI conjunct (KT Lemma 5.3's coincident-panel base stays
   bare-motive, as in the landed program's non-simple flows).
   **Correction (2026-07-24, W5-L5): this parallel-class claim is FALSE**
   — see §"W5 leaf decomposition" L5's finding below (a compiler-checked
   witness shows a parallel class is nondegeneracy-feasible; the tension
   this creates for `HasGenericPencilRealization`'s rank target is an
   open blocker, not a vacuity).
2. **The device is the grade-0 molecular-side chart + the LANDED
   engine; no new engine, no standing transfer-form conjunct.** The N2
   sampler made uniform: seeds = per-body free vectors (hub star-plane
   normals + fill vectors); constructed points = the K⁴ cross product
   (grade-3 `complementIso`, `Meet.lean`, or a small direct `cross₃`) of
   the body's closed-hub-neighbourhood normals padded by fill seeds;
   non-hub normals = cross of own + neighbour points; hinges = the
   point-join extensors `extensor ![pt u, pt v]`. Everything is
   polynomial in the seeds, so the rows'-coordinates identity (the
   mirror of `PanelGeneric.lean`'s `annihRowPoly`/`hg` block) feeds the
   landed engine
   `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`
   (`GenericityDevice.lean`) directly. Per the Phase-30 RELAX precedent
   the motive carries **no** transfer-form genericity conjunct — each
   consumer takes its own product-route shot. (The Phase-34
   `IsGenericNormals` transfer form is *not* mirrored: its
   "LI-at-some-assignment" quantification is ill-founded on the
   reducible constrained stratum — off the distinct-points locus the
   rows are not even functions of the placement — and the candidate
   rows the W5 crux tests live outside any fixed row family.) The
   **re-seeding lemma D6** (every nondegenerate stratum point is a chart
   point: `cross₃(n₁, n₂, ·)` sweeps the full 2-dim perp of an LI pair,
   and likewise in the other arities) is what keeps the **motive
   chart-independent** — arms owe geometric nondegeneracy only, never
   seed bookkeeping, and a later chart redesign (the graded extension
   below) does not restate the motive. This is the churn-control
   property the GP caveat asked for.
3. **New numerics N4–N6: every forced nondegenerate branch tested
   attains full target rank.** The R2 collapse findings only ever tested
   the *all-coplanar* branch of the dense graphs; the pencil stratum's
   other components were untested. N4: theta(2,2,2) with the three
   interior atoms collinear on the two hub-planes' meet line (the branch
   forced when the hub planes are distinct) attains 24/24 in 5/5 exact
   samples — so theta(2,2,2) is `PencilNondegFeasible` and the generic
   conjunct there is *true with the N4 witness* (its producer is the
   contract arm — a W4 obligation, evidence positive). N5: K3,3 with
   each side collinear on its own line attains 30/30 in 5/5 — K3,3 is
   nondegeneracy-INfeasible (each body has a 4-member closed
   hub-neighbourhood), so the conjunct is vacuous there and N5 confirms
   the *bare* target survives on that branch. N6: the "spider-K4"
   (K4 on `{u,a,b,c}` with `u`'s three edges kept and `ab`, `ac`, `bc`
   each replaced by a length-3 path; `u,a,b,c` all hubs, `u`'s closed
   hub-neighbourhood = 4 members) on its coincidence branch
   (`u,a,b,c` coplanar in `Π(u)`; `Π(a) ⊇ line(a,u)` free otherwise;
   interiors inside their hub's plane) attains 54/54 in 6/6 (generic
   baseline 54) — the stratum branches the grade-0 chart cannot reach
   still satisfy the conjecture, so if W4's constrained substrata need
   them, a **graded chart** (points-first elimination ordering; the N6
   sampler is the blueprint) extends the device without touching the
   motive.
4. **Split-arm use-sites are conjecturally feasible (W5-L6).** Two
   attempts to build a 2EC/no-proper-rigid habitat graph containing a
   4-member closed hub-neighbourhood both fell into the contract arm:
   spider-K4 has the dependent proper subset `{u,a,b,c,p₁,p₂,q₁,q₂}`
   (5·9 = 45 > 42 = 6·7), and the 3-chain star with chain length 4 has a
   dependent two-chain subset (5·11 = 55 > 54). The combinatorial lemma
   "2EC + no proper rigid subgraph ⟹ every closed hub-neighbourhood has
   ≤ 3 members" (plus a witness-seed construction, char-free à la
   `momentCurve`) is the W5-L6 leaf; it is what discharges
   `PencilNondegFeasible` at the split arm's `G′ = G^{ab}_v`.
5. **The k = 0 residue (sub-obligation (ii)) sharpened.** KT p. 684
   (re-verified this pass) shows Claim 6.11's proof consumes minimality
   **twice**: Lemma 4.3(ii) (`|B′ ∩ ãb| < 5`) *and* "Gᵥ is minimal by
   Lemma 3.3" (feeding eq. (6.22)). The emptiness route — the spiked
   `isMinimalKDof_of_isKDof_zero_of_noRigid` below, "a rigid loopless
   multigraph with no proper rigid subgraph is minimal 0-dof" — restores
   both at once and is the recommended attack; the fallback (re-derive
   both inputs minimality-free) is strictly more work. Sketch for the
   recommended route: if `G − e` stays 0-dof, `Ẽ` is dependent, the
   circuit's induced rigid subgraph must be spanning (no proper rigid),
   and the count squeeze on spanning circuits against `5|E| ≥ 6(|V|−1)`
   is the open step — genuinely unsettled, but bounded and
   motive-independent.

### Pinned Lean shapes (typechecked spike, 2026-07-24)

```lean
/-- A body of `G` is a *pencil hub* — degree ≥ 3, where the pencil pin bites. -/
def Graph.PencilHub (G : Graph α β) (v : α) : Prop :=
  v ∈ V(G) ∧ 3 ≤ G.degree v

/-- The closed hub-neighbourhood of `v`: the hubs among `v` and its neighbours —
exactly the bodies whose star-plane normals `point v` is forced orthogonal to
(own-panel incidence + the two forced cross-incidences per link, W2 necessity). -/
def Graph.closedHubNbhd (G : Graph α β) (v : α) : Set α :=
  {w | G.PencilHub w ∧ (w = v ∨ ∃ e, G.IsLink e v w)}

/-- Stratum nondegeneracy: adjacent concurrency points projectively distinct,
and each body's closed-hub-neighbourhood normals linearly independent. -/
def IsNondegPencilRealization (G : Graph α β) (F : BodyHingeFramework K 2 α β)
    (normal point : α → Fin 4 → K) : Prop :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v))

/-- The conditioning predicate — the pencil analogue of Theorem 5.5's `G.Simple`. -/
def PencilNondegFeasible (K : Type*) [Field K] (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point

/-- The generic pencil motive: a nondegenerate realization at the deficiency rank. -/
def HasGenericPencilRealization (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework K 2 α β) (normal point : α → Fin 4 → K),
    IsNondegPencilRealization G F normal point ∧
    (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n

/-- The conditioned-pair motive (the final `P` of the reduction). -/
def PencilPair (K : Type*) [Field K] (n : ℕ) (G : Graph α β) : Prop :=
  (PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
    HasPencilRealization K n G
```

The forgetful map `hasPencilRealization_of_generic : HasGenericPencilRealization K n G
→ HasPencilRealization K n G` **proved in-spike** (two lines, drop the conjuncts). The
W3-L7 successor `pencil_conjecture_of_arms_pair` typechecked with `hcontract`/`hsplit`
at the `PencilPair` motive and two new conditioned producers as hypotheses
(`hbase_pair`, `hcut_pair` — the base/cut arms' generic halves; their bare halves are
the landed W3 leaves), concluding the same
`HasPencilPanelRealization ∧ RankHypothesis (G.deficiency 3)` as W3-L7. The k = 0
residue leaf typechecked as:

```lean
theorem isMinimalKDof_of_isKDof_zero_of_noRigid [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} {G : Graph α β} (hD : 4 ≤ Graph.bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hloop : G.Loopless) (hk : G.IsKDof n 0)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    G.IsMinimalKDof n 0
```

### W5 leaf decomposition (dependency order)

- **W5-L0** (the *first buildable commit*): the motive layer — the six pinned decls
  above + the forgetful map + the loop guard
  `not_pencilNondegFeasible_of_isLoopAt` (a loop's link forces
  `LinearIndependent K ![point v, point v]`, false), in
  `Molecule/Pencil.lean`; blueprint nodes in `pencil.tex` (new
  `def:pencil-nondegenerate`, `def:pencil-generic-motive`,
  `def:pencil-conditioned-pair` + restating `thm:pencil-conditional-realization`'s
  planned successor as a red node; the landed W3-L7 node keeps its provisional
  fmlnote until W5-L5 lands).
- **W5-L1**: `cross₃` (the K⁴ generalized cross product) + orthogonality,
  multilinearity, vanishing-iff-dependent, and the perp-sweep lemma (image of
  `cross₃(n₁,n₂,·)` = the 2-dim perp of an LI pair) — either the grade-3
  `complementIso` specialization (`Meet.lean:479`) or a direct cofactor def,
  whichever proves shorter.
- **W5-L2**: the grade-0 chart — `PencilSeed` (per-body hub-normal + fill vectors),
  `pencilChartPoint`/`pencilChartNormal`/`pencilChartFramework` (with an explicit
  hub-selector, the landed `ends`/`hends` idiom), chart well-formedness, and
  by-construction stratum membership (`IsNondegPencilRealization` at WF seeds).
- **W5-L3**: the rows-polynomial identity (pencil `annihRowPoly` mirror; constructed
  points are degree-≤3 polynomial in seeds, hinge rows degree-≤6) + the engine hookup
  + the product-route workhorse (from a WF seed with an LI row subfamily and finitely
  many polynomials each nonvanishing somewhere on the chart, a common seed).
- **W5-L4** (D6): the re-seeding lemma `exists_pencilSeed_of_nondeg` — every
  nondegenerate realization is a WF chart point (uses the perp-sweep lemma per arity).
  **Correction (2026-07-24, per-arity sweep helpers landed):** the reproduction is
  necessarily *projective* (a nonzero per-body scalar), not literal equality, at any
  body with a *full* (`3`-member) closed hub-neighbourhood — there all three `cross₃`
  slots are prescribed real normals, so no fill slot survives to correct the scalar the
  arity-`3` sweep (`exists_smul_cross₃_eq_of_linearIndependent`, `Pencil.lean`) leaves
  free; the arity-`1`/`2` cases (`exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`,
  `range_cross₃L_eq_perp`) do hit the target exactly, since a free fill slot survives
  there. Every `IsNondegPencilRealization` conjunct is invariant under independent
  per-body rescaling of `point`/`normal`, so this is the right invariant for
  `exists_pencilSeed_of_nondeg`'s eventual statement, not a weakening. Full derivation
  in `Pencil.lean`'s new §"W5-L4: the re-seeding lemma's per-arity sweep helpers".
  **Second correction (2026-07-24, assembling the cardinality bound + selector
  construction, pieces 1–2):** `PencilChartWF`'s `nbrSel`/`closedNbhd` conjunct was
  **unconditionally** `∀ v, IsFin3SelectorOf (closedNbhd v) (nbrSel v)`, but
  `IsFin3SelectorOf` needs its target set to have `≤ 3` members and nothing bounds
  `closedNbhd v` at a high-degree hub (every vertex of K4 already has `closedNbhd`
  size `4`) — the predicate was unsatisfiable on every graph the design doc's own
  numerics (N4–N6) exercise. **Fixed**: relativized to
  `∀ v, ¬ PencilHub v → IsFin3SelectorOf (closedNbhd v) (nbrSel v)`, matching every
  existing consumer exactly (`nbrSel` is read only inside a `¬ PencilHub` branch
  throughout `Pencil.lean`, never at a hub) — a same-shape hypothesis strengthening,
  not a weakened conclusion; all downstream theorems (`isNondegPencilRealization_
  pencilChartFramework_of_pencilChartWF` included) compile unchanged in body. **A
  third gap surfaced attempting piece 3 (the global seed assembly)**:
  `PencilChartWF`'s *fourth* conjunct (`nbrSlotPoint` LI) stays
  unconditional, and at an ordinary degree-`2` non-hub body `v` with two distinct
  neighbours `w₁ ≠ w₂` (`closedNbhd v = {v, w₁, w₂}`, exactly `3` members, no fill
  freedom), it demands the **raw, unscaled** triple `{point v, point w₁, point w₂}`
  be linearly independent — `IsNondegPencilRealization` supplies only *pairwise*
  adjacent-point independence (from the two links `v`–`w₁`, `v`–`w₂`), nothing
  about the non-adjacent pair `w₁, w₂` or the full triple. **RESOLVED by the
  2026-07-24 W5-L4 blocker recon — verdict below.**

  **Blocker verdict (2026-07-24 W5-L4 blocker recon; compiler-checked scratch spike,
  not committed): the triple can genuinely fail — route 1 ("derive it") is REFUTED;
  route 2 pinned as a motive strengthening.** A concrete sorry-free
  `IsNondegPencilRealization` over `ℚ` on the path `P₃ = 0–1–2`
  (`(Graph.singleEdge 0 1 0).addEdge 1 1 2`, vertex/edge types `Fin 3`/`Fin 2`)
  takes `point = ![e₀, e₁, e₀+e₁]` (collinear: `point 2 = point 0 + point 1`),
  `normal = ![e₂, e₃, e₂+e₃]`, and *every* edge's supporting extensor the single
  line `extensor ![e₀, e₁]`: all conjuncts hold — both links' endpoint pairs ARE
  independent, and `closedHubNbhd = ∅` everywhere (no hubs, max degree `2`) — yet
  the triple at the degree-`2` non-hub body `1` is dependent. Geometric reading:
  nothing in the landed motive forbids the two hinges at a degree-`2` body from
  *coinciding* (at a parallel class they even coincide by force), so the collinear
  branch lies genuinely inside the current nondegeneracy locus — and there the
  chart's non-hub normal `cross₃(points) = 0`, so no re-seeding target, projective
  or otherwise, can reach it (a weaker reproduction contract cannot repair a
  *vanishing* constructed normal; and the selector cannot drop a member without
  losing that link's coplanarity incidence). The predicate under-specified D6's
  intent — it was designed to characterize the grade-0 chart's image projectively,
  and the missing condition is exactly the non-hub point-triple independence.

  **The pinned route-2 restatement (all shapes typechecked in the spike):**
  1. `IsNondegPencilRealization` gains a **fourth conjunct**
     `∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)`.
     At a `≤ 2`-member closed neighbourhood this adds nothing new (nonzero point /
     the link's pair-LI already give it), so it bites exactly at the `3`-member
     case — the ordinary degree-`2` body with distinct neighbours. It is invariant
     under independent per-body nonzero rescaling (`units_smul`), so it composes
     with the already-recorded projective reproduction contract. It must NOT be
     imposed at hubs: a degree-`≥ 4`-distinct-neighbour hub has a `≥ 5`-member
     `closedNbhd`, never LI in `K⁴` (subdivided K5's hubs, R2-tested, would go
     infeasible).
  2. `PencilChartWF`'s fourth conjunct **relativizes** to
     `∀ v, ¬ G.PencilHub v → LinearIndependent K ![nbrSlotPoint … 0, … 1, … 2]` —
     its sole consumer in the tree is the non-hub branch of
     `hasCoplanarPanelRealization_pencilChartFramework` (via
     `pencilChartNormal_ne_zero_of_not_pencilHub`; the only `hNbrLI` read,
     `Pencil/Chart.lean`), mirroring the landed second-conjunct correction and
     removing the hub-side fill bookkeeping from the re-seeding assembly.
  3. The headline theorem's successor produces the new motive conjunct via the
     mirrored transfer lemma `linearIndepOn_pencilChartPoint_closedNbhd` — the
     `nbrSlotPoint`/`closedNbhd`/`nbrSel` mirror of
     `linearIndepOn_pencilChartNormal_closedHubNbhd`, same
     witnessing-slot-injectivity proof shape.

  **Carried-obligation check (per the dispatch):** (a) chart by-construction
  satisfiability survives — the successor headline shape typechecks and the
  transfer mirror supplies the new conjunct; the landed headline consumes WF's
  fourth conjunct *only* at non-hubs, so the relativization changes no proof body.
  (b) The L3 engine chain (`pencilChartPointPoly` → `pencilAnnihRowPoly` →
  `exists_polynomial_ne_zero_of_linearIndependent_pencilRow`) reads the chart
  *constructions*, never `PencilChartWF` — unaffected. (c) Downstream: L5's arm
  generic halves owe the extra conjunct (single-edge base: the `2`-member case,
  free from the link pair-LI; cut arm: moderate, same infra); L6's witness-seed
  construction owes non-hub triple-LI, the same genericity flavor as its existing
  charter; L7 perturbs from a chart point, which under the restatement genuinely
  satisfies the full motive — nothing orphaned. `not_pencilNondegFeasible_of_
  isLoopAt` and the K4 / hub-parallel-class infeasibility findings hold a fortiori
  (strengthening is monotone toward infeasibility); the parallel-pair base graph
  stays feasible (`2`-member closed neighbourhoods), so KT Lemma-5.3 flows are
  untouched; N4's theta(2,2,2) branch has interior triples `{p(x), p(hub₁),
  p(hub₂)}` generically LI (interiors sit on the hub-panels' meet line, hub points
  do not), so its feasibility narrative survives. **Mechanical fixups owed in the
  restatement slice:** destructuring arities in `hasPencilRealization_of_generic`
  + `not_pencilNondegFeasible_of_isLoopAt` (`Pencil/Motive.lean`) and
  `dotProduct_point_eq_zero_of_mem_closedHubNbhd` +
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`
  (`Pencil/Engine.lean`, `h.2.2` → `h.2.2.1`); the blueprint
  `def:pencil-nondegenerate` node restated in the same commit (the statement-change
  gate — its `\lean{…}` pin survives the flip); the `Motive.lean`/`Chart.lean`
  docstrings and the Engine §"W5-L4 continued" gap paragraph repointed to this
  verdict. **With the restatement, the WF-conjunct gap closes:** at a non-hub
  `3`-member `closedNbhd` the new conjunct feeds the relativized WF conjunct
  directly; the `≤ 2`-member cases pad by fill (a vector outside a `≤ 2`-dim span
  exists); hub points reproduce via conjunct 3 + the landed per-arity sweeps; and
  the non-hub chart normal reproduces *automatically* — the realization's normal
  is orthogonal to the LI point-triple whose common perp is `1`-dimensional
  (`finrank_toDualPerp_triple_eq`), hence proportional to `cross₃` of it, exactly
  the projective contract. **This resolved the WF-conjunct gap, not piece 3
  itself** — attempting the actual global assembly (below) surfaced a further,
  independent gap.

  **A second blocker, surfaced attempting the global assembly (2026-07-24, same
  session): the shared-`fill` conflict, and its fix.** `PencilSeed`'s single
  `fill : α → Fin 3 → Fin 4 → K` field is read by *two* different `cross₃` calls at
  the same body `v` — `hubSlotNormal` (feeding `pencilChartPoint v`, padding
  `hubSel v`'s unused slots) and `nbrSlotPoint` (feeding `pencilChartNormal`'s
  non-hub branch, padding `nbrSel v`'s unused slots) — both indexed by the *same*
  `Fin 3`. Whenever both selectors leave the same slot unassigned, the single
  shared vector `seed.fill v i` must solve two generically-different equations at
  once (the point-reproduction target and the normal-reproduction target). This is
  unavoidable by clever slot placement alone whenever a non-hub `v` has **no
  hub-neighbours** (`closedHubNbhd v = ∅`, forcing the point side to use *all
  three* fill slots) together with a `≤ 2`-member `closedNbhd v` (an isolated
  body, a degree-`1` body, or a degree-`2` body with a repeated/parallel
  neighbour) — a common combinatorial case, not an edge case. A "choose fill
  vectors in the common perp `point v^⊥ ∩ normal v^⊥`" workaround was explored and
  found to leave a residual degeneracy (it needs `point v` not self-orthogonal
  under the standard bilinear form, automatic over `ℝ` but not over a general
  field `K`) — rejected in favor of a clean structural fix. **Fixed**: split
  `PencilSeed.fill` into two independent fields, `fillHub` (read only by
  `hubSlotNormal`) and `fillNbr` (read only by `nbrSlotPoint`) — landed in
  `Molecule/Pencil/Chart.lean`; `PencilSeed.ofCoord` (`Engine.lean` W5-L3) sets
  both from the same coordinate (a harmless coupled special case, since the L3
  rows-polynomial machinery never reads `fillNbr`). This removes the conflict for
  every field `K`, no genericity assumption needed. Also landed as infrastructure
  for the eventual assembly: the general `dotProduct_point_eq_zero_of_mem_closedNbhd`
  (dropping the hub hypothesis on `w` from `dotProduct_point_eq_zero_of_mem_closedHubNbhd`,
  which is now a one-line corollary) and its symmetric mirror
  `dotProduct_normal_eq_zero_of_mem_closedNbhd` (`point w ⬝ᵥ normal v = 0` for
  `w ∈ closedNbhd v`) — the fact the non-hub chart-normal reproduction needs
  (the realization's own closed-neighbourhood chart *points*, each already
  reproducing `point w` up to a nonzero scalar, are orthogonal to `normal v`).

  **Piece 3's point side landed (2026-07-24); the non-hub-normal side and the final assembly
  remain open.** The point-side implementation (`Pencil/Engine.lean`,
  `exists_hubSlotOf_isNondegPencilRealization` + `exists_hubSel_fillHub_of_isNondegPencilRealization`)
  **deviates from this bullet's original recipe in one respect**: rather than literally completing
  the real family to a full basis of `point v`'s perp and applying the arity-`3` sweep uniformly, it
  dispatches internally on `(closedHubNbhd v).ncard ∈ {0,1,2,3}` and routes each case to its own
  ready-made sweep lemma (`exists_cross₃_eq_of_ne_zero`/`_of_ne_zero_of_dotProduct_eq_zero`/a new
  arity-`2` exact helper `exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero`/
  `exists_smul_cross₃_eq_of_linearIndependent`), each wrapped as a uniform `∃ c ≠ 0` **projective**
  statement (`c = 1` at arities `0`–`2`, a genuine scalar only at arity `3`) — a uniform *headline
  shape* at the level callers see, not a uniform *proof*. This was the pragmatic choice: the four
  concrete arities already had (or, for arity `2`, cheaply gained) ready sweep lemmas, so building
  the generic "complete an arbitrary-arity real family to a full basis" infrastructure the literal
  recipe calls for would have been more machinery than the fixed four cases need. The landed
  per-vertex lemma is combined into global `hubSel`/`fillHub` via the `choose` tactic
  (`Classical.skolem`-style), discharging `PencilChartWF`'s first/third conjuncts and the
  point-reproduction fact for *any* `fillNbr`.

  **Piece 3's normal side landed too (2026-07-24, same session as this bullet's write-up):**
  `exists_nbrSlotOf_isNondegPencilRealization` + `exists_nbrSel_fillNbr_of_isNondegPencilRealization`
  complete the closed-neighbourhood *chart-point* family (real, LI by
  `LinearIndependent.units_smul` transport of the realization's own `closedNbhd` point-LI conjunct,
  all `⊥ normal v` by `dotProduct_normal_eq_zero_of_mem_closedNbhd`) with `fillNbr` vectors,
  reproducing `normal v` projectively via the same per-arity dispatch pattern as the point side,
  discharging `PencilChartWF`'s second/fourth conjuncts (not the fifth — that conjunct is purely
  about `pencilChartPoint` adjacency, so it belongs to the point side, corrected from this bullet's
  earlier framing). Two asymmetries the point side didn't have: `closedNbhd v` is never empty
  (arity `0` cannot occur for `v ∈ V(G)`), and at `v ∉ V(G)`, `closedNbhd v = {v}` still needs a
  selector/LI witness with no reproduction target (`exists_linearIndependent_triple_of_ne_zero`, a
  new no-target extend-to-triple helper). A `simp_all` case-bash that compiled instantly in the
  point side's shallower context timed out once copied into this lemma's heavier one — fixed by
  hoisting the light selector proof earlier plus `clear`ing heavy hypotheses (TACTICS-QUIRKS § 99).

  **L4 CLOSED (2026-07-24, same session):** the fifth `PencilChartWF` conjunct
  (adjacent-`pencilChartPoint` distinctness) landed exactly as predicted — an easy corollary of
  the point side's own reproduction transported along `IsNondegPencilRealization`'s
  adjacent-`point`-distinctness conjunct via `LinearIndependent.units_smul`, no new per-vertex
  construction needed — and the final assembly combines both sides' `hubSel`/`fillHub` and
  `nbrSel`/`fillNbr` into one `PencilSeed`, landing `exists_pencilSeed_of_nondeg` in a new leaf
  file `Molecule/Pencil/Reseed.lean` (Engine.lean was near the `≤1500`-LoC cap). No blueprint node
  named for it yet (unnamed-technical-infra precedent). W5-L5 is next (below).
- **W5-L5** (opened 2026-07-24, new leaf `Molecule/Pencil/Pair.lean`): the W3-L7 successor
  `pencil_conjecture_of_arms_pair` (spiked) + the arm re-derivations against the pair motive. Loop
  arm **landed** (`pencilPair_of_isLoopAt` — free, exactly the design's vacuity verdict: composes
  `hasPencilRealization_of_isLoopAt`'s bare half with `absurd`/`not_pencilNondegFeasible_of_isLoopAt`
  for the generic half, no new construction). **Base arm's parallel-class sub-case: the "vacuous"
  plan is REFUTED** (2026-07-24, re-deriving against the current 4-conjunct
  `IsNondegPencilRealization`, per the dispatch's re-derive-don't-adapt caution) — see the finding
  below, **resolved same day** by the user's (b′) `Simple`-conditioning adjudication (below), after
  which **the base arm CLOSED** (`pencilPair_of_ncard_le_two`: edgeless/single-edge genuine
  producers + the parallel case vacuous via `not_simple_of_parallel`, `notes/Phase39.md` *Decisions
  made*). Cut arm's generic half: the original "moderate — mirrors the landed
  `case_cut_edge_realization_gp_gen`" framing was refuted by the cut-arm finding below (the pencil
  chart is non-local in hub structure, so the panel GP arm's seed/polynomial proof does not mirror
  wholesale); its route is now PINNED by the "Cut-arm route verdict" block below (leaves
  L5-cut-i…v; the W3-L4 transport/nondegeneracy/rank infra IS reused there). The successor
  assembly remains open.

  **Finding (2026-07-24, compiler-checked): a `≥ 2`-fold parallel class is nondegeneracy-FEASIBLE,
  even at the base arm's own minimal instance (a parallel pair, no hub involved).** The design
  doc's plan and `PencilNondegFeasible`'s own docstring both claimed parallel classes were
  vacuous for the generic-conjunct obligation; `exists_isNondegPencilRealization_parallel_pair`
  (`Pencil/Pair.lean`) is a compiler-checked, sorry-free counter-witness: two independent panels
  `n₀, n₁` and two independent concurrency points `q₀, q₁` (via `exists_extensor_two_pencils`,
  cross-incidences all `0` by construction) give a genuine `IsNondegPencilRealization` at *any*
  parallel pair — `closedHubNbhd`/`closedNbhd` are both `⊆ V(G) = {x, y}` regardless of hub status,
  and the two chosen normals/points are already independent, so `LinearIndepOn.mono` closes the
  third/fourth conjuncts with no hub reasoning at all. Neither vertex needs degree `≥ 3`.

  This creates a genuine tension for the base arm's own obligation
  (`PencilNondegFeasible → HasGenericPencilRealization`): achieving the *full* target rank `D = 6`
  (deficiency `0` for any `m ≥ 2` parallel class, `Graph.deficiency_le_deficiency_of_le_vertexSet_eq`
  against a `2`-edge sub-rigid witness) needs **two independent-direction hinges** — one alone caps
  rank at `D − 1 = 5`, since `hingeRowBlock e = (Submodule.span K {supportExtensor e}).dualAnnihilator`
  (`RigidityMatrix/Basic.lean`) depends only on the extensor's own line, so proportional extensors
  give the identical row block. But two edges both required to pass "through" the same two points
  `pt_u, pt_v` are forced onto the *same* line whenever `pt_u ≠ pt_v` (`ExtensorThroughPoint`'s
  witness family must literally contain both points, and a decomposable `2`-extensor containing two
  given independent vectors is exactly their span — unique) — so two independent-direction hinges
  through the same pair of bodies force `pt_u = pt_v` (up to scale), which is exactly what
  `IsNondegPencilRealization`'s **second** conjunct (adjacent-point distinctness) forbids. The
  already-landed `exists_pencilPanelRealization_parallel_pair` (W1) confirms this from the
  construction side: its own full-rank parallel-pair witness uses `point := fun _ => q₀`, the
  *same* point at both bodies — not a proof-specific shortcut but (per the argument above) the only
  way to get two independent hinges at all. So `HasGenericPencilRealization` looks unsatisfiable at
  any `≥ 2`-fold parallel class, while `PencilNondegFeasible` is witnessed (landed) there — the base
  arm's generic obligation can be discharged as **neither** vacuous **nor** (yet) provable as
  stated. This is a genuine, unresolved blocker, not a proof gap to fill in — see
  `notes/Phase39.md` *Blockers* for the resolution options assessed (none attempted; needs a
  design-level call, most likely a recon) and why the design pass's own numerics (N4–N6) never
  exercised this: all three tested graphs (theta(2,2,2), K3,3, spider-K4) have `≥ 3` vertices, so
  none instantiate the base arm's own `|V(G)| ≤ 2` regime.

  **Blocker verdict (2026-07-24 L5 blocker recon; compiler-checked scratch spike, not committed
  — the restatement itself landed separately, below).** Three confirmations first, each against
  the landed definition bodies:

  1. **The rank cap is REAL — `HasGenericPencilRealization` is unsatisfiable at any `≥ 2`-fold
     parallel class, as the motive stands.** At a parallel class `{x, y}` with `point x, point y`
     projectively distinct (the motive's second conjunct), *every* parallel edge's supporting
     extensor is proportional to `extensor ![point x, point y]`: each edge's two
     `ExtensorThroughPoint` witnesses give `C.val = extensor p₁ = extensor p₂` with
     `point x ∈ span p₁`, `point y ∈ span p₂`; `C ≠ 0` (the coplanar realization's total nonzero
     conjunct) makes both spans the same 2-plane (`span_range_eq_of_extensor_eq`, `Meet.lean`),
     that plane contains the LI pair so equals `span {point x, point y}`, and
     `exists_smul_extensor_eq_of_mem_span_range` (`Meet.lean`) yields the scalar. Proportional
     extensors give the *identical* `hingeRowBlock` (`(span {supportExtensor e}).dualAnnihilator`,
     `RigidityMatrix/Basic.lean` — it depends only on the extensor's line), so the whole class
     contributes one 5-dim block. At the base instance (`V(G) = {x, y}`) the row span is the image
     of that single block under `r ↦ r ∘ₗ screwDiff x y` — rank `≤ 5 < 6 =` target.
  2. **Option (c) is REFUTED — the target rank is correctly derived.** The parallel pair's
     deficiency is genuinely `0`: `isKDof_zero_of_parallel_pair` (`Deficiency.lean`) is landed and
     is exactly this computation, and the *generic* (unpinned) two-hinge realization attains `6`
     (the landed `theorem_55_base_producer_parallel_pair_gen` flow). The collapse is a true fact
     about the nondegenerate locus, not a mis-derived target.
  3. **Option (b) as scoped (narrow the dispatch) is UNWORKABLE standalone.** `PencilPair` as
     landed is simply **false** at a parallel pair (feasible by the landed witness, generic half
     unsatisfiable by 1), and `Graph.pencil_reduction` instantiates `P` at every graph the
     induction passes through — no arm-narrowing routes around a false motive; (b) collapses into
     a motive change too.

  **Conjecture-level reading: the charter is SAFE.** The phase's headline is the *bare*
  `HasPencilRealization` (existential, deficiency rank), which holds at parallel classes via the
  coincident-point witness (W1's `exists_pencilPanelRealization_parallel_pair`). The collapse is an
  artifact of the conditioning: at a parallel-class graph the pencil stratum is *reducible*, and its
  max-rank locus lies in the coincident-point component — disjoint from the distinct-points
  (nondegenerate) component the conditioned motive quantifies over. This is precisely the phenomenon
  KT's own Theorem 5.5 meets at non-simple graphs ("two parallel edges want *equal* panels", p. 670,
  as recorded in `HasGenericFullRankRealization`'s docstring, `PanelHinge.lean`) and handles by
  `G.Simple`-conditioning; the landed `theorem_55_base_producer_gen`'s arm (iii) discharges the
  generic conjunct at the parallel pair by `not_simple_of_isMinimalKDof_of_ncard_two` — vacuity by
  ¬Simple, exactly the move available here.

  **Two workable repair routes, both spike-typechecked; (b′) RECOMMENDED:**

  - **(b′) — Simple-condition the pair (recommended):** restate
    `PencilPair K n G := (G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G)
    ∧ HasPencilRealization K n G`. Two-layer conditioning, each layer earning its keep: `G.Simple`
    excludes the multigraph degenerations (KT Thm 5.5's own printed conditioning; the landed
    Theorem55 pair's exact shape), `PencilNondegFeasible` excludes the stratum collapses (`K4`) —
    the design pass's verdict-1 refutation applied to Simple-conditioning *alone*, not to the
    conjunction. Costs/effects, swept: the chart tower (WF, the membership headline
    `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF`, `exists_pencilSeed_of_nondeg`,
    the L3 engine) is **untouched** — no motive predicate changes; the landed feasibility witness
    `exists_isNondegPencilRealization_parallel_pair` **stays true** and becomes the documented proof
    that feasibility alone cannot replace `Simple` (spike-checked consistent with
    `not_simple_of_parallel`); `pencilPair_of_isLoopAt` is a one-line fix (the feasibility discharge
    still works; ¬Simple is also available); the base arm's parallel sub-case is vacuous by the
    2-line `not_simple_of_parallel` (spiked), and its empty/single-edge sub-cases are unchanged
    (both simple + feasible, so the small generic producers are owed exactly as before); the cut
    arm's side consumption gets simplicity by `Simple.mono` (upstream); the contract-arm
    feasibility-propagation addendum **resolves** — contraction-created parallel classes make
    `G/E(H)` non-simple, so the generic IH obligation is vacuous there, the exact mirror of the
    landed program's non-simple flows (the route the W5-L5 finding had closed off under
    feasibility-only conditioning); the split arm's habitat `G` is already provably simple
    (`simple_of_loopless_of_noRigid`, W3-L2a, minimality-free, minted for this arm), and the IH
    consumption at `G′ = G^{ab}_v` owes a **new bounded L6 sub-obligation** — `G′` simple (no
    triangle at `v` in the no-proper-rigid habitat since a triangle is a proper rigid subgraph at
    `|V| ≥ 4`, plus the `|V(G)| = 3` edge case where `G′` is base-sized — fold into L6's charter,
    where the feasibility witness-seed construction already owes the same habitat analysis).
    Blueprint: restate `def:pencil-conditioned-pair` + its fmlnote + the red
    `thm:pencil-conditional-realization-pair` prose in the same commit (statement-change gate; the
    `\lean{}` pin survives). Docstring updates: `PencilPair`, `PencilNondegFeasible`'s correction
    note, `Pair.lean`'s section headers.
  - **(a) — strengthen the motive:** give `IsNondegPencilRealization` a fifth conjunct
    `∀ e f u v, e ≠ f → G.IsLink e u v → G.IsLink f u v → LinearIndependent K
    ![F.supportExtensor e, F.supportExtensor f]` (spike-typechecked), making parallel classes
    infeasible (the forcing in 1 + the second conjunct give the contradiction — a bounded W2
    composition, `not_pencilNondegFeasible_of_parallel`) and restoring the original vacuity plan
    with feasibility as the *single* self-scoping conditioning; the docstring's KT
    "no two hinges parallel" analogy becomes literal. Cost — the restatement wave the L4 tower just
    paid once already: the membership headline is **falsified as stated** (the chart's parallel-edge
    extensors are literally equal — `pencilChartFramework` reads `G.endsOf e`, identical on a
    parallel class), so it must gain a no-parallel-class hypothesis (or `PencilChartWF` a
    graph-shaped conjunct) and its blueprint node restates; the Engine's motive-destructuring
    lemmas take arity fixups; the landed feasibility witness `exists_isNondegPencilRealization_
    parallel_pair` becomes **false** and must be deleted (deletion-variant discipline: repoint its
    five-plus cross-references); every future nondeg producer (L6's witness seed, the cut/contract
    arm outputs, L7's perturbation output) owes the extra conjunct forever (vacuous wherever the
    habitat is parallel-free, but carried).

  Both routes leave the reduction skeleton, the W3 bare arms, the W3-L7 assembly, and the N4–N6/R2
  numerics narratives untouched (every tested graph is simple; the only parallel-class graph in the
  program's evidence set is W1's two-body double edge, which exercises the bare motive only).
  Recommendation rationale: (b′) is the landed program's own precedent executed at one-tenth the
  diff, and (a)'s single-predicate elegance buys nothing (b′) lacks mathematically — the two
  conditionings have identical reach (a feasible-and-simple graph is exactly where both fire).

  **Long-run comparison (2026-07-24 follow-up recon, commissioned by user adjudication; projects
  both routes through the phase's remaining program — the immediate costs above are not
  re-litigated).** Methods: landed bodies re-read
  (`Pencil/{Motive,Pair,Chart}.lean`, `Theorem55.lean`'s pair spine, `ReducibleVertex.lean`'s
  simplicity lemmas, the graph library's `Simple` class = `Loopless` + edge-uniqueness); KT
  pp. 668/670 re-read against the `.refs` copy; one scratch spike (below), deleted.

  *The structural fact the projection rests on:* **the two conditionings are logically equivalent,
  graph by graph.** Given the motive's conjuncts 1–2, route (a)'s fifth conjunct *fails* at every
  parallel class (the verdict's item-1 forcing) and is *vacuous* at every simple graph — the
  discharge is a one-line `absurd (he.unique_edge hf) hef` (spike-typechecked, with
  `Simple + 4-conjunct ⟹ the (a)-shaped 5-conjunct bundle` as a corollary) — and the loop guard
  covers looplessness, so `Feasible₅ ⟺ G.Simple ∧ Feasible₄` and the two generic halves are
  equivalent propositions. Consequence: **the remaining mathematics is route-independent** — every
  remaining leaf owes the same content under both — and the whole comparison is statement
  architecture plus the one-time wave. Per the dispatch's dimensions:

  1. *Remaining leaves — symmetric except for vacuity plumbing.* Base arm empty/single-edge:
     simple habitats, identical. Cut arm's generic half: hypotheses coincide at simple `G`; under
     **both** routes the side IH consumption owes side *feasibility*, not just side simplicity —
     and restricting `G`'s witness is not free (the cut edge's endpoint can demote from hub to
     non-hub in its side, acquiring the fourth conjunct with no source) — a route-neutral
     sharpening of "moderate" for the cut-arm dispatch. L6: identical content — under (a) the
     witness seed owes `Feasible₅ G′`, whose *necessary condition* is `G′.Simple` (the forcing),
     i.e. exactly (b′)'s explicit sub-obligation plus the spiked one-liner. L7: (b′) perturbs from
     a chart point with *unconditional* full-motive membership; (a) threads the headline's new
     no-parallel hypothesis from the simplicity in scope (one composition per use). L8:
     motive-independent. Vacuity plumbing is the one real asymmetry: (b′) needs only the 2-line
     `not_simple_of_parallel`; (a) makes the W2-composition forcing lemma
     (`not_pencilNondegFeasible_of_parallel`) load-bearing — bounded, one-time, but the heavier.
  2. *End-state headline.* KT's printed Theorem 5.5 is literally the (b′) shape — "there exists a
     **(nonparallel, if G is simple)** panel-hinge realization" (p. 670, re-read) — and §5.1
     defines nonparallel realizations **only for simple graphs** ("For a simple graph G (i.e., no
     parallel edges exist in G) …", p. 668): KT never extends nondegeneracy to multigraphs; it
     scopes by simplicity up front. (b′) also matches the landed flagship pair
     (`Theorem55.lean`), so the program's two conditioned pairs read as one pattern. (a)'s
     headline is intrinsically attractive ("whenever the nondegenerate component is nonempty, it
     achieves the rank") but is a nondegeneracy-on-multigraphs extension KT deliberately avoids.
  3. *The coordinator-flagged cost asymmetry — confirmed, but not decisive.* (a)'s ongoing
     per-producer tax at provably-simple habitats is indeed near-zero (the spiked one-liner), and
     **every** remaining producer has simplicity in scope: hypothesized (cut arm, L7, via the
     conditioning), owed anyway (L6's `G′`), or trivial (base sub-cases). So (a)'s real long-run
     cost is not the tax — it is the one-time third restatement wave plus the two permanent items
     in 4–5. The asymmetry makes (a) *affordable*, not *better*.
  4. *Chart-image characterization.* Under (a) the membership headline is conditioned forever
     (`pencilChartFramework` reads `G.endsOf e`, so parallel edges get literally equal extensors),
     and every *future* chart — W4's graded extension (N6 blueprint) — inherits a conditioned
     headline. "4-conjunct motive = exact projective chart image" is the design property D6 was
     built for; (b′) preserves it unconditionally. Re-seeding survives under both (its input
     self-scopes under (a)).
  5. *Maintenance / faithfulness.* Given conjuncts 1–2, conjunct 5 carries **zero geometric
     information beyond "G has no parallel class"** — a graph predicate in realization clothing;
     (b′) keeps graph-class scoping in the graph hypothesis, where KT puts it (and the motive
     docstring's "KT no-two-hinges-parallel analogy becomes literal" overstates: KT's
     nondegenerate-hinge form, `def:genuine-hinge-realization` = KT eq. (6.1), has no
     per-parallel-edge clause). Under (a) the landed witness's deletion removes the
     compiler-checked record of the exact phenomenon that motivates the conditioning; under (b′)
     it stays in-tree as the living answer to "isn't `Simple` redundant next to feasibility?".
     Reversibility is asymmetric: under (b′) the (a)-style headline stays reachable as a later
     bolt-on corollary (mint the 5-conjunct predicate, compose with the forcing lemma); under (a)
     the unconditional chart headline is not recoverable.

  **Long-run recommendation: (b′), HIGH confidence** — the projection independently reproduces the
  immediate-cost recommendation. (a) wins only the single-hypothesis aesthetics of the final
  generic statement (and that is recoverable later under (b′)); its permanent costs — the
  conditioned chart headline inherited by every future chart, the program-level split from the
  landed pair's pattern, a third `IsNondegPencilRealization` restatement wave on a tower that
  stabilized only after two — are not recoverable under (a). **User adjudication (2026-07-24,
  verbatim):** asked "With the long-run recon in: which repair route for the `PencilPair` motive?",
  the user selected "(b′) Simple-condition the pair (Recommended)". **Landed same day**: `PencilPair`
  restated to `(G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G) ∧
  HasPencilRealization K n G` (`Molecule/Pencil/Motive.lean`), the loop arm one-line fixed, the
  `not_simple_of_parallel` vacuity helper landed (`Motive.lean`), and the blueprint
  `def:pencil-conditioned-pair`/`thm:pencil-conditional-realization-pair` nodes restated
  (`pencil.tex`) — see `notes/Phase39.md` *Decisions made* for the commit-level record.
  **Cut-arm finding (2026-07-24, the dispatched confrontation of the route-neutral sharpening
  above; derivations checked against the landed definition bodies, restriction infra
  compiler-checked).** The cut arm's generic half is gapped on **both** sides of its side-IH
  consumption, and both gaps localize to a single phenomenon: **a cut endpoint of `G`-degree
  exactly `3` changes hub status between `G` and its side** (degree `≥ 4`: hub in both; degree
  `≤ 2`: non-hub in both — only the two endpoints of the single crossing edge can change degree
  at all).

  1. *Input gap (demotion — the recorded wrinkle, now confirmed with an explicit scenario).*
     Restricting `G`'s feasibility witness to a side `G.induce Vᵢ` fails the fourth conjunct at a
     demoted endpoint `u_c` (a `G`-hub, side non-hub): nothing in the four conjuncts constrains
     the side-closed-neighbourhood point triple at a `G`-hub. Explicit scenario: `G = K_{1,3}`
     (hub `u_c`, leaves `w₁, w₂, v_c`, cut edge to `v_c`) admits a full nondegenerate witness with
     `point u_c, point w₁, point w₂` spanning only a 2-plane — the two side hinges then *coincide*
     as lines (each is the span of its two endpoint points, forced by conjunct 2 + `Meet.lean`'s
     Plücker injectivity), and the side `P₃`'s fourth conjunct at `u_c` fails. Side feasibility as
     a *proposition* is not refuted (P₃ has other witnesses); the *restriction route* is. What
     does restrict is now landed (`Motive.lean`): `IsNondegPencilRealization.mono` (everything
     but the fourth conjunct at demoted hubs, taken as the explicit `hdemote` residual) and
     `PencilNondegFeasible.mono` (feasibility descends along `H ≤ G` when every demotion lands at
     `H`-degree `≤ 1`, where the 2-member closed neighbourhood rides the adjacent-point conjunct
     — the `≤ 1` bound is sharp).
  2. *Output gap (promotion — NEW, beyond the recorded wrinkle).* Dually, the glued realization
     owes `G`'s **third** conjunct at the same endpoint: `u_c` is a `G`-hub, so
     `G.closedHubNbhd` at `u_c` (and at each of `u_c`'s neighbours) gains `normal u_c` — but the
     side witness never constrains `normal u_c` against its neighbours' normals (the side's
     fourth conjunct constrains *points* there), and `normal u_c` is *forced* by the side's own
     hinges (orthogonal to their 3-dim span), so no repositioning of the *other* side can repair
     a dependent choice, and transports of the demoted side preserve its dependencies. The side
     IH's motive simply does not supply what the glue needs at a promoted endpoint.

  **Cut-arm route verdict (2026-07-24 recon; supersedes the earlier UNVERIFIED candidate-repair
  paragraph; the load-bearing compositions compiler-checked in a scratch spike, deleted — the
  drop brick below was proved sorry-free in the spike, not merely typechecked).** The `Gᵢ⁺`
  edge-closed-sides repair is CONFIRMED as the IH-consumption shape wherever it applies, and its
  two feared costs dissolve (1a/1b below). The arm splits into four sub-cases; three are
  buildable now (leaf list below), and one sharply-scoped residual — the **degree-3 pendant
  sub-case (4)** — stays design-open, with a candidate chart route and two refuted dodges
  recorded. `Gᵢ⁺` is simply **`G.induce (Vᵢ ∪ {far endpoint})`**: with `≤ 1` crossing edge this
  graph has exactly the side's edges plus the cut edge, so every `Vᵢ`-vertex keeps its full
  `G`-degree and the far endpoint drops to degree `1`.

  1. ***`|C| = 1`, both `|Vᵢ| ≥ 2` (the generic sub-case): CONFIRMED on `Gᵢ⁺`.*** IH inputs:
     feasibility descends by the landed `PencilNondegFeasible.mono` (composition spike-checked;
     the only obligations are two small degree lemmas — `Vᵢ`-degrees preserved, far endpoint
     degree `= 1`, both from `(G.cutEdges V₁).ncard ≤ 1` + looplessness); simplicity by
     `Simple.mono (G.induce_le …)` (the panel sibling's own move); measure
     `|V(Gᵢ⁺)| = |Vᵢ| + 1 < |V(G)|` exactly from `2 ≤ |V₃₋ᵢ|` (spike-checked); and the
     reduction's `hcut` IH shape (`∀ G', V(G').Nonempty → V(G').ncard < V(G).ncard → P G'`,
     `Induction/ForestSurgery/Reduction.lean`) hands the IH at *arbitrary* smaller graphs, so
     consuming it at `Gᵢ⁺` is already permitted — no reduction change.
     - *(1a) Rank/deficiency: NO shared-edge assembly exists or is needed — regrouping closes it
       with the landed disjoint-sides bricks plus ONE new small brick.* Consume the IH rank at
       `Gᵢ⁺` (target `6|Vᵢ| − def(G[Vᵢ]) − 1`, via the bookkeeping `def(Gᵢ⁺) = def(G[Vᵢ]) + 1`
       — `deficiency_eq_of_cutEdges_ncard_le_one` applied *inside* `Gᵢ⁺` at its singleton far
       side, whose induced side is edgeless with deficiency `0`), then **drop the cut edge's
       rows** to get exactly the induce-side lower bound `6(|Vᵢ|−1) − def(G[Vᵢ]) ≤ finrank Sᵢ`
       the landed `finrank_span_rigidityRows_cutEdge_eq` wants as `hlbᵢ`; that landed assembly
       then closes the glued rank verbatim — its `(D−1)|C|` crossing term recovers the dropped
       `5` and the arithmetic balances exactly. The drop step is the one new rank brick,
       **proved sorry-free in the spike** (≈40 lines: rows of the larger graph = rows of the
       smaller ∪ the extra edge's block image; a swapped-orientation row is the image of the
       negated block row, `hingeRow v u r = hingeRow u v (−r)`; then `Submodule.span_union` +
       `span_image` + `finrank_sup_add_finrank_inf_eq` + `Submodule.finrank_map_le` +
       `finrank_hingeRowBlock`):

       ```lean
       theorem finrank_span_rigidityRows_le_add_of_links_subset {k : ℕ} [Finite α]
           {G' Gs : Graph α β} (ext : β → ScrewSpace K k) {e₀ : β} {u₀ v₀ : α}
           (hl₀ : G'.IsLink e₀ u₀ v₀) (hext₀ : ext e₀ ≠ 0)
           (hlinks : ∀ e u v, G'.IsLink e u v → Gs.IsLink e u v ∨ e = e₀) :
           Module.finrank K (Submodule.span K
               (⟨G', ext⟩ : BodyHingeFramework K k α β).rigidityRows)
             ≤ Module.finrank K (Submodule.span K
               (⟨Gs, ext⟩ : BodyHingeFramework K k α β).rigidityRows) + (screwDim k - 1)
       ```
     - *(1b) Matching transport: decomposes by the crossing endpoints' `G`-hub statuses; the
       matches and steerings needed are complementary, never simultaneous at one endpoint.*
       Since endpoint degrees are preserved in the own side, "hub in `G`" = "hub in the own
       side" at `u_c`/`v_c`. Keep side 1 fixed, transport side 2 by a contragredient pair
       `(g, h)` (the landed `exists_contragredient_linearEquiv` /
       `hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv` infra). Per endpoint,
       exactly one of two obligations arises: at a **non-hub** endpoint, a *projective point
       match* (e.g. `g (point₂ v_c) = b • point₁ v_c`) — it makes the own-side fourth conjunct
       at the *other* endpoint transfer by unit-rescaling congruence, makes the two sides'
       cut-edge hinges projectively equal (each side's hinge is forced onto
       `extensor ![point u_c, point v_c]` by the two through-points + pair-LI, the Meet.lean
       forcing), and makes the needed cross-incidence *automatic* (via the side's own
       `dotProduct_point_eq_zero_of_mem_closedNbhd` at the far endpoint, transported through
       the match). At a **hub** endpoint (say `v_c` a `G`-hub), the glued **third** conjunct at
       `u_c` gains the member `normal v_c` — the finding's output gap — and the transport must
       instead *steer*: `h (normal₂ v_c) ∉ span(side-1 normals on G₁⁺.closedHubNbhd u_c)`, an
       open condition with genuine freedom because the glued far-point line is itself movable;
       satisfiability is fed by `G`'s own feasibility (its witness +
       `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` bound `|G.closedHubNbhd u_c|
       ≤ 3`, so the side family has `≤ 2` members), and unmatched ends owe their cross-incidence
       explicitly (the landed `exists_reposition_cross_incidences` shape). So the new geometric
       core is a **strengthened repositioning lemma** — the landed repositioning extended by up
       to two `∉ span` open conditions — plausibly `[Infinite K]` (the panel sibling
       `case_cut_edge_realization_gp_gen` is `[Infinite K]` for its analogous genericity step;
       its polynomial method is available here as a proof technique). This is the one
       risk-carrying leaf of the sub-case; everything else is transfer bookkeeping.
       **[Superseded in one respect by the L5-cut-iii landing, 2026-07-25 (leaf bullet below):
       the point matches proved unnecessary — the landed lemma is match-free, uniform across
       hub statuses, and any-field.]**
       *(Why not mirror the panel GP arm's seed/polynomial proof wholesale: the pencil chart is
       non-local in hub structure — `closedHubNbhd_{G}(u_c)` gains `v_c` over
       `closedHubNbhd_{G₁⁺}(u_c)` exactly when `v_c` is a `G`-hub, so side-chart row polynomials
       do not literally embed in `G`'s chart; the realization-level transport glue, mirroring
       the landed bare cut arm, avoids that mismatch uniformly.)*
  2. ***`|C| = 0`: buildable now, easy.*** No demotion anywhere (no crossing edges ⟹ induce
     sides preserve degrees), so feasibility restricts by `.mono` with blanket hub preservation;
     both `closedHubNbhd`/`closedNbhd` localize to the own side, so all four glued conjuncts
     transfer wholesale with no transport, no steering, no `[Infinite K]`; rank exactly as the
     landed bare `|C| = 0` branch with the generic side ranks.
  3. ***`|V₃₋ᵢ| = 1` (pendant/isolated far side) with `deg_G u_c ≠ 3`: buildable.*** Here
     `G = H + pendant v_c at u_c` (or `+ isolated v_c`, which case 2 covers), `H := G.induce V₁`,
     and `G₁⁺ = G` makes the `Gᵢ⁺` trick inapplicable — but there is no hub-status change:
     `deg_G u_c ≥ 4` keeps `u_c` a hub of `H` (feasibility restricts by blanket `.mono`; every
     closed-hub-neighbourhood is *unchanged* between `H` and `G`, so the IH witness's third
     conjunct covers all promoted-looking families verbatim), and `deg_G u_c ≤ 2` keeps it a
     non-hub (the one new obligation, the glued fourth conjunct at `u_c` gaining `point v_c`, is
     discharged by *choosing* the fresh pendant data: pick the hinge plane
     `P ∋ point u_c` inside `normal u_c ^⊥` with `P ⊄ span(H-family)` — always possible,
     `3`-dim vs `≤ 2`-dim — then `point v_c ∈ P` off the bad span and `normal v_c ⊥ P`). Rank:
     the landed `finrank_span_rigidityRows_cutEdge_eq` applies **verbatim** with the singleton
     side (its induced side is edgeless: span `⊥`, `hlb₂ = 0 ≤ 0`), so the pendant adds exactly
     `5` — no new rank work at all.
  4. ***`|V₃₋ᵢ| = 1` with `deg_G u_c = 3`: OPEN — the arm's residual core, and exactly the
     finding's `K_{1,3}` configuration.*** Not vacuous: `K₃ + pendant` is simple, feasible
     (hand-checked witness: `normal ≡ e₃`-style with points `e₀, e₁, e₂, e₀+e₁+…` — a routine
     assignment), ¬2EC, and its only `≤ 1`-crossing cuts are the singleton ones. Both gaps
     concentrate here irreducibly, and **a sharpening beyond the original finding: NO
     IH-consumption can close the output gap in this sub-case.** The promoted normal
     `normal u_c` is *forced* (up to scale) to `cross₃` of the point triple at `u_c` by the
     side's own two hinges (whose distinctness the side's fourth conjunct itself guarantees),
     and its independence from the neighbours' hub families is constrained by *no* conjunct of
     any witness in which `u_c` is a non-hub; but every `|V|`-smaller graph containing `H`'s
     content has `u_c` a non-hub — the only way to keep `deg u_c ≥ 3` on `≤ |V(G)| − 1` vertices
     is to add an `H`-internal edge at `u_c`, and that variant fails on *both* sides (its new
     edge's incidences are constraints `G`'s witness does not satisfy, so input feasibility
     breaks; and its deficiency drop is not controlled, so the rank arithmetic can fall short by
     up to `5`). Consequences for the recorded options:
     - *(option (c) — extend the fourth conjunct to degree-3 hubs — REFUTED as a full repair.*
       It closes the *input* gap only (the demoted body's triple-LI would restrict); the
       *output* gap — the glued third conjunct at `u_c` and its neighbours gaining the forced
       `normal u_c` — survives it untouched, so the L4-wave restatement it costs buys only half
       a repair. Do not take this route for the cut arm.)
     - *(a uniform motive strengthening that would close the output gap — carrying conjunct-3
       LI over all degree-`≥ 2` neighbours, whose normals are equally forced — is REFUTED by
       cardinality: at a hub with three degree-`≥ 2` neighbours it demands `4` LI normals inside
       the `3`-dim `point^⊥`, making exactly the cubic 2EC habitats W5 lives on infeasible.)*
     - **Candidate route (the one workable shape found): steer both witnesses on their own
       charts via the landed engine.** (i) *Input:* re-seed `G`'s feasibility witness
       (`exists_pencilSeed_of_nondeg`) and steer it on `G`'s chart
       (`exists_common_seed_pencilRow_and_polynomials`, `[Infinite K]`) so the triple
       `{point u_c, point w₁, point w₂}` becomes LI — a polynomial condition in the seed; then
       the steered witness *restricts* to `H` (the landed `.mono`'s `hdemote` residual is
       exactly that triple), giving `PencilNondegFeasible K H` and firing the IH's generic
       half. (ii) *Output:* re-seed the IH's `H`-witness and steer it on `H`'s chart so the
       `≤ 3` promoted-family conditions (`cross₃`-forced `normal u_c` off each neighbour
       family's span — all polynomial in `H`-seeds, since `closedHubNbhd` members are hubs
       whose chart normals are free seeds) hold alongside the rank rows (rank transfers along
       re-seeding because row blocks depend only on extensor *lines*, and the chart hinges
       reproduce the witness's hinges projectively). (iii) Extend the pendant as in sub-case 3.
       The residual obligations are the two *somewhere-witness* constructions (a seed of `G`
       with the triple LI; a seed of `H` with the promoted families LI) — bounded geometric
       constructions of the same flavor as L6's witness-seed charter, NOT rank certificates
       (not L7-hard), but genuinely new; and the route pulls the chart stack
       (`Chart`/`Engine`/`Reseed`) into the arm's import cone. **Assessed 2026-07-25: GO — the
       two somewhere-witnesses exist and the composition is viable end-to-end; canonical
       verdict + pinned statements + leaf list in the L5-cut-v bullet below.**

  **Feasibility propagation as a proposition (the finding's open alternative — now bounded, not
  settled).** A NEW obstruction mechanism found this recon (derivation-checked against the
  landed incidence lemmas `dotProduct_point_eq_zero_of_mem_closedNbhd` /
  `dotProduct_normal_eq_zero_of_mem_closedNbhd` and the motive conjuncts; the linear-algebra
  cores are 2- and 3-member perp squeezes in `K⁴`): **a triangle with `≥ 2` pencil-hub vertices
  is infeasible.** With two adjacent hubs `y, z`, conjunct 3 at `y` forces `normal y, normal z`
  LI; all three triangle points are orthogonal to both (each vertex is in both closed
  neighbourhoods), hence lie in the `2`-dim common perp — if the third vertex `x` has degree
  exactly `2` its fourth conjunct (a `3`-member `closedNbhd` triple in a `2`-dim space) fails;
  if all three are hubs the three points are squeezed into the `1`-dim common perp of three LI
  normals and even conjunct 2 fails. Consequences: (a) "every `closedHubNbhd` has `≤ 3` members
  ⟹ feasible" is FALSE in general (the "net" graph — a triangle with a pendant at each vertex —
  has all closed hub-neighbourhoods of size `≤ 3` yet is infeasible), so a purely combinatorial
  feasibility criterion cannot rescue the original induce-side route; L6's *habitat-restricted*
  claim is untouched (its 2EC/no-proper-rigid habitat has no triangles at all for `|V| ≥ 4` — a
  triangle is a proper rigid subgraph there, the same fact the (b′) `G′.Simple` bullet uses).
  (b) No counterexample to downward propagation itself is known: this mechanism is
  upward-monotone (hubs stay hubs and links persist upward, so a side exhibiting it makes `G`
  infeasible too), and a demotion-activated infeasibility needs a forcing structure that so far
  always promotes into `G`. Proving propagation in general would require classifying all forcing
  mechanisms — open research, NOT a bounded leaf; it is also *insufficient alone* for sub-case 4
  (the output gap stands regardless), which is why the chart-steering candidate above carries
  both halves.

  **Successor demand check (is the full arm needed?).** `Graph.pencil_reduction` dispatches
  *every* loopless ¬2EC graph on `≥ 3` vertices to `hcut`, and the spiked
  `pencil_conjecture_of_arms_pair` instantiates `P := PencilPair` — whose generic half the
  contract/split arms will consume at arbitrary smaller graphs (which may be ¬2EC). So the cut
  arm is needed at the full conditioned strength (`G.Simple → PencilNondegFeasible → generic`);
  the only conceivable weakening — conditioning the *motive's* generic half away from the
  residual sub-case — would re-open the settled (b′) motive and silently drop honest instances
  (`K₃ + pendant` is simple + feasible), so it is not on the table without user adjudication.

  **Leaf decomposition (build order; sub-cases 1–3 buildable now).**
  - **L5-cut-i** (**LANDED 2026-07-25**, `notes/Phase39.md` *Decisions made*; one commit,
    `Motive.lean` + `RigidityMatrix/Bricks.lean`): the `Gᵢ⁺` structure
    layer — the two degree lemmas for `G.induce (Vᵢ ∪ {far})` under `≤ 1` crossing; the
    feasibility corollary (the spike's composition through `.mono`); the deficiency bookkeeping
    `def(Gᵢ⁺) = def(G[Vᵢ]) + 1` (needs induce-idempotence `(G.induce S).induce T = G.induce T`
    for `T ⊆ S` — mint if the graph library lacks it); and the spike-proved drop brick
    (statement above; home `Bricks.lean` §CutEdgeBrick). Also move (or re-home pointers to)
    `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` +
    `dotProduct_{point,normal}_eq_zero_of_mem_closedNbhd` so `Pair.lean` can consume them
    without importing the chart stack — they are motive-consequence lemmas, currently homed in
    `Engine.lean` (import-cone decision for the builder: move to `Motive.lean` if their
    `finrank_toDualPerp_single_eq` dependency allows, else `Pair.lean` imports `Engine`).
  - **L5-cut-ii** (**LANDED 2026-07-25**, `notes/Phase39.md` *Decisions made*; one commit,
    `Statement.lean` + `Motive.lean` + a `LinearIndepOn` mirror lemma): transport + transfer
    bookkeeping, all five pieces. `IsNondegPencilRealization.mapSupport_screwEquivOfLinearEquiv`
    (`Motive.lean`) layers conjuncts 2–4 over the landed conjunct-1 transport
    (`hasPencilPanelRealization_mapSupport_screwEquivOfLinearEquiv`) by injectivity of `g`/`h`
    alone (`LinearIndependent.map_injOn`/`LinearIndepOn.map_injOn`); the forced-hinge lemma
    `exists_smul_eq_extensor_of_extensorThroughPoint_pair` (`Statement.lean`) is exactly the
    Meet.lean composition (`span_range_eq_of_extensor_eq` +
    `exists_smul_extensor_eq_of_mem_span_range`); the four scale-invariance iffs
    (`extensorInPanel_smul_iff`/`_normal_iff`, `extensorThroughPoint_smul_iff`/`_point_iff`,
    `Statement.lean`) are stated at the concrete grade `k = 2` (a generic `{k : ℕ}` hits
    `OfNat (Fin k) 0` indexing the witness family's first slot — TACTICS-QUIRKS-adjacent, no new
    entry needed); `LinearIndepOn.units_smul` mirrors mathlib's own
    `LinearIndependent.units_smul` (`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`); and the
    boundary identities `Graph.closedNbhd_induce_union_singleton` (equality, no exception) /
    `Graph.closedHubNbhd_induce_union_singleton` (`= G.closedHubNbhd v \ {w₀}`, the "single `u_c`
    exception") land in `Motive.lean`, via the shared subset helper
    `Graph.closedNbhd_subset_of_mem`. Two build-time frictions hit, both already-documented
    idioms (no new entries): the `OfNat (Fin k) 0` generic-grade trap above, and a self-referential
    `rw [hj0]` over-rewrite (TACTICS-QUIRKS § 41 family) fixed by rewriting a fresh named
    hypothesis forward instead of substituting a derived equation into the goal.
  - **L5-cut-iii** (**LANDED 2026-07-25**, `notes/Phase39.md` *Decisions made*; one commit,
    `Arms.lean` + the mirrored `Submodule.exists_mem_notMem_notMem`): the strengthened
    repositioning lemma `exists_reposition_cross_incidences_avoiding`. **Route correction found
    by the leaf's spike (the F9 pattern, this time in the favorable direction):** the point
    *matches* this bullet originally pinned for non-hub ends are UNNECESSARY — the conjunct-4
    transfers they were routed through are equally served by span-avoidance inserts
    (`LinearIndepOn` insert off the fixed family's span), so the landed lemma is ONE uniform
    statement for all four hub-status combinations: the cross-incidence pair + four `∉ span`
    conclusions against ≤ 2-generator span slots (padded with `0` when idle), over **any** field
    (no `[Infinite K]`, no polynomial method), with only the four nonzero-ness hypotheses.
    Everything pulls back through the contragredient identity to prescribed values of `g` on a
    perp-picked 4-frame; satisfiability is dimension counting + the any-field two-proper-subspace
    exchange. The (1b) sufficiency map (which conclusion feeds which glued conjunct) is recorded
    in the lemma's docstring; the `≤ 3` closed-hub-neighbourhood bound enters on the consumer
    side only (presenting each avoided family as a 2-generator span), so the cardinality logic
    lands in L5-cut-iv.
  - **L5-cut-iv**: the arm assembly `pencilPair_of_not_twoEdgeConnected` — generic half wiring
    sub-cases 1–3 (bare half = the landed W3-L4 `hasPencilRealization_of_not_twoEdgeConnected`),
    with sub-case 4 carried as an explicit hypothesis until its route lands (the standing
    no-`sorry` idiom). **Sub-case 2 landed standalone (2026-07-25)**, since the full assembly
    (four sub-cases + the carried hypothesis) is too large for one sitting: three disjoint-sides
    structure lemmas (`Graph.degree_induce_of_forall_isLink_mem` /
    `Graph.closedHubNbhd_induce_of_forall_isLink_mem` / `Graph.closedNbhd_induce_of_forall_isLink_mem`,
    `Motive.lean` — an adjacency-closed-set generalization of the `Gᵢ⁺` boundary identities, no
    exception since there is no far vertex to add) plus the sub-case-2 producer
    `hasGenericPencilRealization_of_cutEdges_eq_empty` (`Pair.lean`): glues the two sides' IH
    generic realizations exactly like the bare arm's own `|C| = 0` branch, with the three
    nondegeneracy conjuncts transferred wholesale via `LinearIndepOn.congr` composed with the new
    structure lemmas. **All three buildable sub-cases (2, 1, 3) are now landed** (2026-07-25);
    **L5-cut-iv is COMPLETE (2026-07-25):** the dispatch shell `pencilPair_of_not_twoEdgeConnected`
    (`Pair2.lean`) wires all four sub-cases together, sub-case 4 carried as the explicit hypothesis
    `hcutPendant3` — **conditioned on `G.Simple`/`PencilNondegFeasible K G`** (threaded from the
    ambient `hSimple`/`hfeas`), not just the pendant producer's own premises with the degree
    equality: dropping that conditioning makes the hypothesis unsatisfiable at the "net" graph
    (triangle + one pendant per vertex, infeasible per the triangle-`≥2`-hub finding above but
    matching every configuration premise), a defect a verification pass caught and a same-day
    corrective commit fixed (`notes/Phase39.md` *Decisions made*).

    **Sub-case 1's rank half landed (2026-07-25)**, a second standalone piece (the full sub-case
    re-derived at F9-contact confirmed it is much larger than sub-case 2 — a 2×2 hub-status split
    driving `exists_reposition_cross_incidences_avoiding`'s eight args, plus two `Gᵢ⁺` IH
    consumptions — so this shrank to the rank composition alone, mirroring L5-cut-i/ii/iii's own
    infrastructure-first landings):
    `hlb_induce_of_isNondegPencilRealization_induce_union_singleton` (`Pair.lean`, generic in
    `V₁`/`e₀`/`u₀`/`w₀` so the assembly applies it once per crossing endpoint) packages the IH's
    `Gᵢ⁺` rank + the drop brick `BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`
    (applied at `G' := Gᵢ⁺, Gs := G.induce Vᵢ, e₀ := e_c`) + the deficiency bookkeeping
    (`Graph.deficiency_induce_union_singleton`) into exactly the `hlbᵢ` shape
    `finrank_span_rigidityRows_cutEdge_eq` wants. New supporting infra: the drop brick's own
    `hlinks` case-dispatch, `Graph.isLink_induce_union_singleton_of_isLink` (`Motive.lean` — both
    endpoints in `Vᵢ` survive the induce directly, one endpoint the far vertex forces the edge to
    `e₀` via `Graph.eq_cutEdge_of_isLink_crossing`, both endpoints the far vertex is a loop);
    `Graph.cutEdges_diff_subset` (`Deficiency.lean`, general: an edge crossing `V(G) ∖ V'` also
    crosses `V'` by an endpoint-swap) — side 2's own `(G.cutEdges V₂).ncard ≤ 1` derives from side
    1's through this, needed for side 2's own `Gᵢ⁺` construction; `exists_subset_pair_of_ncard_le_two`
    (`Pair.lean`, generic — an `ncard ≤ 2` set embeds in a two-element set, padding with an
    arbitrary element when smaller), the plumbing the *repositioning* half (below) will consume.
    Also re-homed `ncard_closedNbhd_le_three_of_not_pencilHub` `Engine.lean → Motive.lean` (the
    same import-cone reason as its `closedHubNbhd` sibling, L5-cut-i) since the repositioning half
    needs it chart-free too.

    **Sub-case 1's repositioning/gluing half landed (2026-07-25)**, closing sub-case 1's
    construction:
    `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`
    (`Pair.lean`) — a standalone producer taking the two `Gᵢ⁺` side witnesses (nondegeneracy +
    target rank) plus `G`'s own feasibility witness, delivering `HasGenericPencilRealization K n G`
    outright; the IH consumption (deriving the `Gᵢ⁺` inputs and firing the IH twice, where the
    both-sides-`≥ 2` condition enters) is the dispatch shell's remaining sub-case-1 work
    (`notes/Phase39.md` *Hand-off*). Built exactly as this bullet's guidance pinned, with one
    structuring refinement: the 2×2 hub-status split lives in four up-front slot-choice `obtain`s
    (conditional covers via `exists_subset_pair_of_ncard_le_two` + the
    `≤ 3`-minus-crossing-endpoint bounds; the q-slot pads with `point₁ u_c` itself in the hub
    branch, so `point₁ u_c ∈ span {q₁, q₂}` holds unconditionally and
    `LinearIndependent.pair_iff'` closes the cut pair-LI in every branch — the recorded
    no-forced-match insight), the repositioning lemma is called ONCE, and each glued conjunct does
    a local insert-vs-`congr` split at the crossing endpoint (`LinearIndepOn.insert` off the
    covered span, one avoidance conclusion each, over the `Gᵢ⁺` boundary identities).

    **Sub-case 3 landed (2026-07-25)**, a third standalone producer (new file `Pencil/Pair2.lean`
    — `Pair.lean` was at the `~1500`-LoC cap):
    `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant` takes `H := G.induce
    V₁`'s IH-supplied witness directly (no `Gᵢ⁺`, since the pendant IS the far side, so the closure
    trick degenerates to `Gᵢ⁺ = G`). Confirms this bullet's own guidance: `u_c`'s hub status never
    changes under `deg_G u_c ≠ 3`, landed as the general (no pendant-configuration hypothesis)
    `Graph.pencilHub_iff_induce_of_degree_ne` plus its two degree-lemma inputs
    (`Graph.degree_induce_eq_of_ne` / `Graph.degree_eq_degree_induce_succ`, `Motive.lean`) — so
    unlike sub-case 1 there is no hub-status case split anywhere in the construction. The fresh
    pendant data (`normal v_c`/`point v_c`) is chosen by a dimension-count generalizing
    `exists_perp_linearIndependent` from a single vector to a small span
    (`SetLike.not_le_iff_exists` against a `≤ 2`-generator cover of `H.closedNbhd u_c`, then
    `le_finrank_toDualPerp_inf` for the joint perp); rank closes by
    `finrank_span_rigidityRows_cutEdge_eq` verbatim (`hlb₂ = 0`, pendant side edgeless). No new
    rank work, confirming the "no new rank work at all" prediction below.
  - **L5-cut-v: GO — route PINNED (2026-07-25 assessment recon; numerics-first, then a
    compiler-checked composition spike, deleted).** The chart-steering candidate route
    (item 4 above) is viable end-to-end; both somewhere-witness constructions exist and are
    generic, not knife-edge. The residual is L6-flavored bounded geometry as hoped — no
    L7-style rank certificate anywhere in it.
    - *Numerics (exact rationals, mirroring the Lean chart definitions — `cross₃` as the
      cofactor determinant `cross₃_apply`, chart points/normals with sorted-enumeration
      selectors, point-join hinges, 15 annihilator rows per edge).* On `K₃+pendant`,
      `C₄+pendant`, and a double-star tree (`u`–`a`,`u`–`w`,`u`–`p`,`a`–`b₁`,`a`–`b₂` — the
      instance with a genuine 2-member promoted family `{forced n_u, free n_a}` and both
      demoted-triple points confined to one 2-dim perp): the input witness (demoted triple LI
      on `G`'s chart) and the output witness (promoted families LI on `H`'s chart) were each
      found at the FIRST random seed, and the full glued `G`-realization passes every
      nondegeneracy conjunct and attains the exact rank target (`17`/`23`/`25`
      `= 6(|V|−1) − def`). Adversarial instance (triangle `u_c w₁ w₂` + pendants making
      `u_c` AND `w₁` hubs): the promoted family at `u_c` is IDENTICALLY dependent (40/40
      seeds — `n(w₁)` is structurally orthogonal to all three triple points, so it is forced
      onto the same 1-dim triple-perp as the forced normal) while `H` itself stays feasible —
      the obstruction is real, unfixable by steering, and excluded EXACTLY by `hcutPendant3`'s
      `PencilNondegFeasible K G` antecedent (that `G`'s triangle has two hubs, the
      triangle-`≥2`-hub finding). A Hall-type dimension count over the per-body allowed perps
      shows this is the ONLY obstruction family for both witnesses: every coincidence that
      pinches the demoted triple or a promoted family into a too-small subspace forces
      `w₁ ~ w₂` with a second hub among `{u_c, w₁, w₂}` — infeasible for `G`.
    - *The two pinned witness statements (spike-typechecked shapes).* (i) *Input:* under the
      sub-case-4 configuration plus `hSimple`/`hfeas`, the two `V₁`-links `e₁ : u_c–w₁`,
      `e₂ : u_c–w₂` (`w₁ ≠ w₂`), and any `hubSel` with
      `∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v)`:
      `∃ q : α × Fin 4 × Fin 4 → K, LinearIndependent K
      ![pencilChartPoint (PencilSeed.ofCoord q) hubSel u_c, … w₁, … w₂]`.
      (ii) *Output:* on `H := G.induce V₁`'s chart, under the same configuration and any
      WF-correct `hubSel`/`nbrSel` pair for `H`:
      `∃ q, ∀ v ∈ ({u_c, w₁, w₂} : Set α), LinearIndepOn K
      (pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel (G.induce V₁))
      (G.closedHubNbhd v)` — the family function needs no by-cases: at `H`-hubs
      `pencilChartNormal` reads the free seed normal, and at the demoted `u_c` its non-hub
      branch IS the forced `cross₃` of the demoted triple.
    - *Composition findings (the full producer spike-typechecked end-to-end, leaves
      `sorry`'d).* (1) The producer's conclusion is exactly `hcutPendant3`'s conditioned
      conclusion, and its premises are `hcutPendant3`'s premises PLUS the reduction's `hIH` —
      which `hcutPendant3`'s statement does not carry. So the discharge **rewires the dispatch
      shell** (prove sub-case 4 inline in `pencilPair_of_not_twoEdgeConnected`'s
      `hdeg3 = 3` branches, where `hIH`/`hSimple`/`hfeas` are all in scope, and delete the
      carried hypothesis from the shell AND from `pencil_conjecture_of_arms_pair`), rather
      than proving `hcutPendant3` standalone — standalone is impossible, it has no IH.
      (2) **`[Infinite K]` is required** (the engine's common-non-root step) and propagates to
      the shell, the successor, and blueprint node `thm:pencil-conditional-realization-pair` —
      an expected statement change (the W5 device is `[Infinite K]` throughout; the conjecture
      is about genericity), NOT a motive change; restate the blueprint in the rewire commit
      (the statement-change gate). (3) The `PencilSeed.ofCoord` `fillNbr := fillHub` coupling
      (L3's 4-role coordinate space) does NOT block the route: chart points and hub normals
      never read `fillNbr`, and both the demoted triple and every promoted family are
      `fillNbr`-free (`nbrSel u_c` is fully assigned — `H.closedNbhd u_c` has exactly `3`
      members), so every steering condition lives on the existing 4-role space; the standing
      WF conditions are witnessed at the `fillNbr`-free flattening of the re-seeded seed
      (chart points there literally coincide with the re-seeded seed's), and `fillNbr` is
      re-chosen freely POST-steering at deg-`≤1` non-hub bodies (nothing else reads it). **No
      Engine restatement needed.** (4) Rank transfers along re-seeding: every witness hinge is
      forced projectively onto the point-join (`exists_smul_eq_extensor_of_
      extensorThroughPoint_pair`), chart points reproduce the witness's projectively, and row
      spans are invariant under per-edge nonzero extensor scaling; equality at the steered
      seed = an LI `pencilRow` subfamily of target size (`≥`) + the landed
      `finrank_span_rigidityRows_add_deficiency_le` (`≤`).
    - *Leaf decomposition (build order; v-b is the next commit).*
      **v-a LANDED (2026-07-25)**: `not_pencilNondegFeasible_of_triangle_two_hubs`
      (`Motive.lean`, any field) — the triangle-`≥2`-hub infeasibility finding as a lemma
      (conjunct-3 LI at two adjacent hubs `y, z`, then the 2- and 3-member perp squeezes in
      `K⁴`, case-split on the third vertex `x`'s own hub status); it gates both witness
      constructions' coincidence exclusions. Statement shape: `x y z : α` pairwise distinct,
      three edges `e₁ : x–y`, `e₂ : y–z`, `e₃ : z–x`, `y z` the two ADJACENT hubs (`hy hz :
      G.PencilHub _`); conclusion `¬ PencilNondegFeasible K G`. Two supporting lemmas moved
      `Engine.lean → Motive.lean` alongside it (same L5-cut-v-a import-cone reason as the
      L5-cut-i re-home): `linearIndependent_triple_of_linearIndepOn` (the `Fin 3` triple
      transfer, W5-L4's own arity-3 glue) and `finrank_toDualPerp_triple_eq` (the `1`-dim
      triple-perp dimension count) — both fully general, no chart-stack dependency, so the
      move was available. **v-b**: witness (i) (statement above; construction: hub normals chosen LI
      per closed-hub-neighbourhood + the v-a exclusions, points hit by the landed arity
      sweeps). **v-c**: witness (ii) (same toolkit on `H`'s chart). **v-d**: steering
      bookkeeping — the "LI `≤3`-family of polynomial vectors at a witness ⟹ one
      somewhere-nonzero polynomial whose non-roots keep it LI" extraction gadget (pair-minor
      + `cross₃Poly` cases), the WF-conditions-at-the-flattening witnesses, and the
      post-steering `fillNbr` re-choice lemma. **v-e**: the input-half assembly
      `pencilNondegFeasible_induce_of_pendant_deg3` (re-seed → steer →
      `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF` → `.mono` with the
      steered triple as `hdemote`). **v-f**: the rank-transport bricks (the `pencilRow` ↔
      chart-`rigidityRows` link bridge — the Engine docstring's deferred "hends-style"
      consumer — proportional row-span invariance, LI-subfamily extraction) + the output-half
      steering assembly. **v-g**: the glue (sub-case-3-shaped; conjunct 3 at `u_c`/`w₁`/`w₂`
      from the steered promoted families, `hlb₂ = 0` rank verbatim) + the shell/successor
      rewire + the blueprint restatement.

    **v-b construction recipe (derived 2026-07-25, docs-only — de-risks the Lean landing, not
    yet attempted in Lean).** Re-deriving witness (i) against the CURRENT `Chart.lean`/
    `Motive.lean` definitions (F9) found the naive route (steer via the abstract arity-sweep
    lemmas `exists_cross₃_eq_of_ne_zero_of_dotProduct_eq_zero`/
    `exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero`, chaining their ABSTRACT
    outputs as inputs to a later sweep) is fragile: those lemmas' outputs are only known to
    satisfy an orthogonality property, not an explicit direction, so a later sweep cannot
    certify its own target avoids the earlier sweep's (unknown) output. The route that works
    instead uses ONLY the four standard basis vectors of `K⁴` (available over any field,
    matching the pinned statement's lack of an `[Infinite K]` hypothesis) and `cross₃`'s
    alternating-cofactor identity (`cross₃_apply`, `Chart.lean`): for `{a,b,c,d} = {0,1,2,3}`,
    `cross₃ e_a e_b e_c = ± e_d` (sign = the permutation parity; irrelevant since only the line
    matters). **Recipe:** `hubNormal u_c := e0`; if `w1` is a hub, `hubNormal w1 := e1` (else
    nothing to fix); if `w2` is a hub, `hubNormal w2 := e2`; every OTHER real hub-neighbour
    appearing in `closedHubNbhd u_c`, `closedHubNbhd w1`, or `closedHubNbhd w2` (`v_c` if it is
    a hub, or a "third party" hub adjacent to `w1`/`w2`) gets `e3`, and any genuine `fillHub`
    padding slot also gets `e3`. Every one of the three target triples then reads back as
    `{e0, x, y}` for two DISTINCT elements of `{e1,e2,e3}` (never a repeat), giving
    `pencilChartPoint u_c = ±e3`, `… w1 = ±e2`, `… w2 = ±e1` — three distinct basis directions,
    hence LI.

    **The two facts that make this watertight (both re-derived, not assumed):**
    (1) *Each of `w1`, `w2` has at most one "extra" hub-neighbour beyond `u_c`* — sharper than
    the blanket `ncard(closedHubNbhd v) ≤ 3` feasibility bound (which alone would allow TWO
    extras when `v` is not itself a hub, breaking the 4-basis-vector budget). The sharper bound
    is `Graph.PencilHub`'s own definition: `¬ G.PencilHub w1` means `G.degree w1 ≤ 2`, and `w1`
    already spends one of those `≤2` edges on `u_c`, leaving at most one more neighbour
    (paralleling the L5-cut-iv sub-case-3 pendant producer's own degree bookkeeping). This
    resolves what looked like a genuine gap on first pass: if a non-hub `w1` could have TWO
    third-party hub-neighbours `q1 ≠ q2` and `w2` (also non-hub) shared BOTH of them, `w1`'s and
    `w2`'s triples would read the identical multiset `{u_c, q1, q2}` and their chart points
    would be forced proportional no matter what seed is chosen — the degree bound rules this out
    (a non-hub vertex never has two "extra" hub-neighbours to begin with).
    (2) *When BOTH `w1` and `w2` are hubs, they are NOT adjacent* — else `u_c, w1, w2` form a
    triangle with `u_c` and (say) `w1` two adjacent hubs, contradicting `hfeas` via **v-a**
    (`not_pencilNondegFeasible_of_triangle_two_hubs`). Without this, `w2` would sit inside
    `closedHubNbhd w1` too, consuming `w1`'s only free slot and forcing `pencilChartPoint w1` to
    the SAME `±e3` as `u_c` — this is the one place v-a's exclusion is load-bearing for v-b (not
    merely "gates coincidences" in the abstract, as the leaf-list bullet above says, but rules
    out the specific collision above). `v_c` is never adjacent to `w1`/`w2` at all (any such
    edge would be a second crossing edge over `V1`, contradicting `hcut_le`'s `≤ 1` bound), so
    it never enters `closedHubNbhd w1`/`closedHubNbhd w2` — only `closedHubNbhd u_c`, where it
    is handled like any other "extra" (assigned whichever of `e1`/`e2` isn't already claimed by
    a hub `w1`/`w2`, since at most one of `v_c`/`w1`/`w2` — never `w1` and `w2` together with
    `v_c` — can be additionally a hub, by the `ncard ≤ 3` bound applied at `u_c` itself).

    **Lean landing, first slice (2026-07-25): the bridging facts + the cross₃ computational
    core, all landed.** The vendored `Matroid.Graph.Degree` library (this project's `Graph α β`
    is `Matroid.Graph`, not `Mathlib.Combinatorics.Graph` directly — the two share the base
    `IsLink`/`Adj` layer, with `degree`/`Simple`/connectivity API added on top by the vendored
    package) already carries the exact bridge needed: `Graph.degree_eq_ncard_adj [G.Simple] :
    G.degree x = N(G, x).ncard` (`.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean`).
    Landed in `Motive.lean` (general `Graph`/`Simple` infra, no chart/motive dependence):
    `Graph.neighbor_eq_of_degree_eq_three` (three distinctly-named neighbours of a degree-`3`
    vertex are its *only* neighbours — `degree_eq_ncard_adj` + `Set.ncard_eq_three` +
    `Set.eq_of_subset_of_ncard_le`) and `Graph.not_adj_of_ne_of_mem_of_cutEdges_le_one` (the
    pendant endpoint is never adjacent to a different `V₁`-member than the pinned cut edge's own
    endpoint — via the already-landed `Graph.eq_cutEdge_of_isLink_crossing` + `IsLink.right_unique`).
    Landed in `Engine.lean` (right after the arity-`3` sweep, `cross₃`-general infra):
    `linearIndependent_pi_single_triple` (three pairwise-distinct standard basis vectors of `K⁴`
    are LI, via `Pi.basisFun`'s own independence restricted along an injective `Fin 3 → Fin 4`)
    and `exists_smul_cross₃_pi_single` (`cross₃` of them is a nonzero multiple of the fourth — a
    direct instance of `exists_smul_cross₃_eq_of_linearIndependent` at `q := Pi.single d 1`, no
    new sign/order bookkeeping needed since only `LinearIndependent` is asked for). All four
    sorry-free, gates green (`lake build` warning-clean, `lake lint` clean), axioms clean
    (`propext`/`Classical.choice`/`Quot.sound` only).

    **What remains (the main assembly, scoped out this session — the shape is now fully mapped,
    not just "locate the API"):** define `index : α → Fin 4` by the recipe's case split
    (`u_c ↦ 0`, `w₁ ↦ 1`, `w₂ ↦ 2`, `v_c ↦` whichever of `1`/`2` isn't already claimed by a hub
    `w₁`/`w₂` (`if G.PencilHub w₁ then 2 else 1`), every other vertex `↦ 3`); take
    `q : α × Fin 4 × Fin 4 → K := fun p => if p.2.1 = 0 then Pi.single (index p.1) 1 p.2.2 else
    Pi.single 3 1 p.2.2` (role `0` reads `index`, every fill role reads the constant `e₃`, so
    `(PencilSeed.ofCoord q).hubNormal v = Pi.single (index v) 1` and `.fillHub v j = Pi.single 3
    1` for every `v, j` — two one-line `funext`/`if`-unfold checks, `Fin.succ_ne_zero` closing the
    role case). The only nontrivial residual is `Set.InjOn index (G.closedHubNbhd u_c)`, needed
    to invoke `exists_smul_cross₃_pi_single` at each of `u_c, w₁, w₂` (their own triples read off
    `index` at whatever `hubSel` selects, in *some* order — irrelevant to `LinearIndependent`,
    but the *values* fed to `cross₃` must be pairwise distinct for the lemma's hypotheses):
    - At `u_c`: `closedHubNbhd u_c ⊆ {u_c, v_c, w₁, w₂}` (`Graph.neighbor_eq_of_degree_eq_three`
      at `u_c`'s three named edges, `PencilHub`'s own `∈ V(G)` conjunct restricting further to
      hubs), and `index` is injective on it *given* `v_c, w₁, w₂` are not ALL simultaneously
      hubs — ruled out by `(closedHubNbhd u_c).ncard ≤ 3` (from `hHubSel u_c`'s
      `IsFin3SelectorOf`, which embeds the target set into `Fin 3`) against the 4 pairwise-distinct
      elements `{u_c, v_c, w₁, w₂}` a witness to all-three-hub would put inside it.
    - At `w₁`/`w₂`: `closedHubNbhd w₁ ⊆ {u_c, w₁} ∪ {≤ 1 more}` — the `≤ 1` bound is the sharper
      fact `notes/Phase39.md` *Decisions made* already flags (a non-hub `w₁` has `degree ≤ 2`,
      already spent on `u_c`, leaving no room for a *second* extra neighbour — the blanket
      `ncard ≤ 3` bound alone would wrongly allow two), so `index`'s "everyone else ↦ 3" default
      never collides with itself; `Graph.not_adj_of_ne_of_mem_of_cutEdges_le_one` (already landed)
      additionally confirms `v_c` is never that "≤ 1 more" (not adjacent to `w₁`/`w₂` at all), and
      v-a excludes the other adjacency collision (`w₁ ~ w₂` while both hubs) exactly as recorded
      above.
    Then `cross₃ (hubSlotNormal … u_c 0) (… 1) (… 2)` rewrites (via the `index`-agreement
    identities) to `cross₃ (Pi.single (index ·) 1)` at the three slot values, feeding
    `exists_smul_cross₃_pi_single` directly; the final `LinearIndependent` follows from three
    pairwise-distinct missing indices (`3, 2, 1` respectively, by construction) via
    `LinearIndependent.units_smul`-style per-body nonzero-scalar transport (already the
    project's standing idiom, e.g. `exists_pencilSeed_of_nondeg`'s own closing step). **Next:
    attempt this assembly fresh** — the per-vertex `InjOn` arguments above are the only
    genuinely new case-work; everything else is now pinned to a concrete rewrite chain.

- **W5-L6**: habitat feasibility (verdict 4) — the ≤ 3 closed-hub-neighbourhood lemma
  on 2EC/no-proper-rigid graphs + the witness-seed construction discharging
  `PencilNondegFeasible` at `G′ = G^{ab}_v`. **Extended by the L5 blocker verdict, per the landed
  (b′) restatement:** also owes `G′.Simple` (the no-triangle-at-`v` habitat argument
  above) for the split arm's generic-IH consumption.
- **W5-L7** (the research core): the single-candidate Claim-6.12 replacement — at the
  Case-III habitat, a chart seed of `G′` realizing rank `6(|V|−2)` *and* the
  candidate-`M₁` escape `r ⬝ Λ²Π̂(a) ≠ 0` (then the assembly + the output's own
  nondegeneracy conjuncts). The product route reduces it to a ≢-0 certificate for the
  escape polynomial on the chart; N2's seeds witness it on one habitat instance, and
  the uniform certificate (a canonical symmetric witness seed per chain habitat, or an
  algebraic identity from KT eq. (6.44)) is the genuinely new mathematics — first
  W5 *research* dispatch once L0–L4 are in tree, numerics-first per instance as
  before.
- **W5-L8** (sub-obligation (ii)): the k = 0 residue (verdict 5; spiked emptiness
  route recommended). Motive-independent; buildable in parallel with L6.

Attack order: L0 → L1 → L2 → L3 → L4 (the device spine), then L5; L6/L8 are
parallel combinatorial tracks after L0; L7 last (consumes L2–L4, L6).

### Open after this pass (owner)

- L7's uniform escape certificate — the research core (W5 dispatch, numerics-first).
- Whether the split arm needs further minimality-free analogues of KT Lemma 4.3
  beyond Claim 6.11's inputs — assess inside the arm build (builder).
- W4's constrained-substrata chart (graded extension, N6 blueprint) and witness
  generality — unchanged from §W4 route, consumes the W5 device (W4 recon).
- **Contract-arm feasibility propagation** (coordinator addendum on acceptance,
  2026-07-24): the contract arm consumes the IH's generic half at the contracted
  graph `G/E(H)`, so it must either derive `PencilNondegFeasible (G.rigidContract
  H r)` from its own hypotheses or route through the bare half where the conjunct
  is vacuous (contraction can create hub-parallel classes, which ~~kill hub-LI~~
  **do NOT kill hub-LI — corrected 2026-07-24, W5-L5 finding: parallel classes
  (hub or not) are nondegeneracy-feasible; the "vacuous via infeasibility" route
  is unavailable here too, same as the base arm's own open blocker** — the
  mirror of the landed program's nonsimple flows around its
  `Simple`-conditioned half). L6 covers the *split* arm's `G′` only. This
  question is part of the W4 recon's charter (W4 recon), and now shares the
  base arm's open blocker (`notes/Phase39.md` *Blockers*) rather than a
  separate vacuity route. **Update (2026-07-24 L5 blocker recon):** under the
  recommended (b′) repair (§"W5 leaf decomposition" L5's blocker verdict,
  pending user adjudication) the vacuity route RETURNS — a contraction-created
  parallel class makes `G/E(H)` non-simple, so the Simple-conditioned generic
  IH obligation is vacuous there.

### Numerics index (this pass)

| # | experiment | result |
|---|---|---|
| N4 | theta(2,2,2), interiors collinear on the hub-planes' meet line, hubs generic (5 samples + 2 generic + 2 coplanar controls) | 24 = target in all (controls 24) |
| N5 | K3,3, sides on two lines (5 samples + controls) | 30 = target in all (one coplanar control hit a deeper degeneration, 29 — not load-bearing) |
| N6 | spider-K4 coincidence branch (`u,a,b,c` coplanar; 6 samples + 2 generic) | 54 = target in all |

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

Pointers re-read and verified by the 2026-07-24 W3–W5 route recon
against the same `.refs` copy: p. 670 (the Theorem-5.6 strip-extend
proof — rank transfer by motion monotonicity alone), pp. 674–675
(Lemma 6.3 eq. (6.6) fresh connecting hinges; Claim 6.4's specialization
`Π₁(v) := Π₂(v*)` + algebraic-independence argument), p. 684 (Claim
6.11, Lemma 4.3(ii) input `|B′ ∩ ãb| < 5`), pp. 690–691 (the `M₁/M₂/M₃`
candidates eq. (6.42), Claim 6.12, eq. (6.44), the four-point span
proof). The W5 design pass re-verified p. 684 and additionally records
that Claim 6.11's proof consumes minimality a second time ("Gᵥ is
minimal by Lemma 3.3", feeding eq. (6.22)) — the §W5 verdict-5 finding.

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
