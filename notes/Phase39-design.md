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

*(2026-07-30: this remainder is now decomposed — dispatch skeleton, carried kernels
(K-c)/(K-bare-c), and the vertex-removal branch — in §"W4 decomposition recon" below;
remainder (iii) is settled there by the landed `PencilPair`.)*

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
4. **Split-arm use-sites (W5-L6).** ⚠️ **Verdict SUPERSEDED (2026-07-29,
   L6a proof-route recon) — canonical resolution now in §"W5 leaf
   decomposition" L6a "Re-route SETTLED".** In brief: the "2EC + no proper
   rigid subgraph ⟹ every closed hub-neighbourhood ≤ 3" lemma this verdict
   proposed is FALSE (computer-verified theta counterexample), but it was the
   **wrong target** — the ≤ 3 bound on `G` is free from the split arm's own
   `PencilNondegFeasible K G` antecedent (landed
   `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), and where it
   fails `G` is infeasible so the obligation is vacuous. The REAL content is
   the transfer `G ⇒ G′`, which fails at "dangerous" split vertices (a
   computer-verified feasible/2EC/no-rigid gadget where `splitOff` makes a
   4-member neighbourhood, so `G′` is infeasible); the fix is to split a
   **safe** vertex, with two coupled open items flagged there.
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
    - *Leaf decomposition (build order; v-d is the next commit).*
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
      move was available. **v-b LANDED (2026-07-25)**: witness (i),
      `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3` (new file
      `Molecule/Pencil/Witness.lean` — `Engine.lean` was at the LoC cap; imports `Pencil.Engine`,
      aggregator wired) — full landing record in the "v-b construction recipe" sub-bullet below.
      **v-c LANDED (2026-07-25)**: witness (ii),
      `exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3` (`Witness.lean`, same
      toolkit on `H := G.induce V₁`'s chart). Refinement vs the pinned shape: carries the pendant
      config `hVG : V(G) = V₁ ∪ {v_c}` (in scope at the v-g discharge, matching sub-case-3's
      producer), so `v_c` is a degree-`1` non-hub never in a family — exactly the composition
      finding's implicit assumption ("promoted families are `fillNbr`-free" holds only there; a
      hub `v_c` would need the `fillNbr`/`nbrSel` layer this refinement sidesteps). The family sets
      are `G.closedHubNbhd v` (stronger than `H`'s; consumer restricts by `LinearIndepOn.mono`);
      the demoted `u_c`'s forced `cross₃`-of-points normal is steered to `±e_0` via
      `exists_smul_cross₃_eq_of_linearIndependent` (`nbrSel u_c` fully assigned,
      `H.closedNbhd u_c = {u_c, w₁, w₂}`). Two reusable engines added to `Witness.lean`:
      `linearIndepOn_smul_pi_single` / `linearIndependent_smul_pi_single_of_injective` (a
      nonzero-scaled family of distinct standard basis vectors is independent).
      `exists_fin3_rank_injOn` (`Engine.lean`) still unconsumed after v-b/v-c — retirement deferred
      to v-d. **v-d COMPLETE (2026-07-29)**: gadget (2026-07-25) + WF-flattening bridge + `fillNbr`
      re-choice, and `exists_fin3_rank_injOn` **RETIRED** (see the v-d completion sub-bullet at the
      end of this leaf list). The "LI `≤3`-family of
      polynomial vectors at a witness ⟹ one somewhere-nonzero polynomial whose non-roots keep it LI"
      extraction gadget is `exists_polynomial_ne_zero_of_linearIndependent_pencilChart{Point,Normal}`
      (`Engine.lean`) — thin `[Field K]`-only specializations of the maximal-minor engine
      `exists_polynomial_ne_zero_of_linearIndependent_at_reindex` (`φ := LinearEquiv.refl`,
      `e := finCongr (Module.finrank_fin_fun K)`; NB the gadget itself needs NO `[Infinite K]` — the
      engine exposes the witnessing minor rather than picking a point, so infiniteness enters only
      when `exists_common_seed_pencilRow_and_polynomials` extracts the common seed downstream). The
      "`cross₃Poly` cases" is the new normal mirror `pencilChartNormalPoly` (+ `nbrSlotPointPoly`) and
      its eval identity, companions of the existing `pencilChartPointPoly`. **v-d completion
      (2026-07-29, new file `Molecule/Pencil/Steer.lean`):** (a) the WF-flattening bridge —
      `PencilSeed.toCoord` + coincidence lemmas + `pencilChartWF_standing_ofCoord_toCoord` (the four
      `fillNbr`-free conjuncts); (b) the post-steering `fillNbr` re-choice
      `exists_fillNbr_pencilChartWF_of_standing` — the four standing conjuncts + each non-hub body's
      `some`-slot `nbrSlotPoint` LI (`hnbr_some`; at a fully-assigned body = conjunct 4, from steering;
      at deg-`≤ 1` = the adjacent-point subfamily, from conjunct 3/5) ⟹ full `PencilChartWF` by a
      `fillNbr`-only re-choice, via the general `exists_extend_linearIndependent` (fill an LI partial
      family's free slots to a full LI family in dim `≥ n`; upstream-eligible, FRICTION
      `[mirror-candidate]`); (c) **`exists_fin3_rank_injOn` RETIRED** — the re-choice takes the
      extend-and-fill route not the pigeonhole, so it stayed unconsumed through all of v-a…v-d;
      tree-wide deletion-hygiene sweep done (decl + orphaned section header retitled to the arity-`2/1/0`
      perp-sweeps it fronted, `Witness.lean` docstring ref repointed to "a pigeonhole fact"). **v-e
      COMPLETE (2026-07-29, `Steer.lean`, imports `Pencil.{Reseed,Witness}`)**: the input-half assembly
      `pencilNondegFeasible_induce_of_pendant_deg3` (`PencilNondegFeasible K G → PencilNondegFeasible K
      (G.induce V₁)` under the pendant deg-`3` config + `hVG`, over `[Infinite K]`). Two landings —
      first the "steer to a common seed" primitive `exists_common_seed_linearIndepOn_pencilChartPoint`
      (finitely many `pencilChartPoint`-LI conditions each satisfiable somewhere share one common seed;
      v-d point gadget `ends := id` + `exists_common_eval_ne_zero_of_forall_exists`, whence
      `[Infinite K]`), then the assembly itself. The key simplification the primitive encodes: every
      steered condition — conjunct 3 (`pencilChartPoint v ≠ 0`), conjunct 5 (adjacent pairs),
      `hnbr_some` (assigned neighbour points), and the demoted triple — is a `pencilChartPoint`-LI
      condition on a subset of `α`, so **one** engine call carries them all (index `α ⊕ (α×α) ⊕ Unit`);
      no `hubSlotNormal`/normal steering gadget is needed for the input half. Assembly: re-seed
      (`exists_pencilSeed_of_nondeg`) → marshal (standing conditions satisfiable at the flattening
      `seed₀.toCoord` via `pencilChartWF_standing_ofCoord_toCoord`; triple at witness (i)'s seed) →
      `exists_fillNbr_pencilChartWF_of_standing` → full `PencilChartWF` →
      `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF` → `.mono` to `H := G.induce V₁`
      (`u_c` the only demotion, `degree_induce_eq_of_ne`; `H.closedNbhd u_c = {u_c,w₁,w₂}` the
      `hdemote` residual, the surviving demoted triple). Three local helpers: `pencilChartPoint_congr`,
      `linearIndepOn_triple_of_linearIndependent` (reverse `Fin 3` set↔indexed),
      `linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint` (the `hnbr_some` reindexing; TACTICS-QUIRKS
      § 102 for the `choose`-tactic idiom). **v-f (next; RECONNED + compiler-spiked 2026-07-29 — full
      decomposition, exact signatures, and the sorry-free rank-transport spike in the dedicated "v-f
      decomposition" sub-bullet below)**: the output-half rank-transport, a faithful pencil-mirror of the
      landed panel lemma `finrank_span_rigidityRows_ofNormals_of_isGenericNormals`; six S=1 leaves,
      **GO — no obstruction, finding (4) composes exactly as pinned**. **v-g PART 1 LANDED
      (2026-07-29, `Pair2.lean`, `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_deg3`)**:
      the glue (sub-case-3-shaped; conjunct 3 at `u_c`/`w₁`/`w₂` from the steered promoted families
      `hpromoted`, elsewhere the `G`/`H` closed-hub-nbhd equality, `hlb₂ = 0` rank verbatim) — the
      demoted-`u_c` fresh-data composition against the promoted families verified green, `[Field K]`-only.
      **v-g PART 2 (next)**: the shell/successor rewire (discharge `hcutPendant3`, add `[Infinite K]`,
      import Steer) + the blueprint restatement (`notes/Phase39.md` *Hand-off* has the step-by-step).

    **v-f decomposition (reconned + compiler-spiked 2026-07-29; the output-half rank-transport).**
    The route is a faithful pencil-mirror of the landed panel lemma
    `finrank_span_rigidityRows_ofNormals_of_isGenericNormals` (`GenericLift/PanelGeneric.lean`):
    lower bound = an LI row subfamily of the target count transferred to the chart, upper bound = the
    landed deterministic B2 bound `finrank_span_rigidityRows_add_deficiency_le`, pinched by
    `le_antisymm`. The panel proof's genericity-over-`q` step is replaced by explicit steering (the
    landed product-route `exists_common_seed_pencilRow_and_polynomials`). **Load-bearing finding: the
    general `BodyHingeFramework` panel-row machinery is REUSABLE on the chart verbatim** — `panelRow`,
    `panelRow_mem_rigidityRows_of_link`, `span_panelRow_eq_rigidityRows`, and
    `exists_independent_panelRow_subfamily_of_le_finrank` (`Pinning.lean`/`GenericityDevice.lean`) are
    framework-agnostic, and the Pencil import cone already reaches them (Statement → Theorem55 →
    Pinning/GenericityDevice), so **no new import** and **no re-proof** of the extraction/B2 layer is
    owed. The genuinely-new work is confined to the graph-bridge (v-f-1) and the re-seeding transfer
    (v-f-3); everything else re-wires landed pieces.

    *Compiler-checked spike (scratchpad only, deleted — not committed).* Three theorems built
    **sorry-free and axiom-clean** (`propext`/`Classical.choice`/`Quot.sound` only, checked by
    `#print axioms`) against the landed olean tree: the bridge (v-f-1), the row-span scaling
    invariance (v-f-2), and the **full `le_antisymm` composition** (v-f-4). The composition carries no
    hidden residual: `spike_output_rank`'s ONLY sorry-analogues are its named hypotheses — the LI
    `pencilRow` subfamily of size `target_H` at the steered seed (`hslink`/`hsLI`/`hscard`) and the
    nonzero hinges (`hne`) — both produced downstream by v-f-3/v-f-6 from landed bricks. **VERDICT:
    GO — composition finding (4) composes exactly as pinned; the residual is the two named leaf
    inputs, no motive/IH change, no orphaned hypothesis.**

    *Leaves (build order; each S=1 given the exact signatures below).*
    - **v-f-1 — the link bridge (the Engine docstring's deferred "hends-style" consumer).** On a
      genuine edge, `pencilRow hubSel G.endsOf q` IS the chart framework's own `panelRow`, hence a
      rigidity row — the whole "graph bridge" is `rw [pencilRow, panelRow,
      pencilChartFramework_supportExtensor_of_mem_edgeSet]` then the landed general
      `panelRow_mem_rigidityRows_of_link`. Spike-proved (`[Inhabited α]`; `i : β ×
      Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2`, `he : i.1 ∈ E(G)`):
      `pencilRow hubSel G.endsOf q i = (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).panelRow
      G.endsOf i` (helper) and `… ∈ (pencilChartFramework (PencilSeed.ofCoord q) hubSel G).rigidityRows`.
    - **v-f-2 — row-span invariance under per-edge nonzero extensor scaling.** Two frameworks on the
      same graph with per-edge proportional (nonzero-scalar) support extensors on links have equal
      rigidity-row spans (via `Submodule.span_singleton_smul_eq`). Spike-proved:
      `(F₁ F₂ : BodyHingeFramework K k α β) (hg : F₁.graph = F₂.graph) (hprop : ∀ e u v,
      F₁.graph.IsLink e u v → ∃ c ≠ 0, c • F₁.supportExtensor e = F₂.supportExtensor e) : span K
      F₁.rigidityRows = span K F₂.rigidityRows`.
    - **v-f-3 — the re-seeded chart hinge is proportional to the witness hinge** (produces v-f-2's
      `hprop`). For a re-seed `seed₁` of an `IsNondegPencilRealization H F₁ normal₁ point₁`
      (`exists_pencilSeed_of_nondeg`: `pencilChartPoint seed₁ w = c_w • point₁ w`), each link's chart
      hinge is a nonzero multiple of `F₁`'s: the landed
      `exists_smul_eq_extensor_of_extensorThroughPoint_pair` forces `F₁.supportExtensor e` onto
      `extensor ![point₁ u, point₁ v]`, and extensor bilinearity turns the reproduction scalars into
      the proportionality. `v-f-2 ∘ v-f-3` + `hrank₁` give `finrank(span (chart seed₁).rigidityRows)
      = target_H` (the only genuinely-new arithmetic; ≈30 lines, mirrors the panel `hrank0` step).
    - **v-f-4 — the output rank conclusion (the `le_antisymm`).** From an LI `pencilRow` subfamily of
      size `target_H` at the steered seed + nonzero hinges, `finrank(span (chart (ofCoord q)
      hubSel H).rigidityRows) = target_H`. Spike-proved (lower bound via v-f-1 + `finrank_span_eq_card`
      + `Submodule.finrank_mono`; upper bound `finrank_span_rigidityRows_add_deficiency_le`). Its
      hypotheses ARE the spike's exact residual goals.
    - **v-f-5 — clean mirror (low-risk): `exists_common_seed_linearIndepOn_pencilChartNormal`** — the
      `pencilChartNormal` twin of the landed `exists_common_seed_linearIndepOn_pencilChartPoint`
      (`Steer.lean`), via the landed normal gadget
      `exists_polynomial_ne_zero_of_linearIndependent_pencilChartNormal`. Convenience for marshalling
      the promoted-family conditions; the assembly may instead fold them straight into
      `exists_common_seed_pencilRow_and_polynomials`'s `P` via the gadget, so this leaf is optional /
      not strictly on the critical path.
    - **v-f-6 — the output-half assembly (capstone). LANDED 2026-07-29** (`Steer.lean`,
      `exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3`). Structurally mirrors
      the landed v-e assembly `pencilNondegFeasible_induce_of_pendant_deg3` at `H := G.induce V₁`,
      ADDING: the rank rows steered alongside (one `exists_common_seed_pencilRow_and_polynomials` call
      — `hLI` = the v-f-1/v-f-3/extraction `pencilRow` subfamily at the flattening
      `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`, `P` = the standing point +
      promoted normal conditions over the index `(α ⊕ (α×α)) ⊕ Fin 3`, each a "nonzero somewhere"
      polynomial via the point/normal gadgets) and the rank conclusion (v-f-4). The "satisfiable
      somewhere" certificates were landed: witness (i) (v-b) — not needed here, the demoted triple is
      a v-e concern — and the promoted-family witness (ii) (v-c). The point-preserving `fillNbr`
      re-choice keeps the rank via `pencilChartFramework_congr` (framework reads points only). Output:
      a steered `IsNondegPencilRealization H` with `finrank = target_H` AND `LinearIndepOn K normal
      (G.closedHubNbhd v)` for `v ∈ {u_c, w₁, w₂}` — the sub-case-3 producer's input shape plus the
      promoted families v-g's glue consumes. Landed in one commit; the `hassigned` discharge used an
      inline `Fin 3`-selector-total pigeonhole at `u_c`.
    - **v-f-5 — DROPPED (not built).** The assembly folds the promoted-normal conditions straight into
      `exists_common_seed_pencilRow_and_polynomials`'s `P` via the normal gadget, so the standalone
      `exists_common_seed_linearIndepOn_pencilChartNormal` mirror was never needed — off the critical
      path as the entry above already flagged. Revive only if a later consumer wants it.

    **v-f COMPLETE (2026-07-29):** all six leaves landed (v-f-5 dropped). Next is v-g, the sub-case-4
    glue + shell/successor rewire — see `notes/Phase39.md` *Hand-off*.

    **v-b construction recipe (derived 2026-07-25; the witness LANDED same day — see "the main
    assembly, landed" below).** Re-deriving witness (i) against the CURRENT `Chart.lean`/
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

    **Correction found assembling the main witness (2026-07-25): the "first slice" recipe above
    has a real gap, now fixed.** A single global `fillHub := e₃` fails whenever a body needs
    **two** padding slots at once (`u_c`, `w₁`, `w₂` can each have as few as ONE real member —
    just themselves, or just the always-present `u_c` — leaving two `none` slots): reading the
    *same* constant at two different slots makes two of `cross₃`'s three arguments literally
    equal, forcing it to `0` outright (a repeated determinant row, in **any** field — not a
    sign/order cosmetic issue). Worse, no fixed *function of the slot index alone* can dodge this
    for every possible placement of the (unknown-in-advance) real member among the three slots —
    a direct pigeonhole check (confirmed by exhaustion before landing the fix): with only two
    "safe" values available (avoiding `0` and the target index) and three slots, some placement
    of the real member forces the fix to double up on the other two. **The fix, landed this
    session** (`Engine.lean`, right after `exists_smul_cross₃_pi_single`):
    `exists_fin3_rank_injOn` — the "rank among earlier `none`-marked slots" function is injective
    on the marked slots, so assigning the *first* marked slot one fill vector and any *second*
    marked slot another never collides, however `hubSel` places the real member. (Historical: this
    helper was RETIRED at v-d, unconsumed — the v-b assembly below took the injective-extension route
    instead; the name no longer exists in the tree.)

    **The main assembly, LANDED (2026-07-25):**
    `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`, new file
    `Molecule/Pencil/Witness.lean` (imports `Pencil.Engine`; `Engine.lean` was one assembly away
    from the ~1500-LoC cap). Statement = the pinned witness (i) exactly (the `∃ q :
    α × Fin 4 × Fin 4 → K` shape, `[Finite α] [Finite β]`, any field). The landed construction
    **supersedes the `fin_cases`-per-vertex skeleton** (and, before it, the flat `index`
    formula): instead of per-vertex slot pinning inside a 7-way hub-status split, ONE abstract
    padding lemma `exists_injective_extension_of_isFin3SelectorOf` does the single `some`/`none`
    shape split (8 cases, `Fin 4` pick facts by a `4 > 3` counting argument) — given any
    `IsFin3SelectorOf` whose selected members carry distinct basis indices avoiding a target
    `d` (`InjOn` + `≠ d` on the neighbourhood), it produces an *injective* `σ : Fin 3 → Fin 4`
    avoiding `d` and matching the selector, so every body's slot triple becomes three distinct
    `Pi.single`s and `exists_smul_cross₃_pi_single` closes ALL arities uniformly (no separate
    arity-`1`/`2` orthogonality argument, no `exists_fin3_rank_injOn` consumption — that helper
    stayed unconsumed through v-a…v-d and was RETIRED at v-d). The 7-way
    hub-status split dissolves into the three per-body `InjOn`/`≠ d` proofs, fed by exactly the
    recipe's facts: `Graph.neighbor_eq_of_degree_eq_three` (u_c's neighbours exhausted), the
    `ncard ≤ 3` bound (not-all-three-hubs + at-most-one-third-party at a hub `w₁`/`w₂`), the
    `degree ≤ 2` bound (at-most-one-third-party at a non-hub `w₁`/`w₂`), v-a's triangle
    exclusion (`w₁ ~ w₂` barred when either is a hub — note: *either*, sharper than the
    recipe's "both", since `u_c` is always the second adjacent hub), and the `≤ 1`-cut
    non-adjacency of `v_c`. Global index map exactly as the recipe: `u_c ↦ e₀, w₁ ↦ e₁,
    w₂ ↦ e₂`, hub-`v_c ↦` the unclaimed one of `e₁`/`e₂`, third parties `↦ e₃`; targets
    `±e₃/±e₂/±e₁`, LI via `linearIndependent_pi_single_triple` + `units_smul`. Build frictions:
    the `∀∃`-quantified `decide` pick facts hit the whnf heartbeat budget (new
    TACTICS-QUIRKS § 101), `Pi.single`/`Fin.cases` needed the § 49-style ascriptions.
    Gates green (build warning-clean + lint); axioms clean. **Next: v-c** (witness (ii), the
    same toolkit on `H := G.induce V₁`'s chart — the extension lemma is body-agnostic and
    should be reused as-is).

- **W5-L6 — habitat feasibility for the split arm's `G′ = G.splitOff v a b e₀`** (`= G^{ab}_v`,
  `Induction/Operations.lean:724`; verdict 4 + the L5 (b′) restatement). **Decomposed 2026-07-29 by
  the L6 design-pass recon**, grounding every signature against the LANDED motive/chart bodies
  (`Pencil/{Motive,Chart}.lean`), NOT the stale 2026-07-24 "Pinned Lean shapes" block (which predates
  the (b′) `Simple`-conditioning and the L4 fourth conjunct).

  **Consumer confirmed (the wrong-level check).** The split arm's generic conjunct is
  `G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K 3 G`; it fires the IH
  `PencilPair K 3 G′`'s generic half `G′.Simple → PencilNondegFeasible K G′ →
  HasGenericPencilRealization K 3 G′` (landed `PencilPair`, `Motive.lean:160`), which consumes
  **exactly `G′.Simple` + `PencilNondegFeasible K G′` and nothing stronger** (checked against the
  landed `PencilNondegFeasible`/`HasGenericPencilRealization` bodies, `Motive.lean:133`/`140`). The
  IH's *output* `HasGenericPencilRealization K 3 G′` is L7's input. **So L6 does NOT feed `hsplit`
  directly — it feeds the L7 split-arm assembly, which discharges `hsplit`.** `G`'s own
  `PencilNondegFeasible K G` antecedent is NOT used by L6: `G′` adds the shortcut edge `ab`, whose
  cross-incidences (`point a ⬝ᵥ normal b = 0`, …) are unforced when `a, b` are non-adjacent in `G`,
  so restricting `G`'s realization does not produce one for `G′` — the fresh witness seed is the
  design's pinned route, and this is why.

  Three sub-leaves, ordered:

  - **L6a — the ≤ 3 combinatorial lemma** (target: new `Molecule/Pencil/Habitat.lean`, imports
    `Pencil.Motive` + `Induction.Operations`; `Motive.lean` is near the ~1500-LoC tripwire, and the
    lemma bridges `closedHubNbhd` to `IsProperRigidSubgraph`. Purely combinatorial, no chart.) Target
    signature:
    ```lean
    theorem ncard_closedHubNbhd_le_three_of_twoEdgeConnected_of_noRigid
        [DecidableEq β] [Finite α] [Finite β] {n : ℕ} {G : Graph α β}
        (hD : 4 ≤ Graph.bodyBarDim n) (hloop : G.Loopless) (h2ec : G.TwoEdgeConnected)
        (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) (v : α) :
        (G.closedHubNbhd v).ncard ≤ 3
    ```
    Structure: `v` non-hub ⟹ `≤ 2` (degree `≤ 2` ⟹ `≤ 2` hub-neighbours, and `v ∉ closedHubNbhd v`);
    `v` a hub with `≥ 3` hub-neighbours (the `≥ 4`-member case) ⟹ exhibit a proper rigid subgraph,
    contradicting `hnoRigid`. Grep confirms **no existing partial**: the landed
    `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) derives `≤ 3`
    *from* a realization — circular here, since L6b is *building* the realization.
    **REFUTED (2026-07-29, L6a build → computer-verified counterexample, coordinator-reproduced; NOT
    the pinned lemma).** The bare-hypothesis lemma above is **FALSE**. Counterexample (verified over
    all `2^19` vertex subsets): the theta graph at `n = 3` (`D = bodyBarDim 3 = 6`) — central hub `v`
    with spokes to `a, b, c`, where `a, b, c` lie on an 18-cycle of three **6-edge** arcs (`19`
    vertices, `21` edges). It is loopless, simple, `TwoEdgeConnected` (min edge-cut `= 2`), and has
    **no proper rigid subgraph**: writing `f(W) := 5·|E_G(W)| − 6·(|W|−1)` (= `−partitionDef` at the
    finest partition), a rigid subgraph forces `f ≥ 0`, and here `max` over proper `|W| ≥ 2` is
    `−1 < 0` — so no proper rigid subgraph (robust to the spanning reading, since `f(V) = −3`). Yet
    `deg v = deg a = deg b = deg c = 3`, so all four are `PencilHub`s and
    `(G.closedHubNbhd v).ncard = 4 > 3`, contradicting the conclusion while every hypothesis holds.
    **Root cause of verdict 4's error:** it sampled only SHORT chains (spider-K4, 3-chain-4), which
    stay dense; **each edge subdivision changes `f` by `−1`**, so lengthening the arcs drives every
    proper subset strictly sparse while preserving the four degree-3 hubs and 2EC. The sharp
    transition at `D = 6`: arcs `(4,4,4) → f_max = 1`, `(5,5,5) → 0` (borderline tight), `(6,6,6) →
    −1` (clean). The builder reproduced verdict 4's own hand numbers as a cross-check (spider-K4
    `f = 3`, chain-4 `f = 1`). Note the counterexample is itself strictly SPARSE (`f(V) = −3`, not
    rigid) — the true split-arm habitat likely carries a rigidity/tightness invariant (`f(V) ≥ 0`)
    the bare hypotheses omit.
    **Re-route SETTLED (2026-07-29, L6a proof-route recon).** The refuted lemma was proving the
    *wrong statement*. The ≤ 3 bound on `G` is **not a graph-combinatorial fact** (candidates (a)/(b)/(c)
    below all miss the point); it is **free from the split arm's own `PencilNondegFeasible K G`
    antecedent**. `PencilPair`'s generic half is `G.Simple → PencilNondegFeasible K G →
    HasGenericPencilRealization K 3 G` (`Motive.lean:160`), so when the split arm proves that half it
    **has `PencilNondegFeasible K G` in scope**, and the LANDED
    `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) turns it into
    `∀ v ∈ V(G), (G.closedHubNbhd v).ncard ≤ 3` with **zero new work**. On graphs where that bound
    *fails* (the theta counterexample: `closedHubNbhd v = 4`), the contrapositive of the *same* landed
    lemma makes `G` **infeasible** (`¬ PencilNondegFeasible K G`), so the split arm's generic obligation
    is **vacuous** — the refuted L6a was never needed there. No combinatorial ≤ 3 lemma on `G` exists.

    **(5,5,5) borderline RESOLVED (moot).** The worry — does a rigidity/tightness hypothesis rescue a
    combinatorial ≤ 3 lemma, since `(5,5,5)` is tight (`f(V) = 0`) with a proper tight subset — dissolves:
    `theta(5,5,5)` has `closedHubNbhd(center) = 4` *regardless of arc length*, hence is infeasible, hence
    vacuous. Arc length flips **no-proper-rigid**, never `closedHubNbhd ≤ 3`, and `> 3 ⟹` infeasible `⟹`
    vacuous. Candidate (a) [strengthen L6a with rigidity/circuit], (b) [3-edge-conn], (c) [max-degree]
    are all solving a non-problem; **none is pursued.**

    **The real gap is the transfer `G ⇒ G′`, and it CAN fail.** L6b needs `hcard` at **`G′`**, not `G`.
    Under `G.Simple` (split-arm antecedent) the fresh edge `ab` and the deletion of the degree-2 `v`
    **preserve every degree** except `v`'s, so `PencilHub` is unchanged off `v` and
    `(G′.closedHubNbhd w) = (G.closedHubNbhd w)` for `w ∉ {a, b}`, while
    `G′.closedHubNbhd a = G.closedHubNbhd a ∪ ({b} if G.PencilHub b)` (symmetric at `b`; `v ∉` either,
    being a non-hub, and `a`–`b` non-adjacent in `G` by `triangle_isProperRigidSubgraph`/`hnoRigid`).
    So the transfer **creates a 4-member neighbourhood at `a`** exactly when `a` is a hub with
    `|G.closedHubNbhd a| = 3` (tight) and `b` is a hub — a **dangerous** split. Then `G′` is **infeasible**
    (landed necessity), the IH's generic half is vacuous, and *there is no `G′`-realization to extend* —
    the "build a fresh feasible `G′`" route dies at that `v`.

    **Computer-verified gadget (this recon, `scratchpad/habitat.py` — session-local, not
    preserved; results recorded here).** The path `a–v–b` with `a` joined to
    two hubs `x, y`, and `x, y, b` on a subdivided-triangle cycle of three length-`L` arcs (`L = 5`: 17
    vertices; `L = 6`: 20), is loopless, simple, **2EC**, **no-proper-rigid** (certified: `f(W) < 0` for
    *every* proper `W`, worst `−1` at `{a, v}`; `f(W) := 5|E_G(W)| − 6(|W|−1) = −partitionDef` at the
    finest partition, so `f(W) < 0 ⟹ deficiency(G[W]) > 0 ⟹ G[W]` not rigid — airtight), and **feasible**
    (`closedHubNbhd ≤ 3` everywhere, `= 3` at `a`). Yet `splitOff v a b` gives
    `closedHubNbhd_{G′}(a) = {a, x, y, b}`, `= 4`, so **`G′` is infeasible**. Splitting any *arc-interior*
    degree-2 vertex instead keeps `≤ 3` (**safe**). So the bound does NOT transfer for an arbitrary split
    vertex.

    **The route survives iff the split arm splits a SAFE degree-2 vertex.** Call a degree-2 `v` with
    neighbours `a, b` **safe** when `¬ G.PencilHub a ∨ ¬ G.PencilHub b` (at least one neighbour a
    non-hub); equivalently, under 2EC (no degree `≤ 1`), `v` is adjacent to another degree-2 vertex.
    Dangerous ⟺ both neighbours hubs with one tight. The refuted L6a is therefore replaced by **two**
    pieces:

    - **L6a-transfer (LANDED 2026-07-30, purely combinatorial, `Molecule/Pencil/Habitat.lean`):** the
      `closedHubNbhd` transfer at a safe split vertex — the honest producer of L6b's `hcard` at `G′`.
      Landed signature:
      ```lean
      theorem ncard_closedHubNbhd_splitOff_le_three_of_safe
          [Finite α] [Finite β] {G : Graph α β} [G.Simple] {v a b : α} {e₀ : β}
          (hab : a ≠ b)
          (heₐ : ∃ eₐ, G.IsLink eₐ v a) (e_b : ∃ e_b, G.IsLink e_b v b)
          (hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b)
          (hcard : ∀ w, (G.closedHubNbhd w).ncard ≤ 3) :
          ∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3
      ```
      **The first pin (bare existentials + `G.degree v = 2`, no `hab`) was FALSE** (coordinator-verified,
      dispatch F9): the two existentials do not force `a ≠ b` (a degree-`2` `v` may have a third
      neighbour, so both are witnessable by the single `v`–`a` edge), and at `a = b` the fresh `e₀` is a
      **self-loop** at `a` whose double-counted degree (Matroid `incFun_eq_two_iff`) can turn a non-hub
      `a` into a `G′`-hub, inflating a *neighbour's* closed hub-neighbourhood to `4` (explicit
      `10`-vertex counterexample `v,a,c,w,h₁,h₂,p₁,p₂,q₁,q₂`, edges `va,vc,aw,wh₁,wh₂,h₁p₁,h₁p₂,h₂q₁,h₂q₂`:
      every hypothesis holds yet `(G′.closedHubNbhd w).ncard = 4`). Fix = the explicit `hab : a ≠ b`,
      **free at the L7 call site** (`exists_splitOff_data_of_degree_eq_two`'s `eₐ ≠ e_b` + `G.Simple`);
      `{n}` and `hdeg` are dropped (`n` was never used, and `hdeg` is unused for the bound under the
      route below). Output `∀ w, (G′.closedHubNbhd w).ncard ≤ 3` still type-matches L6b's `hcard` exactly.
      Route (landed): `hab` ⟹ `G′` loopless ⟹ `G′.degree x ≤ G.degree x` for **every** `x`
      (`E(G′, x) ⊆ insert e₀ (E(G, x) \ {edge to v})`, the `-1`/`+1` cancel — needs neither `e₀ ∉ E(G)`
      nor `ab ∉ E(G)`) ⟹ every `G′`-hub is a `G`-hub; then per `w`: non-hub `w` via
      `ncard_closedNbhd_le_three_of_not_pencilHub`; hub `w` has `G′.closedHubNbhd w ⊆ G.closedHubNbhd w`
      (`splitOff`'s only new adjacency is `ab`, and a hub `w=a` with hub partner `b` contradicts `hsafe`),
      closed by `hcard w`.
    - **L6a-safe-exists (SPLIT BY DEFICIENCY 2026-07-30 recon; BOTH HALVES NOW PROVEN
      minimality-free — non-rigid half same-day recon, rigid half same-day route recon +
      build).** The obligation: under the split-arm
      hypotheses, a **coordinator-safe** degree-2 vertex exists (a degree-2 `v` with a non-hub
      neighbour). Under 2EC (`¬ PencilHub w ⟺ deg w = 2`, from `PencilHub := _ ∧ 3 ≤ degree`,
      `Motive.lean:73`) this is **exactly an adjacent degree-2 pair**, i.e. the LANDED
      `exists_adjacent_degree_two_pair` (`ReducibleVertex.lean:893`, KT Lemma 4.6 at `d = 3`)
      **generalized off `IsMinimalKDof n 0`**. Grounding the landed proof: minimality is consumed
      **only** through the KT-4.5(i) edge bound `no_rigid_edge_count` (`ReducibleVertex.lean:330`); the
      degree double-count (its "bound 1" `2|X₂|+3|X₃₊| ≤ Σdeg` and "bound 2" `Σ_{X₂}deg ≤ Σ_{X₃₊}deg`,
      giving `5|E| ≥ 6|V|` under no-adjacent-pair + 2EC) uses **no** minimality. **So the whole
      obligation reduces to one edge bound off minimality:**
      `(D−1)|E| < D(|V|−1) + (D−1)` (⟺ `5|E| < 6|V|−1` at `D = 6`; ⟺ corank `≤ D−2`), which the
      landed nlinarith contradicts against `5|E| ≥ 6|V|`.

      Re-pin as a mechanical refactor of the landed lemma + a per-deficiency edge-bound discharger.
      **NON-RIGID HALF LANDED 2026-07-30** (both bricks + the composition, `ReducibleVertex.lean` /
      `Operations.lean`; gates + axioms clean). Landed signatures (the pinned `[DecidableEq β]` and
      `hnp` on (i) were DROPPED as **provably inert** — off minimality the only rigidity uses were the
      removed `no_rigid_edge_count`/`two_le_crossingEdges_of_isKDof_zero`, and `IsMinimalKDof`'s type was
      what carried `matroidMG`/`DecidableEq β`; `classical` covers decidability, leaving a strictly more
      general statement):
      ```lean
      -- (i) generalized counting: drop IsMinimalKDof, take the edge bound as an explicit hyp.
      -- Mechanical copy of `exists_adjacent_degree_two_pair`'s body: bounds 1/2 verbatim (2EC via
      -- `two_le_degree_of_twoEdgeConnected`, `Deficiency.lean:1244`), final nlinarith on `hedge`.
      theorem exists_adjacent_degree_two_pair_of_edgeBound     -- LANDED (Graph namespace)
          [Finite α] [Finite β] {G : Graph α β} {n : ℕ} [G.Loopless]
          (hD : 6 ≤ bodyBarDim n) (hV : 3 ≤ V(G).ncard) (h2ec : G.TwoEdgeConnected)
          (hedge : (bodyHingeMult n : ℤ) * E(G).ncard
            < bodyBarDim n * ((V(G).ncard : ℤ) - 1) + bodyHingeMult n) :
          ∃ v a : α, v ∈ V(G) ∧ a ∈ V(G) ∧ G.degree v = 2 ∧ G.degree a = 2 ∧ ∃ e, G.IsLink e v a
      -- (iii) composition for the non-rigid habitat (k := deficiency G > 0):
      theorem exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos   -- LANDED (Graph namespace)
          [Finite α] [Finite β] {G : Graph α β} {n : ℕ} [G.Loopless]
          (hD : 6 ≤ bodyBarDim n) (hV : 3 ≤ V(G).ncard) (h2ec : G.TwoEdgeConnected)
          (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) (hk : 0 < G.deficiency n) :
          ∃ v a : α, v ∈ V(G) ∧ a ∈ V(G) ∧ G.degree v = 2 ∧ G.degree a = 2 ∧ ∃ e, G.IsLink e v a
      ```
      **Non-rigid half (k := deficiency G > 0): PROVEN minimality-free.** New brick (LANDED,
      `Operations.lean`, `Graph` namespace):
      ```lean
      theorem indep_matroidMG_of_noRigid_of_deficiency_pos
          [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} [G.Loopless] {n : ℕ}
          (hD : 1 ≤ bodyBarDim n)
          (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) (hk : 0 < G.deficiency n) :
          (G.matroidMG n).Indep E(G.mulTilde n)
      ```
      Proof (3 landed bricks): if `M(G̃)` is not independent, some base `B` misses a fiber `p`; its
      fundamental circuit `X = fundCircuit p B` **spans `V(G)`** (`fundCircuit_inducedSpan_vertexSet_eq`,
      `Operations.lean`, exactly the no-proper-rigid + Loopless hook) and its `inducedSpan` is
      **rigid** (`circuit_induces_isRigidSubgraph`, `Operations.lean`); a spanning rigid subgraph
      forces `deficiency G ≤ deficiency (inducedSpan) = 0` (`deficiency_le_deficiency_of_le_vertexSet_eq`,
      `Deficiency.lean`), contradicting `hk`. In (iii), `E(G̃)` is then the base
      (`ground_indep_iff_isBase`), so `isBase_ncard_add_deficiency_eq` gives `(D−1)|E| + k = D(|V|−1)`,
      whence `hedge` is immediate (`− k < D − 1`). This discharges the entire **non-rigid** split-arm
      habitat with **no minimality anywhere**.
      **Rigid half (k = 0, `G` rigid): PROVEN 2026-07-30 (route recon + build), minimality-free
      — no subdivision/smoothing detour needed.** The "smooth to a min-degree-3 multigraph `H`,
      apply the minimality-free W3-L1 `exists_isProperRigidSubgraph_of_three_le_degree`, lift back"
      route above is a dead end (subdivision does not preserve deficiency, `C6` rigid ↦ `C7` not);
      the route that actually works needs no deficiency case-split and no smoothing at all — it
      argues **directly off the degree-2 vertex** `v` itself, exactly the counting dual of W3-L1:
      let `Ev = E(G) ∖ E(G, v)` (`|Ev| + 2 = |E|` since `deg v = 2`) and `E'` its `(D−1)`-fold
      fiber in `G̃`. `E'` is independent in `M(G̃)`: else a circuit `C ⊆ E'` induces
      (`circuit_induces_isRigidSubgraph`, KT Lemma 3.4) a rigid subgraph spanning `≥ 2` vertices
      (looplessness) that avoids `v` (every `E'`-fiber's edge avoids `v`), hence proper —
      contradicting `hnp`. Independence gives `(D,D)`-sparsity of `E'` on itself
      (`matroidMG_indep_iff`); its vertex span avoids `v` (`≤ |V| − 1`), so `|E'| + D ≤ D(|V|−1)`,
      i.e. `(D−1)(|E|−2) + D ≤ D(|V|−1)`, which rearranges to the strict target (`D−2 < D−1`).
      LANDED as `edgeBound_of_noRigid_of_degree_two` (`ReducibleVertex.lean`), consumed by the
      composition `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two` — the latter
      **covers BOTH deficiency halves** at the split-arm call site (it needs only a degree-2-vertex
      witness, which either deficiency regime's own search already supplies), so the deficiency
      case split at the L7 call site dissolves: one lemma serves both. The exhaustive computational
      evidence gathered this recon (`scratchpad/{kzero,kzero2,petersen,broad}.py` —
      session-local, not preserved; results recorded here — exact-ℚ
      rigidity-matrix rank + exact partition deficiency, *zero* counterexamples across
      `S(Petersen)` and all tested subdivision families) stands as corroboration, not the closing
      argument — the Lean proof above is unconditional.

    **L6b RE-ROUTED (2026-07-30 spike — the `hcard`-only pin is FALSE; see the L6b block below).**
    Its input `hcard` type still matches L6a-transfer's output at `G := G′`, but `hcard` **alone does
    not imply `PencilNondegFeasible`** — L6b needs an extra triangle-exclusion hypothesis, and a NEW
    obligation **L6d** (triangle-exclusion transfer `G ⇒ G′`) was surfaced. **L6c UNCHANGED** (landed
    citation). **L8 UNAFFECTED.**

    **L6d VERIFIED — the transfer HOLDS, and delivers *full* triangle-freeness of `G′` (2026-07-30
    habitat-foundations recon).** Grounded against the LANDED `not_pencilNondegFeasible_of_triangle_
    two_hubs` (`Motive.lean:563`), `triangle_isProperRigidSubgraph` (`Operations.lean:994`),
    `isKDof_zero_of_cycle` (`Deficiency.lean:743`), and `splitOff` (`Operations.lean:769`). See the
    L6d sub-leaf below for the pinned signatures + route; the two verdicts in brief:
    - **Q1 (triangle ⟹ proper rigid at `|V| ≥ 4`): TRUE, already LANDED** as
      `Graph.triangle_isProperRigidSubgraph` (needs only `3 ≤ bodyBarDim n`, `G.Simple`, the three
      triangle links, `a ≠ b`, `4 ≤ V(G).ncard`). Its contrapositive is exactly "no-proper-rigid +
      `|V| ≥ 4` ⟹ `G` triangle-free". No new lemma for the base fact.
    - **Q2 (transfer to `G′`): the naive worry is void.** A *new* `G′`-triangle can only be
      `{a, b, c}` for `c` a common `G`-neighbour of the split endpoints `a, b` (the fresh edge `ab`
      plus two surviving edges); but then `{v, a, b, c}` is an **induced 4-cycle** in `G`
      (`ab ∉ E(G)` by triangle-freeness, `vc ∉ E(G)` since `deg_G v = 2` with `N(v) = {a,b}`), and a
      **`C₄` is `D6`-rigid** (`isKDof_zero_of_cycle` at `m = 4 ≤ bodyBarDim 3 = 6`; independently
      re-checked, exact partition deficiency `= 0`), hence a *proper* rigid subgraph at `|V| ≥ 5` —
      contradicting `hnoRigid`. So **the common neighbour `c` cannot exist**, `G′` gains *no* triangle
      at all, and full triangle-freeness transfers. The "safe" split hypothesis is **not even needed
      for L6d** (only for L6a-transfer's `closedHubNbhd ≤ 3`); `deg_G v = 2` + no-proper-rigid +
      `|V| ≥ 5` suffice. Exhaustive check (all `{2,3}`-degree habitats `n ≤ 7`; sampled `n = 8`):
      **zero** habitats where any degree-2 split creates even one `G′`-triangle. Because the transfer
      yields the FULL triangle-freeness the design originally intended, **L6b is re-pinned with a
      triangle-freeness hypothesis, not merely the minimal `¬(two-hub-triangle)`** — which makes
      L6b-ii's `#3/#4/#5` core strictly easier (its failure locus, the two-hub triangle, is a fortiori
      absent). Dispatch-log F9 instance — a *confirmed* pin this time, first non-refutation of the L6
      arc's habitat claims.

    **⚠ ADJUDICATION POSTURE (revised 2026-07-30 recon — the earlier "two coupled open items" is
    superseded; a W3-level minimality re-introduction is NOT forced).**
    - **(ii) Coupling to L7 — RESOLVED BENIGN (KT splits a safe vertex).** From the KT source (Lemma
      6.13, the Case-III chain `v₀…v_d`): the rank argument reduces a **chain of ≥ 2** consecutive
      degree-2 vertices and splits at a chain endpoint — a vertex whose chain-neighbour is itself
      degree-2 (a **non-hub**), i.e. **coordinator-safe**. KT obtains that ≥ 2 chain from **Lemma 4.6
      itself** (the adjacent-deg-2 pair). So L7's rank argument does not merely *tolerate* a safe
      vertex — it **consumes** one, and never needs a dangerous (single-subdivision, chain-length-1)
      vertex. The split-vertex choice is L7's (`hsplit` gives mere existence; the arm prover picks any
      degree-2 vertex, and re-derives a safe one from its own hypotheses). **No tension between safety
      and the rank core; no W3-level rework re-introducing split-arm minimality is indicated.**
    - **(i) Safe-vertex existence off minimality — FULLY DISCHARGED (2026-07-30).** The **non-rigid**
      habitat (`deficiency G > 0`, all of the split arm except KT's Case III) was PROVEN
      minimality-free same-day (`indep_matroidMG_of_noRigid_of_deficiency_pos` + the generalized
      counting). The **rigid** residue (`deficiency G = 0`, = KT Case III, where minimality
      classically lives) was the remaining open item; the user adjudicated "prove now" the same
      session, and its own route recon (grounded against `IsProperRigidSubgraph`/
      `circuit_induces_isRigidSubgraph`/`matroidMG_indep_iff`) found a direct minimality-free
      argument off the degree-2 vertex alone (no smoothing, no deficiency case-split) — landed as
      `edgeBound_of_noRigid_of_degree_two` (see the L6a-safe-exists entry above for the route).
      **Both halves are now proven**; the split-arm safe-vertex existence obligation is closed in
      its entirety, and `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two` serves both
      deficiency regimes at the L7 call site.
    - **The `splitOff`-invariant finding stands** (it is what made the safe-vertex distinction
      necessary): `splitOff` does **not** preserve feasibility at a *dangerous* vertex
      (computer-verified gadget, `scratchpad/habitat.py` — session-local, not preserved;
      results recorded here), so L7 must split a safe one — which, per
      (ii), is exactly what KT already does.

  - **L6b — the general-position witness seed** (target: `Molecule/Pencil/Witness.lean`).
    **⚠ THE `hcard`-ONLY PINNED SIGNATURE BELOW IS REFUTED (2026-07-30 bank-authorized spike).**
    `hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3` alone does **not** imply `PencilNondegFeasible K G`:
    a graph with a **two-adjacent-hub triangle** satisfies `hcard ≤ 3` yet is infeasible by the LANDED
    `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`). Compiler-checked (scratch,
    reverted): `not_pencilNondegFeasible_of_triangle_two_hubs (…) (hthm hcard) : False`. Smallest
    witness (simple, hand-verified): `{u,v,w,u',v'}`, edges `{uv,uw,vw,uu',vv'}` — `u,v` deg-3 hubs,
    triangle `u,v,w`, every `closedHubNbhd ≤ 2`. **This is an internal plan inconsistency, not new
    math:** the *Blockers* section of `notes/Phase39.md` (the triangle-hub mechanism refutes any purely
    `≤ 3`-closedHubNbhd feasibility criterion) already recorded it; the L6b pin was never reconciled
    against it. The **chart assembly route is sound** — the spike confirmed the v-e template
    (`Steer.lean:421`, `exists_common_seed_linearIndepOn_pencilChartPoint` →
    `exists_fillNbr_pencilChartWF_of_standing` → headline) composes; the block is *only* the missing
    hypothesis. Corrected decomposition (the `#3/#4/#5` moment-curve core is NOT yet resolved — the
    spike never reached it):
    - **L6b's extra hypothesis is now PINNED as `G` triangle-free** (delivered by L6d below; strictly
      stronger than the minimal-necessary `¬(two-adjacent-hub triangle)`, and free here). Re-pinned
      signature (**CORRECTED 2026-07-30 spike — `[G.Simple]`/`[G.Loopless]` added, see below**):
      ```lean
      theorem pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree
          [Inhabited α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
          (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
          (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
            G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False) :
          PencilNondegFeasible K G
      ```
      (The minimal form would weaken `htf` to `… → ¬ (G.PencilHub y ∧ G.PencilHub z)`; not needed —
      L6d gives the full form.) `hcard` matches L6a-transfer's output; `htf` matches L6d's output; both
      at `G := G′`. **Looplessness FINDING (2026-07-30 spike):** the earlier pin (no `Simple`) is
      **FALSE** — a loop `G.IsLink e v v` makes `IsNondegPencilRealization`'s conjunct #5
      `LinearIndependent K ![point v, point v]` unsatisfiable, so `PencilNondegFeasible K G` is false,
      while `hcard`/`htf` (about triangles, not loops) stay satisfied. The needed hypothesis is
      `[G.Loopless]`; the honest producer supplies the stronger `G′.Simple`
      (`splitOff_simple_of_noRigid_of_card`, L6c), so pin `[G.Simple]`.
    - **L6b-i LANDED (2026-07-30, `Molecule/Pencil/Steer.lean`,
      `pencilNondegFeasible_of_selectors_of_satisfiable`):** the assembly — global selectors + the two
      satisfiable-somewhere chart-point-LI families → `PencilNondegFeasible` (the L5-cut-v-e template
      `pencilNondegFeasible_induce_of_pendant_deg3` minus its `.mono` restriction: steer to common seed
      → reconstruct standing WF conjuncts → `fillNbr` re-choice → headline). Takes `[G.Loopless]`.
      **Home: `Steer.lean`, NOT `Witness.lean`** — it needs Steer's `exists_common_seed_linearIndepOn_
      pencilChartPoint`, and `Steer` imports `Witness`, so the headline cannot live in `Witness`.
      The two condition families it consumes (matching the common-seed index sets, `ι = α ⊕ (α×α)`):
      per body `∃ q, LinearIndepOn (pencilChartPoint (ofCoord q) hubSel) (if PencilHub v then {v} else
      closedNbhd v)`; per pair `∃ q, LinearIndepOn … (if Adj p.1 p.2 then {p.1,p.2} else ∅)`.
    - **L6b-ii (spike-first, THE remaining char-free core; core LANDED, callers open):** the two
      satisfiability families above from `hcard` + `htf`, taking `hubSel`/`hHubSel` as inputs (as v-b
      does). **Route SPIKE-GROUNDED to the finite-`Fin 4`/`Pi.single` route of v-b**
      (`exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`), NOT moment-curve/Vandermonde
      (the `RigidityMatroid` moment curve is over `ℝ`; a char-free Vandermonde would need polynomial
      infra — Vandermonde LI, `cross₃`↔cubic-coeffs, root-set proportionality — none in tree, a bigger
      build). **The general core is LANDED (2026-07-30, `Molecule/Pencil/Witness.lean`,
      `exists_coord_linearIndepOn_pencilChartPoint_of_idx`):** given `idx dtgt : α → Fin 4` with `idx`
      injective + avoiding `dtgt s` on each `G.closedHubNbhd s` for `s ∈ S`, and `dtgt` injective on
      `S`, `∃ q, LinearIndepOn K (pencilChartPoint (ofCoord q) hubSel) S` — v-b's construction verbatim
      (`idx` → hub normals, per-body `exists_injective_extension_of_isFin3SelectorOf` padding,
      `exists_smul_cross₃_pi_single` → scaled targets, `linearIndepOn_smul_pi_single` for distinctness),
      char-free with no feasibility/graph structure of its own beyond `hHubSel`. Its conclusion
      type-matches the L6b-i families exactly (axioms clean). **The adjacent-pair caller (`hsat_adj`)
      is LANDED (2026-07-30, `Molecule/Pencil/Witness.lean`,
      `exists_coord_linearIndepOn_pencilChartPoint_adjacentPair`):** at an adjacent pair `{u,v}` the
      two closed hub-neighbourhoods overlap only inside `{u,v}` (a common third hub closes a triangle
      `u–v–w`, ⊥ by `htf`), so a two-set combinatorial core `exists_idx_dtgt_pair` builds `idx`/`dtgt`
      by injecting `closedHubNbhd u` into a `3`-value palette avoiding `dtgt u` and the disjoint
      remainder `closedHubNbhd v \ closedHubNbhd u` into the values avoiding `dtgt v` and the overlap's
      image (palette sizes matching by the `≤ 3` bound, uniformly — no hub case split). Two reusable
      bricks: `exists_injOn_mapsTo_of_ncard_le` (inject a finite set into a no-smaller one;
      upstream-eligible, `FRICTION.md` [mirror-candidate]) + `exists_idx_dtgt_pair`. **L6b COMPLETE
      (2026-07-30):** the **per-body caller `exists_coord_linearIndepOn_pencilChartPoint_perBody`**
      (`Witness.lean`) — hub/degree-`0` centre → the trivial singleton (private
      `…_hubSingleton`); degree-`1` → `exists_idx_dtgt_pair`; degree-`2` → the **new three-set brick
      `exists_idx_dtgt_triple`** (`Witness.lean`, the analogue of `exists_idx_dtgt_pair` for a non-hub
      centre + its ≤ 2 neighbours; the `C₄`-shared external hub is handled *not* by `S`-separation but
      by the overlap bound `(Xa ∩ Xb).ncard ≤ 2` cancelling and the choice `dtgt b := idx a` — which
      collapses the `Xv`-injectivity constraint since `idx b` is forced off `dtgt b`; DERIVATION GUARD
      met, the tight `{a,b,w₁,w₂}` near-bijection fits `Fin 4`). Then the **headline
      `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`** (`Steer.lean`, `[G.Simple]`
      supplying `[G.Loopless]`): `choose` selectors (`hcard`/`ncard_closedNbhd_le_three_of_not_pencilHub`)
      ⟶ the two callers ⟶ `pencilNondegFeasible_of_selectors_of_satisfiable`. `htf` replaces v-b's
      feasibility-derived `not_pencilNondegFeasible_of_triangle_two_hubs`. Gates + axioms clean.
    - **Selector brick — NOT missing (2026-07-30 spike finding):** the `IsFin3SelectorOf`-existence
      lemma for any `ncard ≤ 3` finite set is already in tree as
      `exists_isFin3SelectorOf_of_ncard_le_three` (`Molecule/Pencil/Engine.lean:793`,
      `{s : Set α} (hfin : s.Finite) (hs : s.ncard ≤ 3) : ∃ sel, IsFin3SelectorOf s sel`) — a
      case-split on `ncard ∈ {0,1,2,3}`. L6b-i / the headline `choose` `hubSel`/`nbrSel` from it
      (`hcard` for the hub side; `ncard_closedNbhd_le_three_of_not_pencilHub` for the non-hub side).

    (Historical) The refuted pin + its route, retained for the assembly detail (`#1`/`#2` still hold):
    Target signature
    ```lean
    theorem pencilNondegFeasible_of_ncard_closedHubNbhd_le_three
        [Inhabited α] [Finite α] [Finite β] [Infinite K] {G : Graph α β}
        (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3) :
        PencilNondegFeasible K G
    ```
    Route, grounded against the LANDED chart: reduce to constructing a `PencilSeed K α`
    (`Chart.lean:361`) + global selectors `hubSel nbrSel : α → Fin 3 → Option α`, prove
    `PencilChartWF G seed hubSel nbrSel` (`Chart.lean:465`), then apply the LANDED headline
    `isNondegPencilRealization_pencilChartFramework_of_pencilChartWF` (`Chart.lean:920`) and repackage
    as the `PencilNondegFeasible` existential. The five `PencilChartWF` conjuncts:
      - **#1** `∀ v, IsFin3SelectorOf (closedHubNbhd v) (hubSel v)` — **CONSUMES `hcard`**
        (`IsFin3SelectorOf`'s surjectivity conjunct needs the target `≤ 3`, `Chart.lean:378`); build
        the global selector by choice (reuse `exists_injective_extension_of_isFin3SelectorOf`,
        `Witness.lean`).
      - **#2** `∀ v, ¬ PencilHub v → IsFin3SelectorOf (closedNbhd v) (nbrSel v)` — **FREE** via the
        LANDED `ncard_closedNbhd_le_three_of_not_pencilHub` (`Motive.lean:451`).
      - **#3/#4/#5** the LI conjuncts (`hubSlotNormal` triple LI at every body; `nbrSlotPoint` triple
        LI at every non-hub; adjacent `pencilChartPoint` pairs LI) — **the general-position /
        char-free "moment-curve" core: COMPILER-CHECKED SPIKE REQUIRED (recon method-match).** These
        are route-composition questions in the defeq-fragile chart zone: they compose through `cross₃`
        of the seed's `hubNormal`/`fillHub`/`fillNbr`, COUPLED through the shared `hubNormal w` reused
        across every body whose `closedHubNbhd` contains `w`. Likely route: a char-free
        Vandermonde/general-position `hubNormal` (distinct field elements, `[Infinite K]`; the
        `RigidityMatroid.lean` moment curve is bar-joint / over `ℝ` — NOT reusable, so "à la
        `momentCurve`" is only an analogy) fed through the L3 common-seed primitives
        (`exists_common_seed_linearIndepOn_pencilChartPoint`, `Steer.lean`;
        `exists_common_seed_pencilRow_and_polynomials`, `Engine.lean`; both `[Infinite K]`). **The
        builder MUST write a throwaway spike (`sorry` the residual LI goals, report the kernel-checked
        residuals) before committing — prose cannot settle whether a chosen seed makes all `cross₃`
        triples LI.** If the spike shows the LI core is multi-commit, split L6b into L6b-i (selector
        assembly #1/#2, prose-settleable given `hcard`) and L6b-ii (the general-position seed
        #3/#4/#5, spike-first).

  - **L6d — triangle-freeness of `G′` (LANDED 2026-07-30, `Molecule/Pencil/Habitat.lean`, both pieces
    over `namespace Graph`; axioms clean).** The honest producer of L6b's `htf` at `G′`. Two pieces:
    a small proper-rigid brick + the transfer wrapper. Pinned signatures below matched verbatim; the
    only build subtleties were routine (defeq closes `![…]`-indexed `Fin 4` goals without `simp`,
    TACTICS-QUIRKS §46; a `rintro rfl` on `f = e₀` substitutes `e₀` away, use a named `intro`+`▸`,
    §4).
    - **The `C₄` brick** — the induced-4-cycle analogue of the LANDED `triangle_isProperRigidSubgraph`
      (`Operations.lean:994`), built the same way (`isKDof_zero_of_cycle` at `m = 4` for `0`-dof,
      instead of `isKDof_zero_of_triangle`; `E(H) = {4 cycle edges}` by the induced-edge antisymmetry
      under `G.Simple`; properness from `|V(G)| ≥ 5`). `cycle_isProperRigidSubgraph` (`Operations.lean:
      1079`) does **not** apply — it needs all-but-one cycle vertex *closed* (degree exactly its two
      cycle edges), but the offending `C₄`'s two hub corners carry external edges. Target:
      ```lean
      theorem c4_isProperRigidSubgraph [Finite α] {G : Graph α β} [G.Simple] {p q r s : α}
          {e₁ e₂ e₃ e₄ : β} {n : ℕ} (hD : 4 ≤ bodyBarDim n)
          (h₁ : G.IsLink e₁ p q) (h₂ : G.IsLink e₂ q r) (h₃ : G.IsLink e₃ r s) (h₄ : G.IsLink e₄ s p)
          (hpq : p ≠ q) (hqr : q ≠ r) (hrs : r ≠ s) (hsp : s ≠ p) (hpr : p ≠ r) (hqs : q ≠ s)
          (hpr_nadj : ∀ e, ¬ G.IsLink e p r) (hqs_nadj : ∀ e, ¬ G.IsLink e q s)  -- chordless
          (hcard : 5 ≤ V(G).ncard) :
          ∃ H : Graph α β, H.IsProperRigidSubgraph G n
      ```
    - **The transfer wrapper** `splitOff_triangleFree_of_noRigid`: at a degree-2 `v` of a simple,
      no-proper-rigid `G` with `|V(G)| ≥ 5`, `G′ = G.splitOff v a b e₀` is triangle-free (= L6b's
      `htf`). Target:
      ```lean
      theorem splitOff_triangleFree_of_noRigid
          [Finite α] [Finite β] {G : Graph α β} [G.Simple] {n : ℕ} {v a b : α} {e₀ : β}
          (hD : 4 ≤ bodyBarDim n) (hV : 5 ≤ V(G).ncard)
          (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
          (hdeg : G.degree v = 2) (heₐ : ∃ eₐ, G.IsLink eₐ v a) (e_b : ∃ e_b, G.IsLink e_b v b)
          (hab : a ≠ b) :
          ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
            (G.splitOff v a b e₀).IsLink e₁ x y → (G.splitOff v a b e₀).IsLink e₂ y z →
            (G.splitOff v a b e₀).IsLink e₃ z x → False
      ```
      Route (grounded): a `G′`-triangle either (i) uses no fresh edge `e₀` ⟹ its three edges survive
      in `G − v ≤ G` ⟹ it is a `G`-triangle ⟹ `triangle_isProperRigidSubgraph` (`|V| ≥ 4`) ⟹ ⊥ via
      `hnoRigid`; or (ii) uses `e₀ = ab` ⟹ its apex `c` is a common `G`-neighbour of `a, b`, `c ∉
      {v,a,b}`, and `{v,a,b,c}` is a chordless induced `C₄` in `G` (`va, vb` from `heₐ/e_b`; `ac, bc`
      surviving; `ab ∉ E(G)` since else `{a,v,b}` is a `G`-triangle killed by (i)'s route; `vc ∉ E(G)`
      since `deg_G v = 2`, `N(v) = {a,b}`, `c ∉ {a,b}`) ⟹ `c4_isProperRigidSubgraph` ⟹ ⊥ via
      `hnoRigid`. **No `2EC`, no safe hypothesis** — those enter only via L6a-transfer's separate
      `closedHubNbhd ≤ 3` obligation. `|V(G)| = 4` is a base case (a `4`-vertex no-proper-rigid 2EC
      triangle-free graph is `C₄`, all degree-2, no hubs; its `splitOff` is a hub-free triangle,
      trivially feasible) — dispatched with L6c's base.

  - **L6c — `G′.Simple`: NOT a new build leaf, a citation folded into the L7 assembly.** For
    `G′ = G.splitOff v a b e₀` at `|V(G)| ≥ 4`, `G′.Simple` is EXACTLY the LANDED
    `splitOff_simple_of_noRigid_of_card` (`Induction/Operations.lean:1104`), consuming `[G.Simple]`
    (split-arm antecedent), the two edges `eₐ : v–a`, `e_b : v–b` at the degree-2 vertex,
    `4 ≤ V(G).ncard`, and `hnoRigid` (split-arm antecedent) — no new construction, no triangle
    argument to re-derive (it is internal to that lemma, via `triangle_isProperRigidSubgraph`). Only
    the `|V(G)| = 3` edge case (triangle spanning, not proper; `G′` on 2 vertices, base-sized) needs a
    separate base dispatch — also an L7/assembly concern.

  **L6 → L7 wiring (settled 2026-07-29; L6d thread added 2026-07-30; the `closedHubNbhd`-transfer
  route, NOT the discarded "re-derive `G′` habitat properties" one).** The chain L7 runs: split-arm
  antecedent `PencilNondegFeasible K G` `→` (landed
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`)
  `∀ w, G.closedHubNbhd w ≤ 3` `→` (**L6a-transfer** at a *safe* `v`) `∀ w, G′.closedHubNbhd w ≤ 3`;
  **and, in parallel from the split-arm's `hnoRigid` + `|V| ≥ 5`,** (**L6d**) `G′` triangle-free;
  the two together `→` (**L6b**) `PencilNondegFeasible K G′` `→` (IH generic half + **L6c** `G′.Simple`)
  `HasGenericPencilRealization K 3 G′` `→` (L7 extension) `HasGenericPencilRealization K 3 G`. The
  earlier "apply a combinatorial ≤ 3 lemma to `G′` from its own 2EC/no-rigid" plan is DEAD (that lemma
  is false, refuted above); the transfer route needs `G′`'s habitat properties *not at all* — only
  `G`'s feasibility + a safe split. **L7 owns the split-vertex choice** and picks a safe one — which,
  per the revised posture above, is exactly the adjacent-deg-2-pair endpoint KT's Case III already
  splits (coupling benign). Existence = L6a-safe-exists (**both halves PROVEN** — non-rigid and
  rigid).

  **Build order.** L6a-transfer LANDED; **L6d LANDED** (the `C₄` brick `c4_isProperRigidSubgraph`
  then `splitOff_triangleFree_of_noRigid` — a faithful `m = 4` mirror of
  `triangle_isProperRigidSubgraph`, no chart stack). **L6b next** (spike-first): both its inputs are
  now honest producers in tree (`hcard` from L6a-transfer, `htf` from L6d), so it is fully
  buildable given its `hcard`/`htf` hypotheses. L6a-safe-exists: **both halves LANDED**
  (`indep_matroidMG_of_noRigid_of_deficiency_pos` + the generalized counting for the non-rigid
  half; `edgeBound_of_noRigid_of_degree_two` for the rigid half — see the L6a-safe-exists entry
  above). L6c is a citation at assembly time; L8 since dissolved into (K)'s discharge (its
  bullet below).
- **W5-L7** (the research core): the single-candidate Claim-6.12 replacement — at the
  Case-III habitat, a chart seed of `G′` realizing rank `6(|V|−2)` *and* the
  candidate-`M₁` escape `r ⬝ Λ²Π̂(a) ≠ 0` (then the assembly + the output's own
  nondegeneracy conjuncts). The product route reduces it to a ≢-0 certificate for the
  escape polynomial on the chart; N2's seeds witness it on one habitat instance, and
  the uniform certificate (a canonical symmetric witness seed per chain habitat, or an
  algebraic identity from KT eq. (6.44)) is the genuinely new mathematics — first
  W5 *research* dispatch once L0–L4 are in tree, numerics-first per instance as
  before. *(Lean shape RE-PINNED 2026-07-30: the carried form is the `hK`
  rank-increment implication, not an `escapePoly` ≢-0 statement — see §"W5-L7
  research recon" "Lean decomposition".)*
- **W5-L8** (sub-obligation (ii)): the k = 0 residue (verdict 5; spiked emptiness route).
  **RULED 2026-07-30 (L7c assembly recon): dissolves as a standalone W5 leaf; survives only as
  a flagged sub-item of kernel (K)'s discharge.** L8's consumer was the split-arm rank core's
  Claim-6.11 step (KT p. 684 consumes minimality twice; the spiked emptiness lemma
  `isMinimalKDof_of_isKDof_zero_of_noRigid` would restore it on the `k = 0` branch — never
  built). Under the 2026-07-30 re-shape that step lives entirely inside `hK`'s *discharge*
  (deferred research): nothing in the buildable L7c assembly consumes minimality (`hK` is
  minimality-free by pinned shape), and the rigid-half landing
  `edgeBound_of_noRigid_of_degree_two` demonstrated the fallback — re-derive a minimality
  consumer directly — is viable and landed its tool set. Do NOT build the emptiness lemma
  speculatively: `hK` is deficiency-agnostic, so the (K) research recon must re-pin what (if
  any) minimality restoration its `k = 0` branch wants; the emptiness route stays the
  recommended tool *there*, with the count squeeze on spanning circuits as its one open step
  (unchanged from verdict 5).

Attack order: L0 → L1 → L2 → L3 → L4 (the device spine), then L5; L6/L8 were
parallel combinatorial tracks after L0 (L8 since dissolved into (K)'s discharge — see its
bullet); L7 last (consumes L2–L4, L6).

### Open after this pass (owner)

- ~~L6a-safe-exists, rigid (`k = 0`) half~~ **CLOSED same day** — landed as
  `edgeBound_of_noRigid_of_degree_two` (a direct, minimality-free argument off the degree-2
  vertex, no smoothing/subdivision detour; see the L6a-safe-exists entry above). *Both the
  `k = 0` half and the L6/L7 coupling are RESOLVED this pass (2026-07-30) — see §"W5 leaf
  decomposition" L6a.*
- L7's uniform escape certificate — the research core (W5 dispatch, numerics-first).
- Whether the split arm needs further minimality-free analogues of KT Lemma 4.3
  beyond Claim 6.11's inputs — assess inside the arm build (builder).
- W4's constrained-substrata chart (graded extension, N6 blueprint) and witness
  generality — ~~unchanged from §W4 route, consumes the W5 device (W4 recon)~~
  **decomposed 2026-07-30**: both now live inside kernel (K-c)'s discharge; see
  §"W4 decomposition recon".
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
  IH obligation is vacuous there. **RESOLVED 2026-07-30 (W4 decomposition
  recon):** feasibility propagation is NOT derived — the arm *dispatches* on
  the contracted graph's `Simple ∧ Feasible` conditioning; when it fails, the
  generic input to kernel (K-c) is unavailable and the case routes to the
  vertex-removal branch (`hnoGood`). See §"W4 decomposition recon".

### Numerics index (this pass)

| # | experiment | result |
|---|---|---|
| N4 | theta(2,2,2), interiors collinear on the hub-planes' meet line, hubs generic (5 samples + 2 generic + 2 coplanar controls) | 24 = target in all (controls 24) |
| N5 | K3,3, sides on two lines (5 samples + controls) | 30 = target in all (one coplanar control hit a deeper degeneration, 29 — not load-bearing) |
| N6 | spider-K4 coincidence branch (`u,a,b,c` coplanar; 6 samples + 2 generic) | 54 = target in all |

L6a-safe-exists numerics (2026-07-30 recon; exact-ℚ Plücker rigidity-matrix rank + exact partition
deficiency; scripts `scratchpad/{kzero,kzero2,petersen,broad}.py` — session-local, not
preserved; results recorded below; reproduce `habitat/safe/exact/search`):

| # | experiment | result |
|---|---|---|
| L1 | `S(M)` (subdivide every edge) for `M ∈ {K4, prism, K3,3}` — rigid? proper rigid subgraph? | all rigid (def 0, boundary `5\|E\|=6\|V\|`); all carry a proper rigid subgraph (`S(K4)⊃C6`; `S(K3,3)⊃S(K₃,₂)`) |
| L2 | `def(S(H))` for dense `H ≤ K3,3`: `K₂,₃`, `K₃,₂`, `C4`, `K3,3−e`, `K3,3−v` | `S(K₂,₃)=S(K₃,₂)=θ(4,4,4)` rigid (def 0); `S(C4)=C8` def 2; `S(K3,3−e)`, `S(K3,3−v)` rigid |
| L3 | **`S(Petersen)`** (girth-5 cubic, triangle- & `K₂,₃`-free; sharpest evasion candidate) | rigid, corank 6, 2EC, feasible, no adjacent deg-2 pair — **BUT** `S(Petersen−v)` (21 vtx) is a proper rigid subgraph → not a counterexample |
| L4 | broad search: **all** subdivision patterns of `K4/K5/K3,3/prism` (simple+2EC+deg-2, no adj pair) | **0** coordinator-safe counterexamples (every one has a proper rigid subgraph); k=0 sub-case: 0 |
| L5 | reproduced prior all-dangerous route-breaker search (`safe/search.py`) | 0 split-safe route-breakers (PM subdivisions + direct hub-cycles `C_k`, `k≥7`) |

### W5-L7 research recon (2026-07-30): the uniform escape certificate

The phase's research core. Question: is the single-candidate escape `r ⬝ Λ²Π̂(a) ≠ 0`
(candidate `M₁`, KT eq. (6.42)) true pencil-generically across **all** Case-III chain
habitats, and by what argument? Method: exact-ℚ Plücker rigidity-matrix experiments
across ≥ 3 structurally-distinct habitats (scripts `notes/scripts/escape/*.py`; same model
as §R2/N2 — molecular `G²`, hinge extensor `ĉ_u ∧ ĉ_v`, 5 rows/edge = `C_e^⊥`, pencil =
every degree-≥3 body's closed star coplanar), plus a decisive sign-change probe. KT
pp. 690–691 re-verified against the `.refs` copy this pass (see below).

**Setup recap (grounded in KT pp. 690–691, read directly this pass).** `M₁` full rank
⟺ `r ∉ (span C(L))^⊥` for the free line `L ⊂ Π(a)` (KT p. 690), and since `a` is
degree-2 in `G^{ab}_v` the line `L` is *completely* free, so `∪_L C(L)` spans all of
`Λ²Π̂(a)`. Hence **escape `M₁` ⟺ `r ⬝ w ≠ 0` for some `w ∈ Λ²Π̂(a)`**. Structurally
`r ⬝ C(q(ab)) = 0` (r is a combination of the `ab`-rows) and `r ⬝ C(q(ac)) = 0` (KT
(6.44)); `C(q(ab)) = â∧b̂` and `C(q(ac)) = â∧ĉ` span the 2-dim `pencil(a) ⊂ Λ²Π̂(a)`.
Since `Λ²Π̂(a) = ⟨â∧b̂, â∧ĉ, b̂∧ĉ⟩`, the escape collapses to a **single scalar**:
**`M₁` works ⟺ `r ⬝ (b̂ ∧ ĉ) ≠ 0`**, i.e. `r` is not orthogonal to the extensor of the
line joining the two chain-end points `pt(b), pt(c)` (a line *not* through `pt(a)`).
All three facts (`r⊥â∧b̂`, `r⊥â∧ĉ`, `M₁ ⟺ r⬝(b̂∧ĉ)≠0`) verified numerically at every
seed below.

**Numerics N7 — the escape across five chain habitats (exact-ℚ).** Each habitat is a
double-subdivision of a base graph with `m₀ = 2n₀−2` (the tightness `5|E|=6(|V|−1)`
condition for double-subdivision), split at an interior degree-2 vertex adjacent to a
hub — giving `G^{ab}_v` with `5|E'| = 6(|V'|−1)+1` (nullity 1, from the
−1 vertex / −1 edge net of the split; ~~this is a **general Case-III fact**, not
habitat-specific~~ **corrected 2026-07-30, non-constancy recon: general only for
tight habitats** — the true general form is `index(G′) = index(G) + 1` with
`index := 5|E| − 6(|V|−1)`, and the hK class contains `index(G) ≥ 1` habitats
whose `G′` has corank ≥ 2, see §"(K) non-constancy recon" below).
Reproduce: `python3 notes/scripts/escape/run_habitats.py`.

| # | habitat (double-subdiv of …) | chain-end degs (b,c) | `\|V'\|` | rank / nullity | dim S | `M₁` escape `r⬝(b̂∧ĉ)≠0` |
|---|---|---|---|---|---|---|
| H1 | K4 (= N2 reproduce) | (3,3) | 15 | 84 / 1 | 5 | ✓ 5/5 |
| H2 | W4 wheel, **spoke** chain | (4,3) | 20 | 114 / 1 | 5 | ✓ 5/5 |
| H2b | W4 wheel, rim chain | (3,3) | 20 | 114 / 1 | 5 | ✓ 4/4 |
| H3 | W5 wheel, **spoke** chain | (5,3) | 25 | 144 / 1 | 5 | ✓ 4/4 (1 seed nullity-2, not generic — skipped) |
| H4 | K5 − perfect matching | (3,3) | 20 | 114 / 1 | 5 | ✓ 4/4 |
| H5 | prism + diagonal | (4,4) | 25 | 144 / 1 | 5 | ✓ 4/4 |

In every rank-target / nullity-1 seed: KT (6.44) holds, `dim S = 5` (the §R3 shortfall,
now confirmed structural — `3+2+2−1−1`, the two overlaps `â∧b̂ ∈ Λ²Π̂(a)∩pencil(b)`,
`â∧ĉ ∈ Λ²Π̂(a)∩pencil(c)`), and `M₁`, `M₂`, `M₃` all work individually. **0 escape
failures across all habitats and every chain-end degree pair (3,3)/(4,3)/(5,3)/(4,4).**

**Finding 1 — the escape has a genuine in-stratum failure locus; route (b) as a
standalone identity is REFUTED.** Sweeping `a` along the meet line `Π(b)∩Π(c)` (the one
free parameter for `a`, exact-ℚ; `notes/scripts/escape/probe_zero.py`), the escape value
`E(t) = r⬝(b̂∧ĉ)` **changes sign** (seeds 1000 and 3000 both take `+` and `−`), with
rank 84 / nullity 1 holding throughout. Bisection (`notes/scripts/escape/localize_zero.py`) pins a zero at an
interior `t* ≈ −2.5311710127` where both bracket endpoints (width `~10⁻¹²`) are valid
rank-84/nullity-1 pencil realizations — so **`M₁` genuinely fails on a codimension-1
in-stratum locus**. Consequence: no algebraic identity can force `E ≠ 0` (a non-constant
`E` that takes both signs on the connected stratum must vanish); the (6.44) identity
gives only `r ⊥ pencil(a)` (2 conditions), and the escape is a *third, independent*
condition. **Routes (a) and (b) are therefore not alternatives** — the design doc's
"(a) canonical seed OR (b) algebraic identity" framing was optimistic. (b) survives only
as a possible cleaner *expression* for `E` feeding a ≢-0 argument, never as a
self-contained certificate. The escape is genuinely generic and **requires the in-stratum
genericity device** (Chart/Engine/Reseed) — exactly the N2 "failure locus is a proper
closed condition, seeds are literal seeds" picture, now proven (not just asserted) to have
a nonempty failure locus.

**Finding 2 — the KT-faithful target is the disjunction `r ∉ S^⊥`; single-`M₁` is
generic-only (optimism guard).** KT's actual Claim 6.12 asks only that *at least one* of
`M₁/M₂/M₃` be full rank, i.e. `r ∉ S^⊥` where `S = Λ²Π̂(a)+pencil(b)+pencil(c)`
(`dim S = 5`, so `S^⊥` is 1-dim). The all-three-fail locus `r ∈ S^⊥` was **never** hit
(0 / 92 valid configs, incl. a targeted sweep across the `M₁` zero and 8 seeds × 7 `t`;
`notes/scripts/escape/probe_disjunction.py`): where `M₁` fails, `M₂` and `M₃` still work. So the disjunction is
far more robust than any single candidate. **This revises the design doc's single-candidate
reduction:** choosing `M₁` alone is *sound* (M₁ full rank ⟹ target rank) and its escape
*is* generically true, but it is **not** a structural shortcut — `M₁`-alone needs the
genericity device just as much as the disjunction would (the design doc's "L ⊂ Π(a) is
completely free, so `M₁` is the cheapest" is about the *device parametrisation* of the free
line, not about the escape being free of a failure locus). The single-`M₁` polynomial (one
`6×6` minor) is simpler to feed the engine than a three-way disjunction, so it stays the
recommended target — but the note that it "works alone, not narrowly" (N2) is a
*generic-point* statement, not an every-point one.

**Route verdict.** The escape is a genuine genericity statement; the correct and only
viable shape is **route (a) — a ≢-0 certificate for the escape polynomial on the pencil
chart, promoted to generic by the landed device.** The device is *already built to consume
it*: `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`) takes the rank
rows (an LI `pencilRow` subfamily) together with finitely many polynomials each nonzero
*somewhere*, and its own docstring names "W5-L7's rank target *and* its candidate-`M₁`
escape polynomial" as the intended consumer. So the whole L7 rank extension reduces
mechanically to **one ≢-0-somewhere obligation** on the escape polynomial `E` — and *that*
is the genuinely-new mathematics.

**The research kernel (crisp).** Prove, uniformly across all Case-III chain habitats:
> **(K)** The escape polynomial `E` (the `M₁` `6×6`-minor determinant, equivalently
> `r ⬝ (b̂∧ĉ)` as a rational function of the chart seed) is **not identically zero** on
> the pencil chart of `G^{ab}_v` — equivalently, `∃` a chart seed `q` with `E(q) ≠ 0`.

Numerics support (K) strongly (5 habitats, all degree pairs, 0 counterexamples; and the
weaker disjunction target `r ∉ S^⊥` is even more robust). What neither numerics (finite)
nor (6.44) (refuted as an identity) settles is *why (K) holds for every habitat*. The
obstruction is that `E` depends on the **global** redundancy `r` (the `a`-block of the
unique stress of `G^{ab}_v`, supported on the fundamental circuit of the excess edge `ab`,
which need not be local), so a per-instance seed cannot discharge the `∀ G` Lean leaf, and
a uniform symbolic value of `E` at a canonical seed appears to require solving the global
stress uniformly.

**Lean decomposition — the L7 assembly is BUILDABLE NOW with (K) as a bounded hypothesis**
(the same posture L6a-safe-exists's rigid `k=0` half rode under, before its 2026-07-30 route
recon closed it — (K) is the one hypothesis of this shape left standing). L7 discharges
`hsplit` of `pencil_conjecture_of_arms_pair` (`Pair2.lean:1229`):
given `G` loopless, `3 ≤ |V(G)|`, `2EC`, no-proper-rigid, `∃ v, G.degree v = 2`, and the IH
`∀ G', |V'| < |V|, PencilPair K 3 G'`, produce `PencilPair K 3 G`. Buildable leaves:
- **L7a — safe split + IH generic half. LANDED 2026-07-30**
  (`hasGenericPencilRealization_of_splitOff_of_safe`, `Molecule/Pencil/Escape.lean`; safe-vertex
  *existence* stays L6a-safe-exists, not this leaf). Pick a safe vertex `v` (L6a-safe-exists; both
  halves now LANDED), form `G' = G.splitOff v a b e₀`,
  and from the IH extract `HasGenericPencilRealization K 3 G'` via the landed L6 chain:
  `PencilNondegFeasible K G` (the `PencilPair` generic-conjunct antecedent) →
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` →
  `ncard_closedHubNbhd_splitOff_le_three_of_safe` (L6a-transfer) + `splitOff_triangleFree_of_noRigid`
  (L6d) → `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` (L6b,
  `Steer.lean:1344`) → IH generic half + `splitOff_simple_of_noRigid_of_card` (L6c). This
  leaf is combinatorial glue, no new math.
- **L7b — the rank-to-generic steering assembly. RE-PINNED 2026-07-30** (L7b-shape route recon,
  fired after the `escapePoly` build dispatch returned BLOCKED). The original pin here — `hEsc :
  ∃ q, MvPolynomial.eval q (escapePoly hubSel G a b) ≠ 0` with `escapePoly` the `M₁` `6×6`-minor
  as an `MvPolynomial`, sized "L3-style, buildable" — is **refuted**: KT eq. (6.42)'s second
  block-row is the *global* stress `r = Σ_j λ_j r_j` (left null vector of the entire rigidity
  matrix of `G′`), so a faithful `escapePoly` needs a corank-1-null-vector-by-cofactors gadget
  that does not exist in tree (multi-commit new infra), and any polynomial formula must fix a
  maximal nonsingular submatrix whose nonsingularity is itself seed-dependent — the column choice
  leaks into the pinned statement ("chosen minor ≠ 0 AND `E ≠ 0`"). **And no polynomial is
  needed**: the engine's rank slot is an LI witness —
  `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`) takes `hLI` directly and
  *internally* polynomializes it (`exists_polynomial_ne_zero_of_linearIndependent_pencilRow`), so
  an ∃-LI-witness escape is already, by the landed engine, equivalent to a maximal-minor-≢-0
  statement without ever defining the minor. Re-pinned L7b (**split-data-free** — `v`, `a`, `b`,
  `e₀`, `hG′`, `hsafe` all drop out; a reusable "L6b + rank" headline; home
  `Pencil/Escape.lean`; ONE commit, ~300–450 lines — every call a landed pattern: the v-f-6 rank
  thread (`Steer.lean:997ff`) with `G` for `G.induce V₁`, the L6b-i WF body (`Steer.lean:1271`),
  the `Witness.lean:1570/1664` somewhere-producers at an arbitrary correct selector, the pinch
  (`Steer.lean:693`)):
  ```lean
  theorem hasGenericPencilRealization_of_independent_pencilRow_target
      [Inhabited α] [Finite α] [Finite β] [Infinite K] {G : Graph α β} [G.Simple]
      (hGne : V(G).Nonempty)
      (hcard : ∀ v, (G.closedHubNbhd v).ncard ≤ 3)
      (htf : ∀ e₁ e₂ e₃ x y z, x ≠ y → y ≠ z → x ≠ z →
        G.IsLink e₁ x y → G.IsLink e₂ y z → G.IsLink e₃ z x → False)
      (hEsc : ∃ (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K)
          (s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)),
        (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
        (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
        ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
        LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))) :
      HasGenericPencilRealization K 3 G
  ```
  **Signature corrected 2026-07-30** (`[Nonempty α]` → `[Inhabited α]`, coordinator-adjudicated):
  `hEsc`'s own *type* reads `G.endsOf`, and `Graph.endsOf` needs `[Inhabited α]` for its off-`E(G)`
  junk value — a statement-level occurrence no tactic-local `Classical.inhabited_of_nonempty` can
  reach, so the route recon's `[Nonempty α]` pin failed to elaborate (builder-caught, BLOCKED,
  compile-verified fix). `[Inhabited α]` subsumes `[Nonempty α]` for existence purposes; the L7c
  call site has concrete vertices (`v`/`a`/`b`) in hand, so this costs nothing downstream. **The
  `hK` pin below has the identical `G.endsOf` shape and needs the same correction** — flagged
  there for the L7c builder.

  Route: destructure `hEsc`; `P` := the per-body + adjacent-pair point conditions at `hEsc`'s own
  `hubSel` (`exists_coord_linearIndepOn_pencilChartPoint_perBody`/`_adjacentPair`, each converted
  per-condition by `exists_polynomial_ne_zero_of_linearIndependent_pencilChartPoint`); one
  `exists_common_seed_pencilRow_and_polynomials` call; reconstruct the standing WF conjuncts +
  the `fillNbr` re-choice + read off the realization (the L6b-i body); pinch the rank at the
  common seed and transport to the re-chosen seed by `pencilChartFramework_congr` (the v-f-6
  thread). In the L7c assembly the antecedents come free: `hcard` from `hfeas`
  (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), `htf` from `hnoRigid` +
  `triangle_isProperRigidSubgraph` (`|V| ≥ 4`). The bare `HasPencilRealization K 3 G` half is the
  forgetful map *where the generic antecedents hold* — see residue (ii) below.
- **Kernel (K) as carried: `hK`, realization-input + extension-shaped** (re-pinned 2026-07-30).
  The recon **rejected** carrying the bare full-family form ((K)-full, no input): given
  feasibility it is equivalent to the generic half of the conjecture itself at `G` — the
  induction would carry its own conclusion schema, and L7a plus the whole L6 chain become dead
  code. The input must be the realization-level `HasGenericPencilRealization K 3 (G.splitOff v a
  b e₀)` — exactly L7a's landed output — NOT a row-LI-at-a-seed input, which would force a
  chart/selector choice into the statement and hit the G/G′ selector mismatch
  (`closedHubNbhd_G(a) = closedHubNbhd_{G′}(a) \ {b}` and symmetrically at `b`, from `¬Adj_G a b`
  (triangle-free habitat); a G′-correct `IsFin3SelectorOf` at `b` *must* select `a` when `a` is a
  hub, and is then G-incorrect). Carried form — the L7c hsplit assembly's sole remaining
  `have`-hyp slot (the rigid `k=0` half closed 2026-07-30); antecedent discipline: (K) carries
  every hypothesis the assembly has at the call site:
  ```lean
  hK : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
    G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
    G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
    (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
    HasGenericPencilRealization K 3 (G.splitOff v a b e₀) →
    ∃ hubSel q s, (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
      (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
      ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
      LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))
  ```
  **Same `[Inhabited α]` correction applies here (flagged 2026-07-30, not yet built):** `hK`'s
  conclusion has the identical `pencilRow … G.endsOf …` shape as `hEsc` above, so whatever
  signature carries `hK` (the L7c hsplit assembly) needs `[Inhabited α]` in scope — cheap there,
  since the assembly already has the concrete vertex `v` in hand (`⟨v⟩ : Inhabited α`).

  This is **KT Claim 6.12 at the rank-increment (consequence) level** — KT p. 690's disjunction
  ("one of `M₁/M₂/M₃` nonsingular") implies it directly; the blueprint node, when written, states
  the increment form with a remark naming KT's sharper disjunction and the `M₁` route as the
  intended proof, and notes the engine-equivalence to a minor-≢-0 statement. **Claim612-style
  opaque functionals** (`case_III_claim612_gen`, `Molecular/RigidityMatrix/Claim612.lean:1339`)
  are the *discharge's* tool (the corank-1 stress of a concrete matrix at a fixed seed needs no
  polynomial gadget), not a carried shape — Finding 1's in-stratum failure locus makes any
  ∀-realization opaque-`r` escape hypothesis false, and the ∃-form collapses into `hK`. Both
  prior attack routes factor through `hK`'s discharge without loss (route 1's `escapePoly` infra
  can still be built *inside* the discharge if that attack is chosen; route 2's opaque-`r`
  fixed-seed `M₁` linear algebra is how the discharge should do the block computation).
  *(Route 1 has since been closed NO-GO — see §"(K) route-1 gate" below.)*

**Not-buildable-now inventory (REVISED 2026-07-30, L7c assembly recon):** TWO carried kernels,
not one — kernel **(K)** (the `hK` implication above) and the bare-half kernel **(K-bare)**
(`hbareSplit`, residue (ii) below, settled this pass: NOT buildable without new mathematics).
L7a and L7b are both LANDED (`Escape.lean`); the L7c hsplit assembly carries `hK` + `hbareSplit`
and is otherwise decomposed into buildable leaves (the "L7c decomposition" block below).
Recorded corrections + tracked residues from the 2026-07-30 L7b-shape route recon:

- **Bookkeeping correction to the earlier "+6 new rows" prose.** The `+6` is the increment over
  the *full* `G′`-row space (which includes the `e₀ = ab` block — not a subfamily of `G`'s rows,
  `e₀ ∉ E(G)`). Against the shared `G−v` rows the two new edges `eₐ`, `e_b` must contribute
  **10** (H1 habitat numbers: common rows 80 and independent — the unique dependency needs the
  `e₀`-block — G-target 90). And `splitOff_deficiency_le/ge` (`SplitOffDeficiency.lean:62/197`)
  pin `def(G′) ∈ {def(G), def(G)−1}`, so the increment over `G′` is 6 *or* 5 by branch. The
  refuted `escapePoly` pin silently baked in one branch and one bookkeeping reading; `hK`'s
  ∃-LI form is branch- and bookkeeping-agnostic (all of it discharge-internal). `hK` is also
  safely vacuous exactly where unusable: a ≥ 4-member `closedHubNbhd` in `G` transfers into `G′`
  (the `G′` sets at `a`/`b` are supersets, elsewhere equal off `v`), killing the
  `HasGenericPencilRealization G′` antecedent.
- **The G′-chart → G-chart re-seed moves out of L7b entirely, into (K)'s discharge.** There the
  landed bricks apply (`exists_pencilSeed_of_nondeg`, `Reseed.lean:65`;
  `exists_independent_pencilRow_subfamily_at_toCoord_of_reseed`, `Steer.lean:813` — its `hubSel`
  is a free variable, only the point-reproduction `hpt` matters), modulo one genuinely new
  **split re-seed** sub-leaf: reproduce the `G′`-realization's points on a G-correct chart. At
  `a`/`b` the G-selector selects a *subset* of the realization's orthogonality set, so the freed
  slot lowers the `cross₃` arity and the landed arity-≤ 2 exact-hit lemmas get easier, not
  harder. This is the recon's single riskiest assumption (no landed instance); if it is harder
  than expected only the discharge's effort estimate moves — `hK` itself stays well-posed.
- **Residue (i) — small `|V|`: PINNED 2026-07-30 (L7c assembly recon) as leaves L7c-3/L7c-4
  below.** `hsplit` supplies `3 ≤ |V|`; L7a and the `htf` derivation need `5 ≤` / `4 ≤`. The
  `|V| ∈ {3,4}` habitat is exactly the spanning `C₃`, `C₄` (identification grounded below) — and
  **`htf` is false at `C₃`**, so the L6b feasibility route fails there; both are direct-witness
  leaves with a fully landed rank thread (`theorem_55_cycle` + bridge B1), see the pins.
- **Residue (ii) — the bare half off-feasibility: SETTLED 2026-07-30 (L7c assembly recon) —
  NOT buildable without new mathematics; a second carried kernel (K-bare), pending user
  adjudication.** `PencilPair`'s bare conjunct (`HasPencilRealization`, rank target included,
  `Statement.lean:103`) is owed *unconditionally*, and the habitat does NOT force feasibility
  (the 19-vertex theta / 17-vertex gadget of the L6a arc: 2EC + no-proper-rigid + simple +
  degree-2-carrying with a 4-member `closedHubNbhd`). Grounded findings (all against landed
  source, this recon):
  1. **The panel precedent structurally cannot cover it.** The landed program's split arm
     produces its bare conjunct ONLY as M4-forgetful ∘ generic — the `hsplitZero` arm of
     `theorem_55_minimalKDof_k_all_k` (`Theorem55.lean:2499`): G0
     (`simple_of_isMinimalKDof_of_noRigid`) discharges the pair's *only* conditioning
     (simplicity), then `hforget_k`. No bare split-extension lemma exists anywhere in the tree
     (W3-L7 `pencil_conjecture_of_arms` also takes `hsplit` as a hypothesis at the bare motive;
     the loop/base/cut bare halves are elementary and split-free). The pencil pair's *second*
     conditioning layer (feasibility) is exactly what the habitat does not force — a genuinely
     new obligation with **no KT analogue** (KT Thm 5.5 conditions on simplicity alone, which
     its split habitat supplies).
  2. **Infeasibility propagates to `G′`, so the generic machinery is dead on both sides.** In
     the habitat (`htf` on `G` from `hnoRigid` + `triangle_isProperRigidSubgraph`, `4 ≤ |V|`),
     `¬PencilNondegFeasible K G` forces some `≥ 4`-member `closedHubNbhd` (contrapositive of the
     L6b headline); the witness body is `≠ v` and `v`-free (a deg-2 `v` is no hub), and
     `splitOff` preserves all degrees off `v` (hub set unchanged, the sole new adjacency `ab`),
     so the same witness makes `G′` infeasible
     (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, contrapositive). Hence the
     IH's generic conjunct is vacuous at `G′` AND `hK`'s realization antecedent is
     unsatisfiable — only the IH's *bare* `HasPencilRealization K 3 G′` survives as input.
  3. **The extension is Case-III-increment-strength; elementary dodges fail.** Against the
     shared `G−v` rows the two new 5-row blocks must contribute in full (the "+10" bookkeeping
     correction above) — exactly what the escape certifies, but now from a possibly *degenerate*
     `G′`-realization (KT's rank/nullity-1 stress structure unavailable). The
     delete-instead-of-split dodge (bare IH at `G − v`, re-add `v`; the two fresh blocks' v-parts
     give `+6`) is FALSE in general: `def(G−v)` can exceed `def(G)` (`C₅ → P₄`: `0 → 3`) — which
     is exactly why KT splits off rather than deletes. And the chart device cannot express a
     4-member hub-neighbourhood incidence (`cross₃` takes three), so no landed in-stratum
     genericity machinery applies at the infeasible `G` either.
  4. **Evidence gap (flag).** All escape numerics (N2/N7) sampled *nondegenerate* pencil-generic
     seeds; no experiment yet probes the bare rank target at an infeasible habitat graph, or
     extension from a degenerate target-rank `G′`-seed — (K-bare) is *less* evidenced than (K).
  Pinned carried form (antecedent discipline as `hK` — everything the assembly has at the call
  site, including `¬Feasible`, whose forced `≥ 4`-hub-neighbourhood structure the discharge may
  exploit; note the implication may *ignore* the given `G′`-witness, so this is the
  weakest-precondition shape — its truth follows from the bare conjecture at `G` even if naive
  extension fails):
  ```lean
  hbareSplit : ∀ (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β), G.Simple → 5 ≤ V(G).ncard →
    G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) →
    G.degree v = 2 → eₐ ≠ e_b → G.IsLink eₐ v a → G.IsLink e_b v b →
    (¬ G.PencilHub a ∨ ¬ G.PencilHub b) → e₀ ∉ E(G) →
    ¬ PencilNondegFeasible K G →
    HasPencilRealization K 3 (G.splitOff v a b e₀) →
    HasPencilRealization K 3 G
  ```
  The feasible case never consults `hbareSplit` (it rides forgetful ∘ generic) and the
  infeasible case never consults `hK` — the two carried kernels partition cleanly by
  feasibility. **User adjudication (2026-07-30, "Numerics gate first"): run the numerics-first
  (K-bare) probe before deciding among carry/motive-change/research** — settled by the probe
  below, which returned SUPPORTED.

  **(K-bare) numerics gate PASSED 2026-07-30** (scripts
  `notes/scripts/kbare/{kbare_common,gate1,gate2,stress_extra}.py`; independent of the (K) escape
  probes, per residue (ii)'s own numerics-first plan above). Both planned gates SUPPORTED, with
  *certified* (not sampled-only) bare-target attainment at every infeasible gadget tried:
  `theta(6,6,6)` + center hub `105/105` target, its safe split `100/100`, `spider(5,5,5)` `90/90`
  (`= 5|E|`, full row independence), a 17-vertex gadget `95/95`, and a `theta`-family sweep
  `120/110/115` — and extension from a *forced-degenerate* seed works in **both** deficiency
  branches (`splitOff_deficiency_le/ge`'s `def(G′) ∈ {def(G), def(G)−1}` dichotomy). One
  discharge-level caveat recorded: in the def-*equal* branch the re-inserted point must avoid
  the deleted hinge's line (an in-stratum genericity side condition the eventual discharge needs
  to track — generic placement works from every seed tried). This fills the evidence-gap flagged
  at item 4 above (the 2026-07-23 rank tests (R2) sampled zero infeasible-*habitat* graphs);
  (K-bare) is now evidenced at parity with (K). *(Scope-corrected by the extension-route recon
  below, same day: every gadget of this gate is count-INDEPENDENT — corank 0 at `G`'s target,
  ≤ 1 at `G′`'s — so the gate never sampled the stressed stratum; the dependent (corank-2)
  stratum is nonempty inside the (K-bare) habitat and was then probed there too (`danger.py`),
  same qualitative picture — see §"(K-bare) extension-route recon".)* **Consequence, per the user's same-day
  "Numerics gate first" adjudication and post-gate "Continue: full L7c" confirmation: route (a)
  — carry `hbareSplit` as pinned — is GO.** L7c-5/6 may proceed carrying it exactly as pinned
  above; the (K-bare) *research* (closing `hbareSplit` itself, as opposed to carrying it) is not
  commissioned by this gate and stays open alongside (K)'s own research (routes 1–2 below).
- **Residue (iii) — non-simple bare half: PINNED 2026-07-30 as leaf L7c-1 below.** `¬Simple`
  habitat `G` is excluded by `hnoRigid` (a parallel pair is proper rigid at `|V| ≥ 3`); the
  externalization IS needed (the assembly needs `G.Simple` for L7b's instance argument and the
  feasible-case forgetful route, not just as the generic conjunct's antecedent), and it is a
  mechanical extraction: `simple_of_isMinimalKDof_of_noRigid` (`ReducibleVertex.lean:698`) uses
  its minimality hypothesis ONLY through `loopless_of_isMinimalKDof` (verified against the body
  this recon) — replace it with a `[G.Loopless]` instance.
- **Residue (iv) — fresh-`e₀` plumbing: CLOSED 2026-07-30.** The producer takes `hfresh : ∃ e₀,
  e₀ ∉ E(G)` exactly as the panel Case-III producer does (`case_III_realization_all_k`), and the
  successor wrapper threads a `∀`-form supply hypothesis exactly as the panel spine's `hfresh`
  carry. The follow-up counting discharge landed the same day:
  `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two` (`Escape.lean`) proves the `∀`-form supply
  from `bodyBarDim 3 * (|α| − 1) < |β|`, following `Graph.freshEdgeSupply_of_card_lt`'s skeleton
  (`Theorem55.lean:2858`) with `edgeBound_of_noRigid_of_degree_two` in place of the minimality edge
  bound; `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` is the consumer-facing headline.

**The L7c hsplit assembly — settled decomposition (2026-07-30 assembly recon).** Ordered
buildable leaves; every named call is landed unless flagged. `[Inhabited α]` enters at
L7c-5/L7c-6 only — their *statements* carry `hK`, whose type reads `pencilRow … G.endsOf …`
(the flagged correction above); L7c-1…4 need none of it.

- **L7c-1 — ALREADY DISCHARGED, no new Lean (caught by the 2026-07-30 build dispatch).**
  externalized habitat simplicity (residue (iii)) was pinned as a new `simple_of_noRigid`
  (`[G.Loopless]` instance, `[DecidableEq β]`, verbatim body of `simple_of_isMinimalKDof_of_
  noRigid` with `loopless_of_isMinimalKDof hG` replaced). The build dispatch diffed this pin
  against `simple_of_loopless_of_noRigid` (`ReducibleVertex.lean:767`, **W3-L2a, landed
  2026-07-24 — minted for exactly this arm**, its own docstring says so: "the split arm's
  habitat `G` is already provably simple … minimality-free, minted for this arm") and found the
  two bodies **byte-identical** (only the `Loopless` argument's binder — instance vs. explicit —
  and the vestigial `[DecidableEq β]`, both artifacts of mechanically copying
  `simple_of_isMinimalKDof_of_noRigid`'s typeclass list rather than genuine proof needs, differ).
  `simple_of_loopless_of_noRigid`'s own `hloop : G.Loopless` explicit binder is in fact the
  *better* fit for L7c-5's pinned signature (which also carries `hloop` explicit, not an
  instance) — no instance-conversion dance needed at the call site: `simple_of_loopless_of_
  noRigid (n := 3) hD hV hloop hnoRigid`. **No `simple_of_noRigid` lands; L7c-1 is closed by
  reuse.**
- **L7c-2 LANDED 2026-07-30** (`ForestSurgery/Reduction.lean`,
  `exists_splitOff_data_of_degree_eq_two_of_twoEdgeConnected`) — the 2EC-sourced split-data
  extractor. **Plan-pointer correction (caught this recon):** the L6a-transfer entry's "`hab`
  free at the L7 call site via `exists_splitOff_data_of_degree_eq_two`" does not hold as-is —
  that lemma (`ForestSurgery/Reduction.lean:326`) requires `hG0 : G.IsKDof n 0`, which the (b′)
  habitat lacks. Its ONLY use of `hG0` is the crossing bound `two_le_crossingEdges_of_isKDof_
  zero`; re-sourced from the habitat's own `h2ec : G.TwoEdgeConnected` at the singleton cut `{v}`
  (the same 2EC-re-sourcing move as the landed `exists_adjacent_degree_two_pair_of_edgeBound`):
  mechanical copy of the original body with the crossing-edges step replaced by
  `h2ec {v} ⟨v, Set.mem_singleton v⟩ hssub` + `cutEdges_eq_crossingEdges_cutLabeling` +
  `crossingEdges_cutLabeling_singleton_subset`. Landed verbatim to the pin (no `n` parameter at
  all — the statement is purely graph-theoretic). Home `ForestSurgery/Reduction.lean` beside
  the original. Gates + axioms clean (`propext`/`Classical.choice`/`Quot.sound`; full
  `lake build` + `lake lint` both clean).
- **L7c-3 LANDED 2026-07-30** (`Molecule/Pencil/Base.lean`, new file) — the `C₃` base leaf
  (residue (i)):
  ```lean
  theorem pencilPair_of_habitat_ncard_eq_three [Finite α] [Finite β] {G : Graph α β}
      (hloop : G.Loopless) (hV : V(G).ncard = 3) (h2ec : G.TwoEdgeConnected)
      (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) : PencilPair K 3 G
  ```
  Identification: Simple (L7c-1) + `|V| = 3` caps every degree at `2`; 2EC forces degree `≥ 2`
  (`two_le_degree_of_twoEdgeConnected`) ⟹ 2-regular ⟹ the spanning `C₃`. Landed via a direct
  contradiction argument (no third neighbour exists to absorb a second edge at any vertex),
  slightly leaner than a full edge/degree classification. Witness (direct, caliber
  `exists_isNondegPencilRealization_parallel_pair`): three of the four `K⁴` standard basis
  vectors as points; hinges = the three side-line wedges; all three panels =
  the triangle's plane (the R1 collapse — two distinct lines through a point span their plane),
  so `normal` is constant (the fourth basis vector); hub-free (`PencilHub` needs degree `≥ 3`)
  makes conjunct 3 trivial and conjunct 4 = the 3-point LI (a sub-family of the basis). Rank: the
  three side-line extensors are LI — proved via a new reusable "join-detector" technique
  (FRICTION [idiom], join each wedge with the complementary unused basis pair; every other wedge
  then repeats a vector against that complement and vanishes) rather than a hand-rolled
  exterior-power coordinate readout — ⟹ `theorem_55_cycle` at `m = 3` ⟹ bridge B1
  (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`, the base arm's own
  single-edge rank thread, `Pencil/Pair.lean:1252ff`) ⟹ rank `= 6(|V|−1)`, which is the target
  since `def = 0` (`isKDof_zero_of_cycle`). Bare half = `hasPencilRealization_of_generic`.
- **L7c-4 LANDED 2026-07-30** (`Molecule/Pencil/Base.lean`,
  `pencilPair_of_habitat_ncard_eq_four`, matching the pinned signature below verbatim) — the `C₄`
  base leaf, same template at `m = 4`. **Not the same proof as L7c-3, on inspection (2026-07-30
  build dispatch):** `C₃`'s witness rides a degeneracy
  specific to *three* points always being coplanar (a shared constant panel normal); at `C₄` no
  such collapse is forced, so each vertex needs its *own* panel normal (the "opposite" basis
  vector, index `i + 2`, simultaneously orthogonal to its own point and both neighbours' — still
  an explicit standard-basis construction, not a generic/numerics route), and the degree bound
  additionally needs the triangle-freeness exclusion below (not just Simple + 2EC). The
  join-detector technique for the wedge-family independence (now landed at L7c-3, FRICTION
  [idiom]) generalizes directly to the 4-term case.
  ```lean
  theorem pencilPair_of_habitat_ncard_eq_four [Finite α] [Finite β] {G : Graph α β}
      (hloop : G.Loopless) (hV : V(G).ncard = 4) (h2ec : G.TwoEdgeConnected)
      (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3) : PencilPair K 3 G
  ```
  Identification: triangle-free (`triangle_isProperRigidSubgraph` at `4 ≤ |V|`), so a degree-3
  vertex is impossible (its three neighbours exhaust `V`, and any second edge at a neighbour
  closes a triangle) ⟹ 2-regular ⟹ the spanning `C₄`. Witness: four generic points, side-line
  hinges, per-vertex panel = the span of its two adjacent sides (no global collapse at `C₄`);
  four LI side extensors in the 6-dim `Λ²K⁴` ⟹ `theorem_55_cycle` (`m = 4`) ⟹ B1 ⟹ target
  (`def = 0` again by `isKDof_zero_of_cycle`).
- **L7c-5 (S2, buildable now GIVEN the (K-bare) adjudication)** — the `5 ≤ |V|` hsplit producer,
  carrying the two kernels:
  ```lean
  theorem pencilPair_of_splitOff_of_habitat [Inhabited α] [Finite α] [Finite β] [DecidableEq β]
      [Infinite K] {G : Graph α β}
      (hloop : G.Loopless) (hV : 5 ≤ V(G).ncard) (h2ec : G.TwoEdgeConnected)
      (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G 3)
      (hdeg2 : ∃ v ∈ V(G), G.degree v = 2)
      (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
      (hK : <the pinned hK above, [Inhabited α] in scope>)
      (hbareSplit : <the pinned (K-bare) form above>)
      (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
        PencilPair K 3 G') : PencilPair K 3 G
  ```
  Route: Simple := L7c-1; safe pair `(v, a₀)` (both degree 2, adjacent) :=
  `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`; split data at `v` := L7c-2 (`b₀`
  from `3 ≤ |V|`); align: the `v`–`a₀` edge is `eₐ` or `e_b` by the extractor's closure clause,
  and its far endpoint is `a₀` by link-uniqueness (loopless makes `a₀ ≠ v`), so wlog `a = a₀`
  and `hsafe := Or.inl` (degree-2 `a₀` is no hub). Then `by_cases hfeas : PencilNondegFeasible
  K G`: **feasible** — L7a ⟹ `G′`-generic; instantiate `hK` (its output IS L7b's `hEsc`, shapes
  verified identical); `hcard` on all of `α` from `hfeas` + the landed `≤ 3` producer with L7a's
  own off-`V(G)` empty-set plumbing (`Escape.lean:87–96`); `htf` on `G` inline from `hnoRigid` +
  `triangle_isProperRigidSubgraph` (`4 ≤ |V|`); L7b ⟹ `HasGenericPencilRealization K 3 G`; pair
  = `⟨fun _ _ => hgen, hasPencilRealization_of_generic hgen⟩`. **Infeasible** — generic conjunct
  `fun _ hf => absurd hf hfeas`; bare = `hbareSplit` instantiated at `(hIH G′ …).2`.
- **L7c-6 (S1, buildable now GIVEN L7c-1…5)** — the successor wrapper (the
  `pencil_conjecture_of_arms_pair` successor): discharges the `hsplit` slot by the
  `|V| ∈ {3, 4}` vs `≥ 5` dispatch (L7c-3/L7c-4/L7c-5), taking `hcontract`, the ∀-form `hK`,
  `hbareSplit`, and a `∀`-form fresh-edge supply (`hfresh : ∀ G' : Graph α β, G'.Loopless →
  (∀ H, ¬ H.IsProperRigidSubgraph G' 3) → (∃ v ∈ V(G'), G'.degree v = 2) → 3 ≤ V(G').ncard →
  ∃ e₀, e₀ ∉ E(G')` — the exact antecedents the counting discharge needs) as hypotheses, with
  `[Inhabited α]` (subsuming the current `[Nonempty α]`). The supply's counting discharge
  (residue (iv) route) is a follow-up S1, not part of this commit — CLOSED same day, see
  residue (iv) above.

**Remaining-open after L7c (the `hsplit` bookkeeping, Q4 of the assembly recon).** Once
L7c-1…6 land, `hsplit` is discharged and the successor carries exactly: `hcontract` (W4),
`hK` ((K) — research, routes 1–2 below), `hbareSplit` ((K-bare) — user adjudication above,
then research), and `hfresh` (mechanical counting, S1 — CLOSED same day, see residue (iv)
above). L8 is DISSOLVED as a standalone leaf (see its ruling in §"W5 leaf decomposition"). The
earlier expectation "L7c carries `hK` alone" is thereby revised: `hK` alone covers only the
feasible branch.

**Route options for kernel (K) — user adjudication.** Numerics-first per instance
(the pinned method) *validates* (K) but cannot *close* the `∀ G` Lean leaf. Three routes:

1. **Localization / reduction to a local model** (recommended to attempt first;
   effort: medium-high, 1 research recon + 3–6 build leaves *if* it holds). Prove (K) by
   showing that at a *generic* seed the escape `E` depends only on a bounded neighbourhood
   of the chain `b–v–a–c` — degenerate the far graph (a "coning"/specialisation seed, à la
   KT's own Claim-6.4 specialisation `Π₁(v):=Π₂(v*)`) so the stress localises and `E`
   reduces to a computable local bracket, manifestly nonzero at a canonical local seed.
   *Risk:* the stress is supported on the (possibly global) fundamental circuit of `ab`;
   localisation needs a "generic-seed stress-localisation" lemma that is itself unproven.
   Next step: a numerical test of whether `E`'s (non)vanishing is local (fix identical
   local chain data across two different global habitats, compare) before committing.
   **Gate FIRED 2026-07-30 — locality REFUTED, route 1 is NO-GO** (the risk confirmed at
   its worst: the stress is supported on *every* edge, and the escape's zero locus moves
   with the far graph at identical local data); see §"(K) route-1 gate" below.

2. **Reuse the landed panel-case span machinery** (effort: medium, 2–4 leaves *if*
   applicable). The panel-case Claim 6.12 (four-point span = 6) is formalised as
   `exists_complementIso_ne_zero_of_homogeneousIncidence` (+`_gen`, `RigidityMatrix/Claim612.lean`).
   The pencil case shrinks the span to 5 but the *escape* only needs `r ∉ Λ²Π̂(a)^⊥`
   (weaker than span-6). Investigate whether a pencil-restricted variant of that landed
   argument certifies `r` avoids the 3-dim `Λ²Π̂(a)^⊥` — i.e. whether the pinned-pencil
   span computation can be run through the same `complementIso` non-vanishing device.
   *Risk:* the four-point argument's independence input (Lemma 2.1) is exactly what the
   pencil pinning breaks (dim 5 < 6), so a genuinely new non-vanishing input is needed.
   **Assessed 2026-07-30 (route-1 gate recon) — risk CONFIRMED against the landed body;
   partial reuse survives**: the span-side computation reduces the disjunction escape to a
   single proportionality `r ∥ w` with `w` the locally-computable generator of the 1-dim
   `S^⊥`, yielding the *variability-lever* reduction of (K) to stress non-constancy —
   see §"(K) route-1 gate" below.

3. **Carry (K) as a project-level `have`-hypothesis indefinitely** (effort: 0 now; defers
   the research). **ADJUDICATED 2026-07-30 (session check-in) and re-shaped same day by the
   L7b route recon:** land L7a (LANDED) + the re-pinned L7b + the L7c assembly with `hK`
   explicit — the same posture L6a-safe-exists's rigid `k=0` half rode under before its
   route recon closed it (this pass, same session). This completes the *entire* pencil
   reduction modulo the single remaining named hypothesis (K) (plus the L7c residues
   (i)–(iv) above, all tracked), turning PENCIL into "conditional on one crisp
   `∃`-statement, with decisive exact-ℚ evidence and 0 counterexamples". Legitimate as a
   milestone; the conjecture is then *proven modulo (K)*, and (K) can be attacked
   (routes 1–2, both factoring through `hK`'s discharge) or adjudicated later.

**Recommendation** (route 3 adjudicated; `escapePoly` deleted by the 2026-07-30 re-pin; L7b
LANDED; L7c decomposed by the 2026-07-30 assembly recon — the block above is canonical). Build
L7c-1 + L7c-2 (one S1 plumbing commit), then L7c-3/L7c-4 (the base leaves), then — once the
(K-bare) adjudication returns — L7c-5 and L7c-6. *(All of the above landed 2026-07-30.)* The
route-1 (localisation) research recon FIRED 2026-07-30 and its local-vs-global gate **refuted
locality — route 1 is closed NO-GO**; the surviving (K) attack is the variability-lever
reduction through route 2's span-side reuse (§"(K) route-1 gate" below), whose open core —
uniform stress non-constancy — is the recommended object of the next (K) recon. The (K-bare)
research recon (numerics-first, residue (ii) above) can run independently. Do **not** guess
that (K) is provable by (6.44) — that is refuted; do **not** re-attempt route-1 localisation.

### (K) route-1 gate (2026-07-30): the local-vs-global test — locality REFUTED, NO-GO

Commissioned per route 1's own pinned first gate above ("a numerical test of whether `E`'s
(non)vanishing is local … before committing"). Question: at a generic seed, does the escape
`E = r ⬝ (b̂∧ĉ)` depend only on a bounded neighbourhood of the chain `b–v–a–c`, so that
degenerating/coning the far graph localises the stress? Method: exact-ℚ, same model as N7
(scripts `notes/scripts/escape/localtest.py` + `localtest_zeros.py`; reproduce
`python3 notes/scripts/escape/localtest_zeros.py`). Every reported configuration validated rank = target,
nullity 1, (6.44), `r ⊥ â∧b̂`, `r ⊥ â∧ĉ`, `r ≠ 0`.

**Setup (N8).** Fix one **radius-1 local block**, identical rationals across all runs:
`pt(b)`, `Π(b)`, `pt(c)`, `Π(c)`, the two non-`a` in-plane neighbours of each of `b` and `c`,
and `pt(a)(t) = p₀ + t·dir` on the meet line `Π(b) ∩ Π(c)`. Vary ONLY the far graph:
within-habitat far resampling (H1 = dbl-subdiv K4, far seeds 1–3) and cross-habitat
(H4 = dbl-subdiv (K5 − matching), chain-end degrees (3,3) matching H1's, so the radius-1
block is habitat-portable verbatim). Repeated with a second local block (seed 77) — same
picture throughout.

**Results (exact-ℚ):**

1. **The stress is supported on every edge** — 17/17 (H1) and 23/23 (H4) edge blocks carry
   nonzero stress in every valid run, both local blocks. In these tight habitats
   (`5|E′| = 6(|V′|−1) + 1`, no proper rigid subgraph upstream) the fundamental circuit of
   `ab` is the entire edge set: there is no proper subgraph to localise the stress onto.
   The route's named risk, confirmed at its worst.
2. **`[r]` moves with far data.** At the same `t` and identical local block, the projective
   direction of the escape vector `r` differs across all three H1 far seeds and both H4 far
   seeds (5 pairwise-distinct directions).
3. **The zero locus of `E(t)` moves — including within one habitat.** Same local block,
   integer sweep `t ∈ [−6,6]` + bisection (bracket width ~4·10⁻⁹, endpoints valid
   rank-target/nullity-1 realizations): H1 far1 — **no zero** (constant sign); H1 far2 —
   zeros at `t* ≈ −1.7529130, −0.0048921`; H4 far1 — zeros at `t* ≈ −3.0835821, −2.7321426`.
   Identical local chain data is compatible with both vanishing and non-vanishing of the
   escape, decided by the far graph alone.
4. **Sensitivity radius ≥ 4.** Moving a SINGLE far interior vertex (graph distance 4 from
   the chain, staying inside its hub's plane — an in-stratum move) changes `[r]` and
   multiplies the normalized escape `Ẽ` (scale fixed by `r`'s first nonzero coordinate) by a
   factor non-constant in `t` (0.7419 at `t = 0`, 5.3133 at `t = 1`) — so the zero set of
   `t ↦ E(t)` itself changes under one distance-4 vertex move. No radius-≤ 3 neighbourhood
   determines the escape's (non)vanishing. (All cross-run comparisons here use scale-free
   invariants — projective `[r]`, zero loci, normalized ratios; raw signs of `E` across
   *different* runs are λ-scale artifacts and were not used.)

**Widened-habitat pointer (2026-08-02).** Finding 1's *explanation* ("no proper
subgraph to localise the stress onto") is a `hnoRigid` consequence, but the gate's
NO-GO verdict does not depend on it — see `notes/Pencil-informal.md` §"widened
kernels (routes 1/3)" *Step 1* (row K4).

**Verdict: route 1 is NO-GO.** The escape's (non)vanishing at a generic seed is a genuinely
global function of the seed — not a function of any bounded chain neighbourhood — because
the corank-1 stress it reads is globally supported and globally coupled. The
coning/specialization variant loses its premise too: localising the stress means shrinking
the realized circuit, i.e. forcing a proper row subset dependent — a rank-threatening
degeneration with no landed control, and the "generic-seed stress-localisation" lemma the
route needed is now *known false at generic seeds* (support is the whole edge set there).
Do not re-attempt.

**Route-2 assessment (against its named risk, grounded in the landed body).** The landed
device's engine is `case_III_claim612_gen` (`RigidityMatrix/Claim612.lean:1339`; the
consumer-facing `exists_complementIso_ne_zero_of_homogeneousIncidence` at `:1382` adds only
the line-data dispatch): its **sole non-vanishing input is `hr : r ≠ 0`** plus a
linearly-independent 4-family `pbar` whose pairwise joins span all of `Λ²K⁴`
(`span_omitTwoExtensor_eq_top`, Lemma 2.1). The panel certificate is exactly "the candidate
spaces span everything, so `r ≠ 0` suffices". Under the pencil pin the available candidate
space is `S = Λ²Π̂(a) + pencil(b) + pencil(c)` with `dim S = 5` (structural, N7), so
`r ∈ S^⊥ ∖ {0}` is uncontradicted and `r ≠ 0` concludes nothing: **the named risk is
CONFIRMED** — no pencil-restricted rerun of the landed argument closes (K); a genuinely new
non-vanishing input is required. What *does* survive as reuse is the span-side reduction:
`S^⊥` is 1-dimensional with generator `w` computable from the local block alone
(`pencil(b)` is determined by `(pt(b), Π(b))`, `pencil(c)` by `(pt(c), Π(c))`, `Λ²Π̂(a)` by
the three chain points), and the KT-faithful **disjunction** escape (one of `M₁/M₂/M₃`
works, KT Claim 6.12 p. 690 — which implies `hK`'s rank increment, and `hK` is
candidate-agnostic) fails at a seed **iff `r ∥ w`**.

**The variability lever (new; what a route-2/(K) recon needs to settle).** Since `w` is
fixed on the fiber of seeds over a fixed local block, any two seeds in that fiber with
`r₁, r₂ ≠ 0` and `[r₁] ≠ [r₂]` cannot both satisfy `r ∥ w` — at least one certifies the
disjunction escape, hence the `hK` increment. **(K) therefore reduces to stress
non-constancy**: *over some chart-generic local block (where `dim S = 5`), the stress's
`a`-block direction `[r]` takes at least two values as the far data varies.* Exactly this
non-constancy is what N8 witnesses in every habitat and under a single distance-4 vertex
move (findings 2/4). Two cautions pinned now: the reduction needs the **disjunction** form,
not `M₁`-alone (two distinct `[r]` can both lie on the 3-dim
`{r ⬝ (b̂∧ĉ) = 0} ∩ pencil(a)^⊥`; only the 1-dim `S^⊥` is excluded by non-constancy), and
proving non-constancy uniformly in `G` is still open — it is a strictly weaker target than
any pointwise escape certificate (it asks only that `r` *move* as one far vertex moves, not
where it lands), plausibly a derivative/transversality statement about the corank-1 stress,
but the `∀ G` uniformity remains the crux. That statement is the recommended object of the
next (K) recon — *fired same day, verdict PARTIAL, next subsection.*

**(K-tight) re-pin pointer (2026-08-02).** The lever's `w` is now *identified*: the
carrier-corrected criterion (KT pp. 684–691 re-derived against the carrier) puts combined
failure at `r ∥ ★C(Π(b) ∩ Π(c))` — the meet line's starred extensor, local-block data —
and the `E = r ⬝ (b̂∧ĉ)` M₁ test used by this gate's scripts certifies only the
*panel-model* escape, which the carrier cannot realize. The gate's verdicts (locality
refuted, non-constancy as the lever) are unaffected. `notes/Pencil-informal.md`
§(K-tight).

### (K) non-constancy recon (2026-07-30): corank stratification — PARTIAL, kernel narrowed to (K-tight)

Commissioned as the route-1 gate's follow-up: *does uniform stress non-constancy have a
provable route?* Answer: **not within landed machinery — but the question itself was
mis-scoped**, and this recon replaces it with a corank stratification that (a) corrects a
factual error in the N7 record, (b) discharges the escape *automatically* on a whole
stratum modulo one new seed-quality obligation, and (c) confines the genuinely hard kernel
to the tight class. Methods: definition bodies re-read (`IsProperRigidSubgraph`,
`Deficiency.lean:483` — properness is **vertex**-properness `V(H) ⊂ V(G)`;
`HasGenericPencilRealization`, `Motive.lean:140`), a boundary-load derivation (below,
flagged where not yet KT-pinned), and exact-ℚ experiments N9a/N9b
(`notes/scripts/escape/n9.py`; reproduce `python3 notes/scripts/escape/n9.py`).

**1. Corank stratification (correction + witnesses).** Write `index(G) := 5|E| −
6(|V|−1)`. The split arithmetic gives `index(G′) = index(G) + 1` always; in the `k = 0`
branch (`G` rigid) `G′` is rigid too, so its corank at a target-rank seed is
`index(G) + 1` — **corank 1 holds exactly on the tight stratum `index(G) = 0`**. The hK
class genuinely contains `index(G) ≥ 1`: `C₅` (index 1, `G′ = C₄` corank 2 — cycles later
turn out non-critical, see item 4) and, non-trivially, **θ(4,4,3)** (10 vertices, 11
edges, index 1, both chain ends degree-3 hubs): N9a confirms it is rigid (54/54 generic
AND pencil-generic), has no vertex-proper rigid subgraph (its cycles are `C₈`/`C₇`, both
flexible; all proper subgraphs are unions of subpaths under the count), and its split at
the short path's interior gives `G′` with **corank exactly 2** at pencil-generic
target-rank seeds (48/48, 3/3 samples). `index(G) ≤ 4` on the whole habitat class
(`edgeBound_of_noRigid_of_degree_two`), so the stratification is finite: `index ∈
{0,…,4}`.

**2. The general escape condition is about the stress *image* `R_a`, and `dim R_a ≥ 2` is
automatic escape.** Derived this pass by a boundary-load calculus (flag: my derivation,
numerically consistent, NOT yet re-pinned against KT pp. 684–691's general
`|B′ ∩ ãb| < 5` machinery — that re-pin is the first task of any formalization): a
dependency of the extended `G`-rows involving the two new blocks corresponds to a vector
`u ∈ C(va)^⊥ ∩ C(vb)^⊥` realizable as an antisymmetric boundary load `(−u @ a, +u @ b)`
of the shared (`G−v`) rows; with the candidate construction `hinge(vb) := q(ab)`,
`hinge(va) := L` swept, such `u` must lie in `R_a := {a-blocks of the `ab`-fiber parts of
`G′`-stresses}`, and the extension attains `G`-target iff `R_a ⊄ (span C(L))^⊥` for some
candidate — over all three candidates, **failure ⟺ `R_a ⊆ S^⊥`**. Since `dim S^⊥ = 1`
(both-ends-hubs, chart-generic), `dim R_a ≥ 2` makes failure *impossible*. N9a: at every
θ-split seed, `dim R_a = 2`, `dim S = 5`, `R_a ⊄ S^⊥`, and every generic re-insertion of
`v` attained the `G`-target 54/54 (6/6 extension samples).

**3. `dim R_a = corank − s₀`, and the habitat kills `s₀` combinatorially.** The a-block
map on the stress space has kernel = the pure shared-row stresses (`s₀`-dim), because the
`ab`-fiber's 5 rows biject combinations to `C(ab)^⊥` — so `dim R_a = corank − s₀`. A
count-matroid circuit supported inside `G−v` induces a rigid subgraph on `V(C) ⊆
V(G)∖{v} ⊊ V(G)` (`circuit_induces_isRigidSubgraph`, landed) — **excluded by
`hnoRigid`**. So `s₀ = 0` at count level, and `s₀ = 0` holds at any seed where the shared
subrank is generic. Consequence: **on `index(G) ≥ 1` strata the escape is automatic at
shared-subrank-generic seeds** — the escape kernel is *replaced* by a seed-quality
obligation, **(K-shared)**: `∃` a `G′`-chart seed with `G′`-rows at target rank AND the
count-independent shared family fully independent. Engine-composable (two LI conditions,
the engine's native food); the somewhere-witness for the shared half is related to the
IH at `G−v` (which has `< |V|` vertices, so `hIH` applies!) but is NOT free: the IH's
generic half is feasibility-conditioned, and a `G−v` witness needs the `a ∈ Π(b)`-star
incidence added before it lives on `G′`'s chart. Promising, unfinished — pinned as the
`index ≥ 1` branch's remaining obligation, strictly better-shaped than an escape
certificate (monotone row-independence of a count-independent family, no stress, no
deficiency bookkeeping).

**4. The hard kernel is (K-tight), and its habitats are 2-connected.** Non-hub chain ends
give `dim S = 6` (`r ≠ 0` suffices — the landed panel argument's shape closes pointwise),
so the critical class is: **tight (`index 0`), both chain ends hubs** — exactly the N7
double-subdivision family, unknowingly chosen. There `corank = 1`, `R_a = ⟨r⟩`, and
failure ⟺ `r ∥ w` — the variability lever's proper scope. New structural fact: a
lever-critical habitat has **no cut vertex** — blocks satisfy `index(G) = Σ index(Bᵢ)`;
a block of index ≥ 1 contains a circuit (rigid, vertex-proper — excluded), and an
index-0 block is either count-independent (then rigid, vertex-proper — excluded) or
contains a circuit (excluded); so all blocks would need index ≤ −1, contradicting the sum
`= 0` unless `G` is a single block. This kills the one *identified* mechanism for
`[r]`-constancy (a stress living autonomously on one side of a cut vertex, where far
moves provably cannot touch it). **N9b (canonical-move completeness):** in H1, moving
ANY single far movable vertex (all six, in-plane where constrained) changes `[r]` — the
non-constancy is witnessed by every available move, not a lucky one.

**5. Provable route for (K-tight)? NO — each candidate mechanism hits the same missing
technology.** (a) *Canonical-move derivative argument*: numerically complete (N9b), but a
Lean proof must express `[r]` as a rational function of the seed and show a derivative is
nonzero — this is precisely the corank-1-stress-by-cofactors infrastructure the L7b build
dispatch REFUTED as in-tree-absent (chosen-minor dependence, multi-commit new infra), now
needed inside the discharge rather than the statement. (b) *Degeneration/limits*: needs
stress control at degenerate seeds — the localization machinery route 1 was shown to
lack. (c) *Via the engine*: circular — the somewhere-witness for "`[r] ≠ [r₀]`" IS
non-constancy. Verdict: **PARTIAL** — the reduction narrowed the kernel's habitat class
(tight, both ends hubs, 2-connected) and weakened its target (`r` must *move*, not land
anywhere specific), with decisive numerics and zero counterexamples, but no landed-brick
route closes it. The single identified enabling technology for ANY further attack is the
**stress-as-chart-rational-function infrastructure** (corank-1 cofactor gadget over the
chart ring + subrank-genericity bookkeeping) — it would serve mechanisms (a) and (b)
and the §2 failure-condition formalization alike.

**Adjudication options (user). ADJUDICATED (2026-07-30 session check-in, verbatim):
"C: literature hunt + A"** — i.e. option A (keep carrying `hK` as pinned) AND option C
(run the cheap read-only literature hunt) both proceed; option B (commission the
stress-function infrastructure) is NOT commissioned now. The literature hunt itself is
the coordinator's next dispatch, not run by this pass.

- **A — keep carrying `hK` as pinned** (recommended; consistent with the standing route-3
  adjudication). Zero effort now. The stratification above becomes the discharge's
  roadmap when (K) research resumes: `index ≥ 1` → automatic-escape branch modulo
  (K-shared); `index 0` → (K-tight). `hK`'s statement needs no change (its ∃-LI shape is
  agnostic to all of this — the pin held up well).
- **B — commission the stress-function infrastructure** (the only identified path to
  closing (K) in-tree): 1 design pass to pin the cofactor gadget + chart-ring plumbing,
  then multi-commit build, then the (K-tight) non-constancy argument on top — research-
  scale, success not assured (the final derivative-nonvanishing step is itself unproven
  mathematics; numerics say true, nothing says provable-cheaply).
- **C — literature hunt** (stress non-constancy / stress matrices of count-tight
  body-hinge graphs): low odds — the stratum is novel (phase-open finding), and the
  question mixes pencil-chart geometry with matroid tightness in a form unlikely to be
  in print. Cheap to run alongside A.

**Widened-habitat pointer (2026-08-02).** If W4 routes 1/3 are adjudicated, this
section's stratification is consumed on a habitat where `hnoRigid` is FALSE. What
survives, what breaks (item 3's `s₀ = 0` and item 4's proof, not its conclusion),
the corank identity `dim R_a = 5 + def(G′) − def(G−v)`, the reduction of item 1's
`index ≤ 4` to a cheap leaf plus (E-loc), and a caveat against item 2's failure
criterion: `notes/Pencil-informal.md` §"widened kernels (routes 1/3)".

**(K-tight) re-pin pointer (2026-08-02, later).** Item 2's owed KT pp. 684–691 re-pin is
**done, against the carrier** — `notes/Pencil-informal.md` §(K-tight). The §2 criterion is
corrected there (three panel leaks: M₁'s `Λ²Π̂(a)` is carrier-unrealizable; M₂/M₃'s spans
are the *full* `Λ²Π̂(b)`/`Λ²Π̂(c)`, not the pencils; the obstruction space is
`U = R_a ⊕ ⟨w⟩`, not `R_a`), item 4's "non-hub ends: `r ≠ 0` suffices" is corrected (a
1-dim bad set `⟨★C_ab⟩` remains per route), and (K-shared) is absorbed into
`dim R_a ≥ 1`. The Step-5 caveat's seed-442 mispredict dissolved: a placement-sampler
artifact, not a criterion failure — no genuine escape failure exists in the phase's
corrected numerics (`notes/scripts/w4/repin.py`).

**(K-pitch) development pointer (2026-08-04, two dispatches).** Item 5's enabling-technology
assessment is **partially superseded**: the pitch polynomial (the null-wrench sufficient
certificate) needs NO stress-as-chart-rational-function infrastructure — it transfers
stress-free to the motion side of `G − v − a` (the chain ends' relative twist system; a
kernel computation, no cofactors), and **closes in bracket-monomial form** at splits with a
parallel length-3 companion chain (θ(3,3,6), a (K-res) hard-stratum member). The same day's
second dispatch attacked the uniform gap: the **naive collinear-collapse leading term is
REFUTED as a chart move** (its panel-resident repair forces the target-rank-deficient
all-coplanar locus), corrected to the **slide-in degeneration** — rank-persistent, hence
motion-continuous, with a `G°`-local limit system that stays pitched on simple hub
multigraphs and goes null exactly on parallel-edge ones (where the companion forms take
over); and the companion mechanism extends to length-4 companions via the **Λ-compression**
(all far data through one covector; `Q(z) = Φ_loc(λ)`). The uniform gaps are now
**(K-Λ)/(K-slide)**, both `G°`-level and strictly more local than (K-wit).
`notes/Pencil-informal.md` §(K-pitch) Steps 5b/6; exact-ℚ `notes/scripts/w4/pitch.py`.

**(K-slide) transfer-theorem pointer (2026-08-04, third dispatch).** The slide-in is now a
**proof device**, not a heuristic: the slide-transfer theorem (S1) — slide = chart automorphism
at `ε ≠ 0`, row family polynomial through `ε = 0` — makes one exact limit witness prove the
pitch `≢ 0` on the habitat's chart, with the rank-persistence proviso *dissolved* (now an
a-posteriori corollary). Witnessed and closed: the `K4`/`W4` double-subdivision control
habitats at **every** split, `K5−2e`, prism+diagonal, mixed-lengths, and hub-hub-edge members
(23/23 limit witnesses; both untested Step-6(e) flanks now inside the framework). Parallel
`G°`-edges are **structurally obstructed at order 0** (repeated-line cycle stress, proven for
the full support; hub-concentrated circuit exhibited for the reduced one) — the sharpest
uncovered shape is `P21` (non-`bc`-parallel, no short `bc`-companion, reachable by neither
mechanism). Residue renamed **(K-slide-cl)** (class-uniform, parallel-free shapes).
`notes/Pencil-informal.md` §(K-slide); exact-ℚ `notes/scripts/w4/kslide.py`.

One more scope note for the eventual discharge, recorded while fresh: `hK`'s class also
contains `k > 0` (`def(G) > 0`) habitats, where `G′` can have corank 0 (no stress at all
— e.g. `C₇ → C₆`) and the escape story is vacuous; the discharge there should follow KT
Case II (Lemma 6.8, which §R3 found survives the pin), not Case III. The `k = 0` /
`k > 0` fork is internal to the discharge; nothing in `hK`'s statement moves.

### (K) literature hunt (option C) (2026-07-30): the crux is novel — NO HIT

The user-adjudicated option-C hunt (above): *does published literature bear on the (K-tight)
crux — stress non-constancy for count-tight body-hinge multigraphs on the pencil substratum?*
Method: WebSearch/WebFetch + the `.refs/` copies (pypdf keyword sweeps + page reads). Verdict:
**NO HIT on the crux.** The closest published body of work is the White–Whiteley "pure
condition / algebraic geometry of stresses and motions" theory, which is the in-print ancestor
of option B's stress-as-chart-rational-function infrastructure but does **not** address the
constrained-substratum non-constancy the (K-tight) kernel needs. The stratum-specific question
is confirmed novel (the phase-open no-literature finding stands, now against a deliberate hunt).

**What was searched (so the hunt is not silently repeated).**
- *Venues/authors:* White–Whiteley algebraic-geometry-of-stresses/motions (`.refs` 1983, 1987);
  Whiteley molecular + hinge-panel special-position analysis (`.refs` 1988, 1999, 2005); Tay
  1989 (`.refs`); Schulze–Tanigawa symmetric body-hinge; Nixon–Owen–Power surface-constrained
  frameworks; Jackson–Jordán molecular (`.refs` 2008/2009); Tanigawa Dilworth-truncation (`.refs`
  2010); Garamvölgyi generic stress matroid (2023). Spot-check of the two phase-open sources:
  Jordán 2016 (`.refs`) has **0** pages matching pencil/coplanar/concurrent/molecular/
  special-position; KT 2011 already recorded silent — both confirmed silent, not re-litigated.
- *Terms:* "self-stress / stress matrix (5,6)-tight body-hinge"; "pure condition bracket-ring
  special positions"; "coplanar/concurrent hinge special position stress"; "generic rigidity on
  a variety / substratum"; "coincident-point rigidity special position"; "corank-1 stress
  rational function transversality"; "sp²/planar-bonded molecular rigidity".

**Nearest hits (verified citations; each a MISS on the crux, relevance noted).**
- **White & Whiteley, *The algebraic geometry of motions of bar-and-body frameworks*, SIAM J.
  Algebraic Discrete Methods 8 (1987), no. 1, 1–32** (`.refs`, title page + p. 21–25 read).
  THE closest analogue: for a bar-and-body isostatic multigraph a *single* polynomial (the pure
  condition) cuts out the special positions, and at a generic point of each irreducible factor
  the stress space is 1-dim with scope = the whole block (Prop. 4.6), with the factoring given by
  the block lattice. *Miss:* (i) bar-and-*body*, not body-*hinge* (a hinge is a special 2-extensor
  position of five bars); (ii) it structures the stress at generic points of the special-position
  *variety* (where the frame goes dependent), not on a full-rank **pencil substratum**; (iii) it
  proves stress *scope/factoring*, never the **non-constancy of a fixed corank-1 stress's a-block
  direction `[r]` as data varies within a tight substratum** — exactly the (K-tight) object. It is
  the published shape of option B's infrastructure, not a discharge of (K).
- **White & Whiteley, *The Algebraic Geometry of Stresses in Frameworks*, SIAM J. Algebraic
  Discrete Methods 4 (1983), no. 4, 481–511** (`.refs`, DOI 10.1137/0604049). The bar-joint
  predecessor of the 1987 theory; same single-polynomial / stress-factoring story, one step
  further from body-hinge. *Miss:* same three reasons, more so.
- **Whiteley, *Rigidity of molecular structures: generic and geometric analysis*, in Rigidity
  Theory and Applications (Thorpe & Duxbury, eds.), Kluwer/Plenum 1999, pp. 21–46** (`.refs`,
  pp. 25–32 read). Directly on molecular (concurrent-hinge) bodies and their **polar hinge-panel
  (coplanar-hinge)** structures; carries the geometric special-position analysis (C₆ boat = linear
  line complex, the Bricard "four planes concurrent" shaky condition). *Miss:* expository /
  per-small-cycle (C₆), no general non-constancy result for tight (5,6) multigraphs; and it treats
  concurrency (molecular) and coplanarity (its polar) as **separate dual halves** — never their
  intersection, which is exactly the pencil stratum (both at one body). Corroborates the project's
  self-dual-stratum finding; does not touch the crux.
- **Whiteley, *Union of matroids and rigidity of frameworks*, SIAM J. Discrete Math. 1 (1988),
  no. 2, 237–255** (`.refs`, p. 245 read). States the concurrent↔coplanar polarity (three
  concurrent lines dual to three coplanar) and, in §6.2, points to the White–Whiteley
  single-polynomial special-position theory. *Miss:* the polarity is background the project
  already has; no non-constancy result.
- **Schulze & Tanigawa, *Linking rigid bodies symmetrically* (arXiv:1402.0039, 2014).** Symmetric
  body-bar/body-hinge rigidity via symmetry-adapted matrices. *Miss:* a **symmetry** substratum,
  not the concurrency+coplanarity pencil substratum; orthogonal machinery.
- **Garamvölgyi, *Stress-linked pairs of vertices and the generic stress matroid*
  (arXiv:2308.16851, 2023).** Algebraic-dual "generic stress matroid" of the bar-joint rigidity
  matroid; about *generic* stress structure / global-linkedness. *Miss:* bar-joint, generic (not a
  constrained substratum), and about stress *constancy* across generic realizations — the opposite
  question from substratum non-constancy.
- **Nixon–Owen–Power surface-constrained frameworks** (surveyed, not a `.refs` primary): a
  "generic rigidity on a variety" template, but for **bar-joint** frameworks on 2-surfaces
  ((2,k)-tight), no bearing on body-hinge pencil stress. *Miss.*

**Consequence for the phase.** None — option A stands (adjudicated). The hunt does **not** change
the (K) outlook: no published result discharges (K-tight), and the nearest theory (White–Whiteley
pure condition) is precisely the infrastructure option B would build in-tree, not an off-the-shelf
citation. If (K) research ever resumes under option B, the 1983/1987 pure-condition papers are the
right starting exemplars for the corank-1 cofactor gadget + irreducible-factor stress bookkeeping.
No coordinator/user escalation needed (expected NO-HIT confirmed).

**(K-pitch) pointer (2026-08-04).** The pure-condition calculus WAS since engaged, informally
and without commissioning option B: at companion-length-3-chain splits the pitch certificate
factors into a product of five 4-point brackets — the White–Whiteley factoring mechanism in
miniature, on the motion side. `notes/Pencil-informal.md` §(K-pitch).

### (K-bare) extension-route recon (2026-07-30): NO-GO on landed machinery — the kernel is real, corank-stratified, and its stressed stratum is nonempty

Commissioned per the *Hand-off* `hbareSplit` bullet: *does the extension route discharge
`hbareSplit` with landed machinery, and if not, what exactly is the new mathematics?* Methods:
definition-body re-reads (`PencilNondegFeasible`/`IsNondegPencilRealization`, `Motive.lean:110/133`;
`HasPencilRealization`, `Statement.lean:103`; `exists_pencilSeed_of_nondeg`, `Reseed.lean:65`;
`indep_edgeSet_mulTilde_of_noRigid_of_pos`, `ReducibleVertex.lean:515`; the L7c-5 body,
`Escape.lean:334ff`), a skeleton-arithmetic construction, and exact-ℚ probes
(`notes/scripts/kbare/danger.py`; reproduce `python3 notes/scripts/kbare/danger.py` from that
directory). Verdict: **NO-GO for a build now** — the extension route stays *supported as
mathematics* (strengthened below) but no landed-machinery route closes the `∀ G` leaf; carrying
`hbareSplit` as pinned (the standing GO) is unchanged. What the recon settles:

**1. The landed genericity machinery is *provably* dead at infeasible `G` — by definition, both
sides.** `PencilNondegFeasible` (`Motive.lean:133`) IS "a nondegenerate realization exists", so
`¬ PencilNondegFeasible K G` says the entire chart/reseed/engine device has *nothing to consume*:
`exists_pencilSeed_of_nondeg` (`Reseed.lean:65`) takes an `IsNondegPencilRealization`, and the
engine's callers all sit above it. Infeasibility propagates to `G′` (residue (ii) item 2), so no
reseeding device exists on either side. The extension's ONLY genericity slot is the
**`pt(v)`-placement freedom**: 3-dim when both split ends are non-hubs, 2-dim (the hub end's star
plane, which contains `line(pt a, pt b)`) when one end is a hub — `hsafe` caps hub ends at one,
so the freedom never drops below 2-dim and line-avoidance is always dimensionally possible.

**2. Count dichotomy — landed-brick shape, corank-stratifies the kernel.** If `E(G̃)` is
count-dependent it contains a circuit (`Matroid.Dep.exists_isCircuit_subset`);
`circuit_induces_isRigidSubgraph` + `hnoRigid` (vertex-properness) force the circuit to *span*, so
`def(G) = 0`. This is exactly the body of `indep_edgeSet_mulTilde_of_noRigid_of_pos`
(`ReducibleVertex.lean:515`, KT 4.5(ii)), whose minimality enters only via
`loopless_of_isMinimalKDof` (`:521`) and `hG.deficiency_eq` (`:582`) — a habitat variant (explicit
`hloop` + deficiency value) is mechanical, the same freeing as `simple_of_loopless_of_noRigid`.
With corank-at-target `= index + def` (`index := 5|E| − 6(|V|−1)`) and `def(G′) ∈ {def, def−1}`
(`splitOff_deficiency_le/ge`), the (K-bare) habitat splits: **`def > 0` ⟹ count-independent**
(corank 0 at `G`, ≤ 1 at `G′`); **count-dependent ⟹ rigid** (`def = 0`, `index ≥ 1`, corank
`index` at `G` and `index + 1 ≥ 2` at `G′`). `index ≤ 4` (`edgeBound_of_noRigid_of_degree_two`)
keeps the stratification finite.

**3. The landed gate's evidence covered only the independent stratum.** Probe 0 (`danger.py`):
all seven gate gadgets — `theta(6,6,6)+center` and its split, `spider(5,5,5)+center`, the
17-vertex gadget, the `theta` family sweep — are count-INDEPENDENT (`target = 5|E|` in every
attainment figure; corank 0 at `G`'s target). The "parity with (K)" reading was
independent-stratum-only (scope note added at the gate block above).

**4. The stressed stratum is NONEMPTY inside the (K-bare) habitat — witness DZ, so infeasibility
buys no corank control.** Construction (skeleton arithmetic: subdivide a cubic multigraph
skeleton, `f`-constraints become per-sub-skeleton length bounds — every 2EC skeleton edge ≤ 4,
skeleton cycles through two apex edges ≥ 7 total, sub-thetas ≥ 13; a triangle-containing skeleton
like `K4` is arithmetically excluded at index 1, which is why the earlier 19-vertex theta family
was forced count-*sparse*): **DZ** = subdivided `K3,3` on parts `{h0,u1,u2} | {h1,h2,h3}`, lengths
`h0`: (1,1,1), `u1`: (2,4,4), `u2`: (4,2,4). Certified exactly (`danger.py` probe 1): 20v/23e,
simple, 2EC, min-deg 2, `max f(W)` over proper `|W| ≥ 2` = **−1** (no proper rigid), `f(V) = +1`
(count-DEPENDENT, spanning circuit, index 1), `def = 0`, and `closedHubNbhd(h0) =
{h0,h1,h2,h3}`, ncard **4** ⟹ provably infeasible
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, contrapositive). A genuine
`hbareSplit` habitat member whose split carries **corank 2** at target-rank seeds — beyond even
(K-tight)'s corank-1 setting. Consequence: `¬Feasible` does NOT confine the discharge to
corank ≤ 1; the two kernels' hard zones are *disjoint but adjacent* ((K-tight): tight rigid,
feasible side; (K-bare)-dependent: index ≥ 1 rigid, infeasible side).

**5. Extension probes at DZ — the route's mathematics survives at corank 2 (N-DZ).** Bare target
attained at `G` (114/114, 10/10 samples + exact-ℚ confirm — DZ is *not* a counterexample to
PENCIL's bare half). From corank-2 target-rank `G′` seeds, for BOTH split shapes — non-hub-ends
(free placement) and the KT-faithful hub-end split at `v = u1h2_1` (`a = u1` hub: placement
confined to `u1`'s star plane) — **every off-line placement tried attains** `114` (exact-ℚ
confirmed once per shape) and **every on-`line(a,b)` placement fails by exactly 1** (113;
midpoint included — collinear `pt(v)` puts both new hinges on the deleted hinge's own line). The
def-equal caveat's locus persists at corank 2 and, at every seed tried, the observed failure set
is exactly the line. 0/15 seeds produced an off-line failure.

**6. Where `¬ PencilNondegFeasible K G` is consumed: routing only.** In the landed assembly it
selects the branch (`Escape.lean:396–428`); in the extension route it acts *negatively* (item 1 —
it is why no landed device applies). The insertion statement itself is feasibility-blind (the
gate's context probe C already certified it at a feasible gadget), and no step of the identified
discharge consumes the forced `≥ 4`-hub witness (it sits off the chain, `v`-free). A future
discharge *may* exploit that structure, but nothing identified needs it — so a proof of the
insertion lemma below would discharge `hbareSplit` with its `¬Feasible` antecedent unused.

**The minimal new mathematics (the honest core).** One open statement:

> **(K-bare-ext)** — the *arbitrary-seed insertion lemma*: for **every** bare pencil realization
> of `G′ = G.splitOff v a b e₀` attaining `target(G′)` (habitat antecedents, `hsafe`), there is a
> placement `pt(v)` — off `line(pt a, pt b)`, and inside the hub end's star plane when an end is
> a hub — whose induced realization of `G` attains `target(G)`.

The caveat's Lean form is a **side condition inside (K-bare-ext)'s `∃`** (a non-collinearity
`pt(v) ∉ line(pt a, pt b)`, e.g. a 3-point LI conjunct), NOT a separate genericity-supply
obligation: the supply is the placement freedom itself over `[Infinite K]` (avoid a line in a
≥ 2-dim slot) once the attainment locus is known nonempty — the W5 seed/reseed/engine devices are
not the supply and provably cannot be (item 1). Why (K-bare-ext) is new mathematics, precisely:
the only identified proof calculus is the boundary-load / `R_a`-image analysis of the (K)
non-constancy recon §2, which (i) is **not landed**, (ii) carries the explicitly-owed **KT
pp. 684–691 re-pin** as its first task — that re-pin is therefore a prerequisite here, not a free
brick — and (iii) was derived for *chart-generic* seeds: its `s₀ = 0` step (shared-subrank
genericity) is not automatic at an opaque IH seed, so a genuinely new **arbitrary-seed/seed-repair
extension** of the calculus is needed (rank-`≥ target` is open, which helps perturbation
arguments, but in-pencil-variety local moves have no landed device at infeasible `G′`), plus a
**corank-stratified uniform statement** (corank-0 seeds reduce to a stress-free monotone
row-independence claim — the (K-shared) shape; corank ≥ 1 meets escape-type stress obstructions;
corank 2 is now known reachable). Relative to (K): easier on uniformity (no non-constancy — the
placement freedom is the prover's), **harder on the seed side** (no chart, adversarial seeds), so
(K)'s option-B stress-function infrastructure serves it only in its arbitrary-seed variant —
(K-bare-ext) is related to, but not subsumed by, that commission.

**Adjudication options (user). ADJUDICATED (2026-07-30 follow-up, verbatim): "C: cheap
numerics extensions + A"** — option A (keep carrying `hbareSplit` as pinned, the standing
route-(a) GO) stands AND option C's three probes were commissioned and run same day (results
block below); option B (the insertion-calculus research) is NOT commissioned now.

- **A — keep carrying `hbareSplit` as pinned** (recommended; this is the standing "route (a) GO"
  adjudication, unchanged). Zero effort now; this recon's stratification + (K-bare-ext) become
  the discharge's roadmap, exactly as the (K) recon's stratification did for `hK`.
- **B — commission the insertion-calculus research** (the only identified path to closing
  `hbareSplit` in-tree): first the owed KT pp. 684–691 re-pin, then the corank-stratified
  boundary-load lemma at arbitrary seeds, then (K-bare-ext) on top — research-scale, success not
  assured; shares its hardest ingredient (stress control at non-generic seeds) with (K)'s
  option B without being identical to it.
- **C — cheap numerics extensions alongside A** (evidence-only, cannot close the leaf):
  adversarial seed hunts at DZ (deeper-degenerate `G′` seeds, à la `stress_extra.py`), an
  `index ≥ 2` danger-gadget existence search (the `K3,3` skeleton is arithmetically excluded at
  index 2 by the same length bounds; larger skeletons unprobed), and off-line failure-locus
  mapping (is the failure set *exactly* the line at corank 2?).

**Option-C results (2026-07-30, same day; exact-ℚ, `notes/scripts/kbare/optc.py`; reproduce
`python3 optc.py c1|c2|c3` from that directory).** Evidence-only, per the adjudication — nothing
here closes the leaf; (K-bare-ext) as pinned is unchanged. Findings:

- **C1 (adversarial seeds).** The three *chain-local* degenerations tried at DZ's corank-2 split
  (chain line forced through the far hub point, from either side; apex star collinear) all fall
  **below `target(G′)`** at every sampled seed (106–107 vs 108, 18/18) — they are excluded by
  (K-bare-ext)'s own rank antecedent. A structural plus for the eventual discharge: at these
  seeds the target-rank hypothesis itself polices exactly the local chain degeneracy the
  insertion calculus's `dim S` step needs (evidence-level: one gadget, one sampler family). The
  *global* hub-coplanar degeneration IS target-compatible: 6/6 corank-2 seeds, off-line
  placements attain 3/3, on-line/midpoint fail by 1 — the picture is unchanged on that deeper
  stratum.
- **C2 (`index ≥ 2` existence) — danger gadgets with corank-3 splits EXIST.** In the family
  "subdivided cubic skeleton + apex hub (three length-1 edges), per-edge length ≤ 3" (the length
  bound is forced at index 2 by the drop-one-edge subsets): `K3,3` is arithmetically excluded
  (0 candidate length assignments), but **cube `Q3` and Wagner `V8` (both 24v/28e) and Petersen
  (29v/34e) all yield hits** — both 8v-skeleton hits certified exactly (`f(V) = +2`, `def = 0`,
  `max f(W)` proper `= −1`, 2EC, simple, infeasible; the Petersen hit skeleton-level-certified
  only, `2^29` exact table skipped). Mini-gate on both 8v hits: bare target **138/138 attained**
  (corank 2 at `G` itself), and extension from **corank-3** `G′` seeds (hub-end split, placement
  confined to the hub's star plane): off-line in-plane attains 3/3 at every seed, on-line fails
  by exactly 1 (137). So the corank stratification is genuinely inhabited at least up to
  `corank(G′) = 3` (`index ≤ 4` caps it at 5), and the qualitative extension picture is
  corank-stable so far.
- **C3 (failure-locus map at corank 2).** At fixed target-rank DZ `G′` seeds, both split shapes:
  **every** sampled point ON `line(a,b)` fails by exactly 1 (15/15 per shape, rank exactly
  `target − 1`; 3 per shape exact-ℚ-confirmed), and **0** exact-ℚ-confirmed failures among 179
  off-line placements (80 free-space randoms + 20 points on planes through the line at the
  non-hub split; 79 randoms in the hub end's star plane at the hub-end split). As far as
  sampling shows the failure set is *exactly* the deleted hinge's line — sharply consistent with
  (K-bare-ext)'s side condition being precisely line-avoidance and nothing more.

**Widened-habitat pointer (2026-08-02).** W4 routes 1/3 do **not** reach this kernel —
a residual is `PencilNondegFeasible` by hypothesis, so the split producer's
`hbareSplit` branch (`Escape.lean:424–428`) is unreachable there; this recon's count
dichotomy and (K-bare-ext) stand exactly as pinned. `notes/Pencil-informal.md`
§"widened kernels (routes 1/3)" *Step 0*.

**(K-tight) re-pin pointer (2026-08-02, later).** (K-bare-ext)'s named prerequisite —
the KT pp. 684–691 re-pin — is **done** (`notes/Pencil-informal.md` §(K-tight); exact at
arbitrary target-rank seeds, so item (iii)'s chart-genericity worry narrows to
`dim R_a ≥ 1`). One correction to C3's gloss: the failure set is *not* exactly the line —
on the `dim U = 2` stratum it is `line(a,b) ∪ P′`, a second line invisible to C3's
sampling and exhibited at the control (`repin.py --control`); (K-bare-ext)'s `∃`-form
side condition is unaffected. Implications for the statement:
`notes/Pencil-informal.md` §(K-bare-ext).

**Numerics index (this recon).** `notes/scripts/kbare/danger.py` (see the directory README's
row): probe 0 = gate-gadget count audit; probes 1–2 = DZ certification + bare attainment;
probes 3a/3b = corank-2 extension, non-hub-ends and hub-end splits.
`notes/scripts/kbare/optc.py` (README row): the adjudicated option-C probes — C1 adversarial
degenerate seeds, C2 index-2 gadget search + corank-3 mini-gate, C3 failure-locus map.

### W4 decomposition recon (2026-07-30): the `hcontract` arm — dispatch skeleton, two carried kernels, one under-decomposed branch

Commissioned by the coordinator (the phase's last unattacked core; the `hK`/`hbareSplit`
adjudications stand and were not reopened). Continues §"W4 route (third core)" above.
Methods: landed definition bodies re-read (`Escape.lean`'s successor `hcontract` slot;
`Motive.lean` `PencilPair`/`IsNondegPencilRealization`; `Deficiency.lean`
`IsProperRigidSubgraph` — carries `2 ≤ |V(H)|` and `V(H) ⊊ V(G)`, so the contraction
measure and nonemptiness are free; `ReducibleVertex.lean` `rigidContract` +
`rigidContract_vertexSet_ncard_lt`; `Contraction.lean` `rigidContract_deficiency_eq`
(landed, minimality-free) and the two KT-6.5/6.6 identification lemmas
(`exists_degree_two_removeVertex_of_no_simple_contraction`,
`deficiency_eq_zero_of_simple_rigid_no_simpleContraction`) — both verified to consume
`IsMinimalKDof n 0`; the panel Case-I architecture (`Theorem55.lean`
`case_I_dispatch_gen`/`case_I_realization_nonsimple_gen`/`case_I_realization_h65_gen`,
`CaseI.lean`/`Coupling.lean`); L7b's landed body (`Escape.lean:186` — its `htf` is consumed
*only* through the two `Witness.lean` somewhere-producers); a `lake env lean` signature
spike (all five statements below elaborated AND the full dispatch skeleton *compiled*
against them, `sorry`-bodied kernels; scratch deleted); four new exact-ℚ gates
N8/N9/N10/N10b (tracked, `notes/scripts/w4/`, README there). KT pointers (Lemmas 6.2/6.3/6.5,
Claims 6.4/6.6, pp. 673–676) are consumed as previously verified (§Citations); no new
external citations are introduced.

**Verdict (a) — the constrained family `F` is NOT reified.** No new motive, no `F`
predicate, no `PencilPair` change. The fiber-product family (pairs coupled by the W2
cross-incidences at `δ(V′)`) lives only *inside* the kernels' discharges — as the
graded-chart parametrization of constrained substrata (verdict 3's N6 blueprint) — exactly
as (K) avoided reifying `escapePoly`. At statement level the arm carries hK-shaped
implications: realization-level inputs at the contracted graph, the ∃-LI-`pencilRow`
conclusion at `G`. **Remainder (iii) is thereby settled by the landed `PencilPair`:** the
IH interface is the conditioned pair itself, and its consumption partitions by the
*contracted graph's* two-layer conditioning — `(G.rigidContract H r).Simple ∧
PencilNondegFeasible K (G.rigidContract H r)` gates the generic input, mirroring L7c-5's
feasible/infeasible partition one level down.

**Verdict (b) — the dispatch skeleton is buildable now (spike-compiled).** The `hcontract`
producer `pencilPair_of_properRigid` dispatches four ways (KT's own 6.2/6.3/6.5 split plus
the pencil's second conditioning layer):

1. `¬ G.Simple` — generic conjunct vacuous; bare via **W4-A** (KT Lemma 6.2 mirror, below).
2. `G.Simple ∧ ¬ PencilNondegFeasible K G` — generic vacuous (`absurd`); bare via kernel
   **(K-bare-c)** fed the *bare* IH at `G.rigidContract H r` (any `(H, r)`; the bare IH is
   unconditioned, so no contraction dispatch is needed here).
3. `G.Simple ∧ Feasible ∧ ∃ (H, r)` with contraction Simple ∧ Feasible — the IH's generic
   half fires at the contraction; kernel **(K-c)** turns it into LI rows for `G`; **W4-B**
   (below) steers them to the generic motive; bare = forgetful. (Skeleton note from the
   spike: build the generic result once and pair it L7c-5-style,
   `⟨fun _ _ => hgen, hasPencilRealization_of_generic hgen⟩` — the two conjuncts must not
   each re-run the construction.)
4. `G.Simple ∧ Feasible ∧` no such `(H, r)` — the **vertex-removal branch** (KT Lemma 6.5
   territory, broadened by the feasibility layer), carried as the explicitly
   under-decomposed `hnoGood` hypothesis pending its own identification recon (verdict (d)).

Measure plumbing all landed: `rigidContract_vertexSet_ncard_lt` (strict decrease from
`2 ≤ |V(H)|`), image-nonemptiness via `vertexSet_rigidContract`, `IsProperRigidSubgraph.
vertexSet_nonempty` for the representative `r`.

**Verdict (c) — the pinned carried shapes** (all spike-elaborated; antecedent discipline as
`hK` — everything the call site has; `[Inhabited α]` needed by `pencilRow … G.endsOf`, the
L7b-flagged correction):

```lean
hKc : ∀ (G H : Graph α β) (r : α), G.Simple → 3 ≤ V(G).ncard →
  H.IsProperRigidSubgraph G 3 → r ∈ V(H) →
  PencilNondegFeasible K G →
  (G.rigidContract H r).Simple →
  HasGenericPencilRealization K 3 (G.rigidContract H r) →
  ∃ (hubSel : α → Fin 3 → Option α) (q : α × Fin 4 × Fin 4 → K)
    (s : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2)),
    (∀ w, IsFin3SelectorOf (G.closedHubNbhd w) (hubSel w)) ∧
    (∀ i ∈ s, (i : β × _ × _).1 ∈ E(G)) ∧
    ((Nat.card s : ℤ) = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) ∧
    LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q (i : β × _ × _))

hbareContract : ∀ (G H : Graph α β) (r : α), G.Simple → 3 ≤ V(G).ncard →
  H.IsProperRigidSubgraph G 3 → r ∈ V(H) →
  ¬ PencilNondegFeasible K G →
  HasPencilRealization K 3 (G.rigidContract H r) →
  HasPencilRealization K 3 G

hnoGood : ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard →
  PencilNondegFeasible K G →
  (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
  (∀ (H : Graph α β) (r : α), H.IsProperRigidSubgraph G 3 → r ∈ V(H) →
    ¬ ((G.rigidContract H r).Simple ∧ PencilNondegFeasible K (G.rigidContract H r))) →
  (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
  HasGenericPencilRealization K 3 G
```

**(K-c)** is KT Claim 6.4 at the rank-increment level on the constrained family: input =
exactly what branch 3 extracts from the IH; conclusion identical to `hK`'s ∃-LI form
(branch- and bookkeeping-agnostic; the vacuity guard mirrors `hK` — an infeasible
contraction kills the input). Bookkeeping grounding: `rigidContract_deficiency_eq` pins
`def(G/E(H)) = def(G)`, and `|V(G/E(H))| = |V(G)| − |V(H)| + 1` makes the target increment
exactly `6(|V(H)| − 1)` — the H-block's own rigid-block target, N3's `18 = 6·3` (the ncard
*equality* for the collapse image is one small counting brick; only `<` is landed). Its
discharge is the phase's genuine W4 research: (i) the graded chart on the constrained
substrata (points-first elimination, N6 sampler as blueprint) — the joint-genericity
device, remainder (i); (ii) per-boundary-pattern in-family `G′`-block witnesses — remainder
(ii), evidence now N3 + N10 + N10b (three structurally distinct patterns, below); (iii)
the specialization semicontinuity step (KT p. 675's argument re-run on the chart). Both
attack routes factor through the discharge without loss.

**(K-bare-c)** mirrors `hbareSplit` (weakest-precondition; the implication may ignore the
given witness — its truth follows from the bare conjecture at `G`). Evidence: gate N8
(below) — and note the specialization glue *runs* at the fully degenerate contracted input
(the 3-parallel class's target-rank realizations are provably all coincident-cluster: two
distinct hinges through both points force coincident points, then coincident panels — the
W5-L5 forcing).

**`hnoGood` is a branch-arm, NOT a crisp kernel** — it carries the full IH, so per the
(K)-full rejection rationale it must not be treated as a discharge-ready research kernel;
it is the honest placeholder for branch 4 pending the identification recon below. Do not
build a discharge against it before that recon re-pins it. *(Re-pinned 2026-07-30 by the
L4 recon: superseded by the NARROWED `hnoGood'` + the buildable co-1 identification leaf
— see §"W4-L4 identification recon".)*

**W4-B — the feasibility-based L7b sibling (buildable leaf).** Statement = L7b
(`hasGenericPencilRealization_of_independent_pencilRow_target`) with `hcard`/`htf` replaced
by `hfeas : PencilNondegFeasible K G` (spike-elaborated). The contract habitat *has*
triangles (a triangle is proper rigid at `4 ≤ |V|` — the arm's own entry condition), so
L7b is unusable as landed; but its `htf` is consumed only through the two `Witness.lean`
somewhere-producers (`exists_coord_linearIndepOn_pencilChartPoint_perBody`/
`_adjacentPair`), which *construct* point-LI seeds from nothing. With feasibility in hand
the witness itself supplies every point condition, transported to the chart by the landed
re-seed (`exists_pencilSeed_of_nondeg`); the one new brick is sourcing those conditions
**at `hEsc`'s own `hubSel`** (the re-seed reproduces at the witness's selectors; a
per-body slot-transport — same arity-dispatch pattern as `Engine.lean`'s landed sweeps,
`pencilChartPoint` is per-body local — is the flagged risk, est. small). Everything else
is L7b's body verbatim (engine call, WF reconstruction, `fillNbr` re-choice, rank pinch).

**W4-A — the non-simple bare producer (buildable leaf; KT Lemma 6.2 mirror,
minimality-free).** `¬Simple` + loopless gives a parallel pair; the 2-body pair subgraph is
proper rigid at `3 ≤ |V|` (the landed `isKDof_zero_of_parallel_pair` + the panel 6.2's own
`H′` construction pattern); contract it (`rigidContract_deficiency_eq` preserves the
deficiency, so targets differ by exactly `6`); bare IH at the contraction; un-contract with
**shared data** — both endpoints inherit `(pt₂(v*), Π₂(v*))`, old hinges keep their
extensors with endpoints re-routed (cross-incidences are free: the data is literally
shared; a third parallel edge, a *loop* at `v*` in the contraction, re-routes the same
way), and the class itself gets two independent lines through `pt*` in `Π*` (the W1
parallel-pair move). New bricks: the glue construction + `HasPencilPanelRealization` proof
(cut-arm assembly style), and the **motions-collapse rank brick**: with two
independent-line hinges on the pair, any glued motion has `S(x) = S(y)` (the two
`hingeRowBlock`s' kernels meet only in equality), so glued motions ≅ contracted motions
and `rank = 6 + rank(contracted)`; the `≤ target` direction is free (the universal
partition bound). Bounded, est. 2–3 commits; no kernel.

**Verdict (d) — the vertex-removal branch is real, nonempty, and holds the W4
discriminating instance; its identification is the one genuinely unshaped question.**
`C4+x,y` (the §W4-route cluster instance) is simple, feasible (hubs `{1, 3}` nonadjacent,
triangle-free — the landed L6b headline), has proper rigid subgraphs, and **every**
contraction is non-simple, provably: every rigid subgraph on ≥ 2 vertices contains both
`1` and `3` (deleting either leaves a star, a forest — nothing rigid), and every outside
body is adjacent to both, so ≥ 2 edges always merge into a parallel pair at `v*`. So
branch 4 cannot be dodged. On it, the KT-6.5 *shape* (a degree-2 vertex `v` with `G − v`
rigid) does hold at this instance (`v = x`, `G − x = C4+y`), and gate N9 (below) confirms
the pencil vertex-removal route end-to-end: IH at `G − x` attains 24/24, the re-add
(`pt(x)` on `Π(1) ∩ Π(3)`, hinges the forced joining lines) attains 30/30 — with a genuine
in-stratum failure locus, `pt(x) ∈ line(pt(1), pt(3))` capping rank at exactly 29
(deliberate control), excluded by precisely the output motive's fourth conjunct at `x`.
The geometric re-add is therefore the landed steering pattern (L5-cut-v /
`exists_isNondegPencilRealization_induce_promotedNormal_of_pendant_deg3`, plus the panel
h65's triple-LI det factor's pencil analogue) — bounded once the branch's combinatorics is
pinned. What is NOT known, and is the next recon's charter (**W4-L4**): the
minimality-free identification — both landed 6.5/6.6 lemmas consume `IsMinimalKDof n 0`
(verified against the bodies), the pencil habitat has no minimality, and the trigger is
broader (non-simple **or infeasible** contraction, no KT analogue for the second
disjunct). Open sub-questions there: does the branch always present a degree-2 vertex `v`
with `def(G − v) = def(G)` (the (K-bare) gate's `C₅ → P₄` warning shows vertex deletion
does not preserve deficiency in general)? and the `G − v` feasibility interface (the
cut-arm demotion gap; the landed input-steering pattern is the expected fix). Do NOT
assume KT Claim 6.6 transfers.

**Numerics index (this recon; exact-ℚ, tracked `notes/scripts/w4/hybrid_gates.py`, seed
fixed, reproduce `python3 notes/scripts/w4/hybrid_gates.py 6`).** All targets certified
against the exact partition deficiency; pencil-witness conjuncts verified per sample; the
universal `rank ≤ target` bound makes mod-p/exact agreement one-sided (the scripts use
exact ℚ throughout here).

| # | gate (instance, kernel shape probed) | result |
|---|---|---|
| N8 | K4 via triangle contraction ((K-bare-c): coincident-cluster contracted input, specialization glue) | contraction 6/6; hybrid **18/18** in 6/6 samples |
| N9 | `C4+x,y` via vertex removal (branch 4; also the first direct truth sample of the conjecture at the discriminating instance — §R2 only bounded it) | `C4+y` **24/24**, extended **30/30** in 6/6; collinear control: `pt(x) ∈ line(pt1, pt3)` gives exactly **29** (the fourth-conjunct locus) |
| N10 | `C4 + x∼1, y∼2, x∼y` via C4 contraction ((K-c): simple + feasible contraction; two *distinct-anchor* boundary panels — the first pattern beyond N3's single cluster) | triangle IH 12/12; hybrid **30/30** in 6/6 |
| N10b | `C4 + x∼1, y∼1, x∼y` (forced boundary panel: body 1's panel = `plane(pt₁(1), pt₂(x), pt₂(y))`, no genericity survives at it) | triangle IH 12/12; hybrid **30/30** in 6/6 |

Remainder (ii)'s evidence now spans three structurally distinct boundary patterns
(single-cluster N3, free two-anchor N10, forced-panel N10b) — per the pinned
numerics-first method, further patterns stay numerically explorable per-instance inside
(K-c)'s discharge.

**Honest scope caveats.** Every gate instance has `def = 0` at both `G` and the contracted
graph — deficient-habitat contraction instances are unprobed (the same count-independent
first-gate scope the (K-bare) arc later had to widen); the gates test the *hybrid at the
specialization-flavored family point*, not the chart-generic transfer (that is (K-c)-(iii)'s
research content); and `hnoGood`'s shape is deliberately coarse (see above).

**Ordered leaf list (W4-L*).**

- **W4-L1** (buildable now): W4-A, the non-simple bare producer + its two bricks
  (shared-data un-contraction glue; motions-collapse rank). 2–3 commits.
- **W4-L2** (buildable now): W4-B, the feasibility-based L7b sibling (one flagged small
  brick: somewhere point-conditions at an arbitrary correct `hubSel` from a nondeg
  witness). 1–2 commits.
- **W4-L3** ~~(after L1/L2): the dispatch skeleton `pencilPair_of_properRigid` (spiked
  above, compiles modulo the leaves/kernels)~~ **RESHAPED 2026-07-30 (L4 recon)** — the
  canonical skeleton is now L3′ in §"W4-L4 identification recon" (adds the ¬2EC cut-arm
  reuse and the co-1 dispatch; carried set changes).
- **W4-L4** (recon) — **FIRED 2026-07-30, verdict in §"W4-L4 identification recon"**:
  minimality trace complete, the feasibility-for-minimality trade closes the co-1 case
  minimality-free (buildable leaf W4-L4b), the residual narrows to `hnoGood'`
  (0 search candidates).
- **W4-L5** (build, after L4b): the vertex-removal geometric leaf — N9's construction in
  Lean (forced joining-line hinges, `pt(v)` steered off the failure line + promoted
  conditions), the L5-cut-v / h65 steering pattern on `G − v`'s chart. Interface now
  PINNED as the `hremove` producer shape (§"W4-L4 identification recon").
- **Kernels (K-c) / (K-bare-c)**: carried (the hK/hbareSplit posture); discharge research
  as recorded above, after (or alongside) the (K)/(K-bare) work they share the device
  extension with.

**Adjudication options (user). ADJUDICATED (2026-07-30, verbatim): "B: L4 recon
first"** — settle the W4-L4 minimality-free 6.5/6.6-identification question BEFORE
building L1→L3; options A (build now, kernels carried) and C (deficient-habitat numerics
first) are NOT commissioned now. The L4 recon ran the same day — verdict, the re-pinned
carries, and the L1–L3 reshape in §"W4-L4 identification recon" below (the leaf list
above is superseded in part by that section's restatement).

### W4-L4 identification recon (2026-07-30): minimality-free 6.5/6.6 — the feasibility trade, the co-1 dispatch, the narrowed residual

Commissioned by the user's "B: L4 recon first" adjudication (verbatim; options block
above). Question: can the KT Lemma 6.5 / Claim 6.6 identification be re-derived
minimality-free for the pencil habitat's broader trigger (contraction non-simple OR
infeasible)? Methods: the two landed identification lemmas' proof bodies read
line-by-line (`Induction/Contraction.lean:1004`
`exists_degree_two_removeVertex_of_no_simple_contraction`, `:1171`
`deficiency_eq_zero_of_simple_rigid_no_simpleContraction`); their input bricks verified
minimality-free against source (`exists_maximal_induced_isProperRigidSubgraph`,
`Deficiency.lean:978`; `exists_isLink_pair_of_rigidContract_not_simple`,
`Contraction.lean:870`; `removeVertex_deficiency_ge`, `SplitOffDeficiency.lean:405`;
`deficiency_le_deficiency_of_le_vertexSet_eq`, `Deficiency.lean:930`;
`two_le_degree_of_isKDof_zero`, `Deficiency.lean:1306`); a `lake env lean` spike (the
identification-lemma statement AND the full reshaped skeleton compiled, `sorry`-bodied
leaves only; scratch deleted); a two-run combinatorial search probe (tracked,
`notes/scripts/w4/no_good_search.py`). No new external citations (KT Claim 6.6, p. 676,
consumed as previously verified).

**Verdict 1 — the minimality trace.** `:1004` consumes `IsMinimalKDof n 0` at exactly
TWO points, both in its tail: step 4b, `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_
isKDof` (forcing `G = G''`, which is what buys `deg_G(v) = 2` and `G − v = G′`), and
step 5, `subgraph_minimality` (packaging `(G − v).IsMinimalKDof n 0` — consumed only by
the *panel* IH's minimality interface, which the pencil IH does not have). Steps 1–4a —
the maximal induced-saturated extraction, the parallel-pair extraction from
non-simplicity, the two-`addEdge` carrier `G''` with `G'' − v = G′` and
`def(G'') = 0`, and the maximality argument forcing `V(G'') = V(G)` — are entirely
minimality-free (every input brick verified). `:1171` consumes minimality ONLY in its
final line (`hG.deficiency_eq`, reading `k = def(G)`) — its own docstring's claim, now
verified against the body; a minimality-free sibling concluding `G.deficiency n = 0` is
an L7c-1-grade verbatim-prefix extraction (not separately needed below — the co-1 route
subsumes it).

**Verdict 2 — the feasibility-for-minimality trade (the recon's key finding).** In the
pencil habitat, the `hcard` bound (from `PencilNondegFeasible K G` via the landed
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`) replaces minimality for the
degree-2 conclusion. Let `H` be proper rigid with `v ∉ V(H)` and `eₐ : v–a`,
`e_b : v–b` into `V(H)`. Any third `G`-edge at `v` goes to some `w ∈ V(H) ∖ {a, b}`
(loopless; a repeat of `a`/`b` is a parallel pair, killed by `G.Simple`) — but then
`closedHubNbhd_G(v) ⊇ {v, a, b, w}` has FOUR members: `v` is a hub (three edges), and
each of `a, b, w` has `H`-degree `≥ 2` (`two_le_degree_of_isKDof_zero` at the rigid `H`,
`2 ≤ |V(H)|` from `IsProperRigidSubgraph`) plus the `v`-edge, so `G`-degree `≥ 3` —
contradicting `hcard`. Hence `deg_G(v) = 2` exactly, with no minimality anywhere.

**Verdict 3 — the co-1 reformulation: the identification decouples from contractions.**
The right dispatch is on `∃ H` proper rigid with `|V(H)| + 1 = |V(G)|` (a **co-1** rigid
subgraph), not on contraction non-simplicity:

- *Co-1 present:* `v` := the unique outside vertex; `deg_G(v) ≥ 2` (2EC, available by
  the skeleton's branch-0 below); `deg_G(v) = 2` by Verdict 2; carrier
  `G'' := (H.addEdge eₐ v a).addEdge e_b v b ≤ G` spanning with `G'' − v = H` (the
  landed `:1004` step-3 plumbing verbatim) gives `def(G'') = 0`
  (`removeVertex_deficiency_ge` + `def(H) = 0`), hence `def(G) = 0`
  (`deficiency_le_deficiency_of_le_vertexSet_eq`) and `def(G − v) = 0` (`H ≤ G − v`
  spanning). Simple ✓ by `mono`. **Every brick is landed**; the pinned leaf
  (spike-elaborated) is

  ```lean
  theorem exists_degree_two_of_co1_rigid [DecidableEq β] [Finite α] [Finite β]
      {G : Graph α β} (hSimple : G.Simple) (hV3 : 3 ≤ V(G).ncard)
      (h2ec : G.TwoEdgeConnected)
      (hcard : ∀ w ∈ V(G), (G.closedHubNbhd w).ncard ≤ 3)
      {H : Graph α β} (hH : H.IsProperRigidSubgraph G 3)
      (hco1 : V(H).ncard + 1 = V(G).ncard) :
      ∃ (v a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ eₐ ≠ e_b ∧
        G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧
        (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
        G.deficiency 3 = 0 ∧ (G.removeVertex v).deficiency 3 = 0 ∧
        (G.removeVertex v).Simple ∧ v ∈ V(G)
  ```

  This is leaf **W4-L4b** (buildable now, 1 commit).
- *The bridge to KT's trigger:* the maximal `G′`'s contraction being non-simple
  IMPLIES a co-1 rigid subgraph exists, minimality-free — steps 1–4a produce
  `V(G'') = V(G)` with `G'' − v = G′`, so `G − v ⊇ G′` is spanning on `V(G) ∖ {v}`,
  `def(G − v) ≤ def(G′) = 0`, and `G − v` is itself a co-1 proper rigid subgraph. So
  the co-1 dispatch **subsumes the entire non-simple disjunct** of the broader trigger;
  KT Claim 6.6's own carrier machinery survives as the bridge's proof, with its two
  minimality points replaced by Verdict 2 + the deficiency computation. (Conversely a
  co-1 subgraph's contraction is always non-simple at `deg_G(v) ≥ 2` — two vertices,
  parallel `v–v*` edges — so co-1 ⟺ maximal-contraction-non-simple in the 2EC habitat;
  prose only, the dispatch needs one direction.)

**Verdict 4 — the residual (`hnoGood` → `hnoGood'`, NARROWED).** With co-1 dispatched,
the carried branch shrinks to: `G` simple, 2EC, feasible, `∃`-rigid, **no co-1 rigid
subgraph**, and no `(H, r)` with contraction Simple ∧ Feasible. Its recorded structure:
every maximal induced-saturated proper rigid `G′` there has a provably **simple**
contraction (non-simple would produce a co-1 via the bridge — contradiction), hence
infeasible by the trigger; and infeasibility's `¬hcard` mechanism provably localizes AT
`v*` (an outside vertex `w` adjacent to `v*` loses its unique `V(G′)`-neighbour `u` —
always a `G`-hub, since `deg_{G′}(u) ≥ 2` plus `w`'s edge — and gains at most `v*`, so
off-`v*` closed hub-neighbourhoods stay `≤ 3`; a 4-member set needs `v*` hub with `≥ 3`
hub outside-neighbours). Honest caveat: `PencilNondegFeasible` has no combinatorial
characterization — landed-sufficient is `hcard ∧ triangle-free` (L6b) plus the spanning-
`C₃` witness (L7c-3); landed-necessary is `hcard` and no-2-hub-triangle — so a **middle
zone** (e.g. `hcard` graphs with only `≤ 1`-hub triangles beyond `C₃`) is undecided by
landed lemmas, and the residual's trigger is a genuinely geometric predicate. The
narrowed carry (spike-elaborated, still IH-carrying — a branch-arm, not a discharge-ready
kernel):

  ```lean
  hnoGood' : ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard →
    G.TwoEdgeConnected → PencilNondegFeasible K G →
    (∃ H : Graph α β, H.IsProperRigidSubgraph G 3) →
    (∀ H : Graph α β, H.IsProperRigidSubgraph G 3 → V(H).ncard + 1 < V(G).ncard) →
    (∀ (H : Graph α β) (r : α), H.IsProperRigidSubgraph G 3 → r ∈ V(H) →
      ¬ ((G.rigidContract H r).Simple ∧ PencilNondegFeasible K (G.rigidContract H r))) →
    (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
    HasGenericPencilRealization K 3 G
  ```

**Verdict 5 — residual inhabitedness: 0 candidates found; vacuity CONJECTURED, not
proven.** Search probe (`notes/scripts/w4/no_good_search.py`, two runs). Run 1 (coarse
two-way proxy, candidate-OVER-inclusive since provably-good was under-approximated):
full coverage of families A1 (cycle + 3 anchored hub gadgets, the `¬hcard`-at-`v*`
mechanism; 3267 instances) and A2 (cycle + anchored adjacent pair, the triangle
mechanism; 1170) + 2000 sparse randoms → exactly ONE candidate, `B#351` (two adjacent
degree-4 hubs joined by a hub edge + three length-3 paths) — dissolved on inspection:
contracting its rigid 6-vertex theta leaves the **spanning `C₃`**, simple and feasible
by the landed L7c-3 witness (the coarse proxy had treated every triangle as
not-provably-feasible). Run 2 (refined three-way classifier: provably-good /
provably-bad / middle-zone, `B#351` kept as a regression check, `|V| ≤ 13` cap): 4000
randoms + the two-hub-multi-path family C + capped A1/A2 → **0 candidates, strong or
middle**. Structural squeeze recorded: two hand constructions aimed at the residual both
collapsed (a C6+3-hub gadget — its `G − b` was rigid, i.e. co-1; a C5+pair gadget — a
small `C₄` subgraph had a simple + provably-feasible contraction), and the two-hub-long-
path family always yields a good contraction through "contract everything but one path"
(the leftover is a `C₃`/`C₄`/..., provably feasible). **Conjecture (open):** the
residual habitat is empty — every simple 2EC feasible graph with a proper rigid subgraph
has a co-1 rigid subgraph or a Simple∧Feasible contraction. If proven, `hnoGood'` is
vacuously dischargeable; until then it is carried as pinned. Do NOT treat the search as
proof; the middle zone additionally means a true inhabitant could be missed by the
proxies in either direction.
**REFUTED 2026-08-02** — the conjecture is FALSE (an explicit `|V| = 19` inhabitant, both
feasibility verdicts landed-lemma-certified; the caps above were the blind spot). Current
argument state, the structure theorem that survives, and the routes out:
`notes/Pencil-informal.md` §"`hnoGood'` vacuity".

**The reshaped skeleton (L3′) and the W4-L5 interface (`hremove`) — supersedes the
decomposition section's W4-L3 pin.** The skeleton `pencilPair_of_properRigid`
(spike-COMPILED end-to-end, `sorry`-bodied leaves):

0. `¬ G.TwoEdgeConnected` → reuse the landed cut arm wholesale
   (`pencilPair_of_not_twoEdgeConnected hD2 hn h2ec hIH`, `Pair2.lean` — signature
   verified; this is what puts 2EC in scope for every later branch, needed by both the
   co-1 identification and the residual's structure).
1. `¬ Simple` → generic vacuous; bare via W4-A (leaf W4-L1, unchanged).
2. `Simple ∧ ¬ Feasible` → generic vacuous; bare via `hbareContract` at any `(H, r)`
   (kernel unchanged).
3. `Simple ∧ Feasible`: build the generic result ONCE (`⟨fun _ _ => hgen,
   hasPencilRealization_of_generic hgen⟩`), by:
   - co-1 rigid subgraph exists → W4-L4b, then the vertex-removal producer `hremove`
     (the W4-L5 leaf's pinned interface — carried as a hypothesis until W4-L5 lands):
     from the habitat + the identification's outputs (`deg`-2 closure clause,
     `def(G) = 0 = def(G − v)`) + the IH, produce `HasGenericPencilRealization K 3 G`;
   - else `∃ (H, r)` contraction Simple ∧ Feasible → IH generic → `hKc` → W4-B
     (leaf W4-L2, unchanged);
   - else → `hnoGood'` (the antecedent plumbing from the two `by_cases` compiles —
     the no-co-1 strict bound comes from `Set.ncard_lt_ncard` on `V(H) ⊂ V(G)` plus
     the co-1 case exclusion).

**Re-pinned ordered leaf list (canonical; supersedes the decomposition section's).**

- **W4-L4b** (buildable now, 1 commit, all bricks landed): the co-1 identification
  lemma above. Recommended FIRST build of the arc (cheapest, and it certifies the
  trade that everything else leans on).
- **W4-L1** (buildable now, unchanged): W4-A, the non-simple bare producer.
- **W4-L2** (buildable now, unchanged): W4-B, the feasibility-based L7b sibling.
- **W4-L3′** (after L4b/L1/L2): the reshaped skeleton + successor restatement, carrying
  `hKc`, `hbareContract`, `hnoGood'`, and `hremove`; blueprint nodes in the same commit.
- **W4-L5** (its own arc, the largest build; before or after L3′): discharge `hremove` —
  the N9-validated re-add (forced joining-line hinges, `pt(v)` on `Π(a) ∩ Π(b)` steered
  off `line(pt(a), pt(b))`), the L5-cut-v / h65 steering pattern on `(G − v)`'s chart;
  its inner obligations: `G − v` feasibility for the IH's generic half (the demotion
  gap at the two neighbours — the landed input-steering pattern) and the output
  conjuncts at `v` and its neighbours.
- **Kernels** `hKc` / `hbareContract`: carried, unchanged. **`hnoGood'`**: carried,
  narrowed; ~~its research options are (i) prove the vacuity conjecture … or (ii) attack
  it directly~~ — option (i) is **REFUTED** (2026-08-02, `notes/Pencil-informal.md`
  §"`hnoGood'` vacuity"); the live options are now that section's routes 1–3.

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
