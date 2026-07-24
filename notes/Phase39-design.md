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
- **W5-L5**: the W3-L7 successor `pencil_conjecture_of_arms_pair` (spiked) + the arm
  re-derivations against the pair motive: loop arm free (the loop guard); base arm's
  generic half (small: single-edge/empty producers; parallel classes are
  nondegeneracy-infeasible, hence vacuous); cut arm's generic half (moderate — mirrors
  the landed `case_cut_edge_realization_gp_gen`; the W3-L4 transport/nondegeneracy/rank
  infra is reusable). This is the churn the GP caveat predicted, now bounded and
  scheduled.
- **W5-L6**: habitat feasibility (verdict 4) — the ≤ 3 closed-hub-neighbourhood lemma
  on 2EC/no-proper-rigid graphs + the witness-seed construction discharging
  `PencilNondegFeasible` at `G′ = G^{ab}_v`.
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
  is vacuous (contraction can create hub-parallel classes, which kill hub-LI —
  the mirror of the landed program's nonsimple flows around its
  `Simple`-conditioned half). L6 covers the *split* arm's `G′` only. This
  question is part of the W4 recon's charter (W4 recon).

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
