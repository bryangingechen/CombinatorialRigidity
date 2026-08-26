# PENCIL — §(K-grid) informal-mathematics workbook (the tight-stratum grid residual)

**Purpose.** §(K-grid) of the kernel-(K) research arc (Phase 39, PENCIL), split
out of `notes/Pencil-informal.md` (2026-08-19, the doc-split structural round,
`notes/Pencil-structure.md`) **verbatim** — heading, standing notation, and every
one of *Steps G0–G97* with their Verification / Confidence / What-would-change-this
blocks, byte-for-byte as they stood in the parent file. Nothing below is
re-verdicted, re-worded, or re-derived by the split; it is the same argument in a
new location. The split fired because this one section had grown to 9 883 lines —
39% of the parent workbook, six times the next-largest section — and was the
section three of the seventh fan-out's five directions wrote into.

**What stayed behind, and why.** The **State of (K)** gap map — the phase's single
status object, including §(K-grid)'s own gap-map row — stays whole in
`notes/Pencil-informal.md`; splitting it across files would defeat its purpose. The
*Shared dictionary*, the *Section index*, and every other §(K-*) section stay there
too. This file carries only the section body; `notes/Pencil-informal.md`'s *Section
index* points here, and `notes/check-gapmap-cells.py` needs no change (it reads only
the gap map, which did not move).

**Reading this file.** Cross-section citations that name a **label** — `(GR-nn)`,
`(GR-nn′)` — resolve via `notes/Pencil-labels.md`'s registry regardless of which
file the label's home section lives in; nothing about that registry changed. A
citation that names a **location** in the old sense ("§(K-grid) *Step Gnn*") now
means "*Step Gnn* below, in this file" rather than a spot inside
`notes/Pencil-informal.md`. The *State of (K)* gap map, `notes/Pencil-fanout.md`,
`notes/Pencil-labels.md`, `notes/Pencil-strategy.md`, `notes/Phase39.md`,
`notes/Phase39-design.md` and `notes/scripts/README.md` all cite this section by
name or by label; none of those citations needed to change except the small number
that named `notes/Pencil-informal.md` (the *workbook*) explicitly as this section's
location, which now name this file instead.

---

## §(K-grid) — the tight-stratum grid residual: the direction network becomes a **generalized-spline** problem, the "(AC-4)(i)–(ii) ⟹ isostatic" statement is **REFUTED as named**, its correction is a pair of **proven counting obstructions** that are **empirically exact**, chart-image membership is **proven and machine-verified**, and the census extends 15/15 to **907/907**

Read against §(K-clos): this section discharges the two deliverables its
(AC-6) verdict block names for the tight stratum — *Step Z4*'s direction
network, and the chart-image membership left "argued, not verified" — and
runs the cheap kill its *what-would-change-this* line asks for. Notation
inherited from §(K-clos) *Steps Z2–Z6*: `⋆`, the fixed quadric `Q`, the
ruling 2-colouring `col : E(G) → {A, B}`, the eigenspaces `Λ²₊`/`Λ²₋`, the
per-ruling-component parameters of the grid construction. Everything here is
over `ℚ(i) ⊂ ℂ̄`; descent is (AC-7)'s and is quoted, not re-derived.

**Status, stated before the mathematics.**

- **Refuted — the gap-map sentence as literally written.** The *State of (K)*
  map asked for *Step Z4*'s contracted direction network "proven isostatic
  whenever (AC-4)(i)–(ii) hold". That statement is **false**, and was already
  false in the pinned data: 8 of `ds-K4`'s 64 colourings are balanced with
  both ruling classes forests and sit at rank 89 < 90 (the `--sweep` rows
  with one eigen-block at 44). Mechanism identified and complete on the
  pool: a **bond of the contracted graph inside a single ruling class** —
  at `ds-K4`, a monochromatic hub, i.e. a free rotor ((GR-2)).
- **Proven — the reduction.** At a legal colouring each `⋆`-eigen-block is,
  after contracting the other ruling class, a **direction network in `K³`
  whose directions lie on a fixed conic and are constant on ruling
  classes** — equivalently a **generalized C¹-quadratic spline system** on
  the contracted multigraph, with edge moduli `(t − t_X)²`, one parameter
  per class. Its failure space `Z` (deficit from isostatic) has three
  equivalent exact descriptions and satisfies a rank identity verified at
  688/688 pool colouring-blocks ((GR-1)).
- **Proven — two obstruction families; empirically exact.** Two independent
  counting families bound `dim Z` from below ((GR-3)); at **generic** class
  parameters their max equals `dim Z` at every one of the 688 pool
  instances ((GR-4) — conjectured in general, exact on the pool). The
  concrete construction's component-index parameters are **not generic**
  (10/688 instances overshoot — a special-value artifact, not a property of
  the recipe). *(Since Steps G8–G9, 2026-08-06, direction G:)* **(GR-4) as
  stated is REFUTED on the widened pool** — the two families are incomplete
  (185 overshoots at 4200 blocks, 59 filter-passing), and the proven unified
  family **(GR-8)** (sub-multigraph cycle spaces) is exact at every probed
  block; the repaired equality is **(GR-4′)**, and **the discharge path no
  longer consumes any version of (GR-4)** (Step G10).
- **Proven-informally AND machine-verified — chart-image membership.** Every
  σ-fixed grid configuration with linearly independent closed-hub-
  neighbourhood point triples is projectively a point of the landed chart's
  image, at an explicit seed; the `pencilRow` rank at that seed is the
  configuration's body-hinge rank. Verified end-to-end at 5 shapes — the
  chart-constructed points *rebuild* the Tay-target rank ((GR-5)). "Argued,
  not verified" is retired.
- **The cheap kill came back empty, 907/907.** Over the full `kslidecomb`
  class pool — the **exhaustive `K4` stratum (877 shapes**, the same 877 the
  workbook's §(K-slide-comb) `--k4full` row counts — an independent
  consistency check on the pool enumeration**)**, a `|V°| ≤ 5` sweep (6
  shapes), a `|V°| = 6` seeded sweep (21 shapes), and the three tight
  thetas including the previously unpooled θ(2,5,5) — an admissible
  target-rank colouring **exists at every shape**, and at 835 of 907 shapes
  the *first* filter-passing colouring already hits ((GR-6) evidence).
- **What is left is combinatorial, and — since Steps G10–G11 — exactly ONE
  gap.** The former pair "(GR-4) + (GR-6)" is superseded: the **tree-triple
  certificate theorem (GR-9)** (proven) discharges the geometry outright
  wherever its colouring exists, consuming no version of (GR-4), and the
  residual is the single statement **(GR-10)** — every tight class shape
  admits an admissible colouring with both-block tree-triple certificates
  (907/907 measured, no min-max yet; the grouped-exchange failure is the
  named obstruction). No geometric residue remains: this is the
  "rank condition becomes combinatorial" step `Pencil-strategy.md` §2.2
  says the arc lacks, delivered for the tight stratum — with the arc's
  base-rate caveat now attached to a colouring-existence statement instead
  of a rank statement.

### Step G0 — the question, and what would count as an answer

§(K-clos) (AC-6) leaves one live question: does the grid recipe reach the
Tay target at every tight class shape? A negative with mechanism refutes the
tight-stratum residual; a positive **proof** would discharge `hK` there
directly (no escape route, no split, no inductive hypothesis), then over
every infinite characteristic-0 field by (AC-7). The section attacks it in
the order the map prescribes: census first (Step G5), then the two named
deliverables — the direction network (Steps G1–G4) and chart membership
(Step G6).

### Step G1 — (GR-1): the eigen-block is a conic direction network, i.e. a generalized-spline system, and its deficit has an exact linear-algebra form

Fix a legal colouring (all bodies distinct) whose class `B` is a forest,
and work in the `+` block; everything dualizes with `A ↔ B`, `+ ↔ −`.

**(a) Hinge lines are constant on ruling classes.** Two adjacent bodies of
an `A`-edge share their ruling-`A` parameter, so the hinge is *the* ruling-A
line at that parameter ((AC-2)); all edges of one `A`-component `X` (in this
section: one **class**) carry the **same projective hinge line**, whose
`Λ²₊`-coordinate vector `d_X` is a point of the conic
`Q₃ = {α² + β² + γ² = 0}` — the decomposable locus of the eigenspace
(§(K-clos) *Step Z2*). Distinct classes get distinct, freely choosable conic
points (one `P¹`-parameter each).

**(b) Contraction.** By (AC-4), the `+`-block unknowns are `m_v ∈ K³` with
`m_u = m_w` across `B`-edges (3 rows) and `(m_u − m_w) ∥ d_X` across
`A`-edges of class `X` (2 rows). With `E_B` a forest its rows are
independent, so writing `H₊ = G/E_B` (nodes = the `n_c` `B`-components):

> `rank₊ = 3|E_B| + rank(DN₊)`,

where `DN₊` is the **direction network** on the contracted multigraph: place
the `B`-components as points of `K³` such that, for each class `X`, the
nodes it meets are collinear along `d_X`. *Legality already sanitizes the
contraction*: two bodies coincide iff they share both ruling components, so
at a legal colouring `H₊` has no loops and no same-class parallel pairs.

**(c) The spline form.** Over `ℂ̄` (char ≠ 2) the conic is projectively the
moment curve: a fixed `ℚ(i)`-linear change of basis of the eigenspace puts
`d(t) = (1, t, t²)`. Writing `q_v(t) = m_v² − 2t·m_v¹ + t²·m_v⁰`, the edge
condition `(m_u − m_w) ∥ d(t_X)` becomes

> `q_u − q_w ∈ span (t − t_X)²`,

i.e. `DN₊`-solutions are exactly the **generalized C¹ splines of degree ≤ 2**
on `H₊` with edge moduli `(t − t_X)²` — one modulus per class, repeated on
the class's edges. (Generalized splines on graphs are a classical object —
GKM theory; Gilbert–Polster–Tymoczko, *Generalized splines on arbitrary
graphs*, Pacific J. Math. **281** (2016), no. 2, 333–364 — but the matroid
theory of *repeated* moduli needed here appears not to be off the shelf;
nothing below is cited from that literature.)

**(d) The failure space.** Global constants (dimension 3) are always
splines; the deficit is jump-valued. Writing `m = |E_A|`,
`cut(H₊) ⊆ K^{E_A}` for the cut space of the contracted multigraph, and
`s : E_A → K` for the class-parameter function (`s_e = t_{X(e)}`):

> **(GR-1)** *(proven; driver `--spline`, 688/688 exact)* Let `H₊` be
> connected. Then
>
> `rank(DN₊) = 3·n_c − 3 − dim Z₊`,  where
> `Z₊ = { c ∈ K^{E_A} : c, s·c, s²·c ∈ cut(H₊) }`
>
> (entrywise products). Equivalently, `Z₊` is the space of spline jump
> assignments mod constants; equivalently again, with `π : K^{E_A} → H₁(H₊)`
> the quotient by the cut space, `H_X := π(K^X)` and
> `ℓ_X := span(1, t_X, t_X²) ⊂ K³`,
>
> `dim Z₊ = m − dim Σ_X H_X ⊗ ℓ_X`  inside `H₁ ⊗ K³`.
>
> At a **tight balanced** colouring, `2m = 3n_c − 3` and
> `dim(H₁ ⊗ K³) = 3h = m`, so: **target rank ⟺ Z₊ = Z₋ = 0 ⟺ the class
> subspaces `H_X ⊗ ℓ_X` fill `H₁ ⊗ K³` exactly.**

*Proof.* Rank–nullity: `rank(DN₊) = 3n_c − dim(splines)`, and
`splines / constants ≅ Z₊` by reading off jumps (`c_e` = the coefficient of
`(t − s_e)²` in `q_u − q_w`); membership of the jump vector in the
coboundary space is, coefficient-by-coefficient in `t`, the condition
`c, sc, s²c ⊥ cycle space = cut membership`. The tensor form is the same
kernel computed through `π` class-by-class. ∎ The driver computes the two
sides through genuinely different matrices (the eigen-block rref over `ℚ(i)`
with the actual conic directions vs. the `3h × m` rational cycle/parameter
matrix) and finds them equal at all 688 legal both-forest colouring-blocks
of the five-shape pool (`ds-K4`, `ds-(K5−M)`, θ(2,5,5), θ(3,4,5), θ(4,4,4)).

**Balance check.** `2m ≥ 3n_c − 3` with equality iff the colouring is
balanced at a tight shape — so (AC-4)(i) is the *square count* of the
direction network, and any row dependency costs target rank exactly.

### Step G2 — (GR-2): the gap-map statement is refuted; the mechanism is a bond inside one class

> **(GR-2)** *(refuted/proven; driver `--mech`)* "(AC-4)(i)–(ii) ⟹ both
> blocks isostatic" is **false**. At `ds-K4`: of 20 balanced colourings with
> both classes forests, **8 sit at rank 89**, every one carrying a
> **monochromatic hub**; the 12 filter-passing ones (adding: no
> monochromatic hub) are exactly the 12 target-rank colourings of the
> pinned (AC-6) sweep. The mechanism, in both languages: all hinges at a
> monochromatic hub are **one projective line** (they share the hub's
> ruling component), so the body is a **free rotor** about it — dually, the
> hub's star cut is a **bond of `H₊` lying inside a single class** `X`, and
> any cut vector `c` supported inside one class has `s·c = t_X·c`, so
> `c ∈ Z₊` survives the parameter conditions that kill every generic cut
> vector.

Relation to (AC-9), stated so the two do not blur: *every* body of degree
≥ 3 in *any* σ-fixed configuration carries a coincident hinge **pair**
(pigeonhole against the two rulings — (AC-9)); a pair costs no rank, which
is why (AC-3) reaches the target anyway. Rank is lost exactly when the
coincidence is **total** at a body — all its hinges one line — which is the
monochromatic-hub case; (GR-2) is thus the rank-costing boundary case of
(AC-9), and the filter's no-monochromatic-hub clause is its exclusion.

### Step G3 — (GR-3): two proven counting obstructions, mutually non-subsuming

> **(GR-3)** *(proven)* For any legal colouring with the other class a
> forest, `dim Z₊` is bounded below by each of:
>
> **(a) class-cut defects.** `Z₊ ⊇ ⊕_X (cut(H₊) ∩ K^X)`, of dimension
> `Σ_X (comp(G ∖ X) − 1)` — a nonzero term exactly when deleting the edges
> of the single class `X` disconnects `G`. *(The monochromatic hub is the
> case `X = the star of a hub`.)*
>
> **(b) class-union counts.** For every union `F` of classes:
> `dim Z₊ ≥ |F| − 3·dim H_F` with `dim H_F = |F| − comp(G ∖ F) + 1`; so
> `Z₊ = 0` requires **`3(comp(G∖F) − 1) ≤ 2|F|` for every union of ruling-A
> classes** (and dually for `B`).
>
> **(c) contracted sparsity.** For every node subset `S` of `H₊` with
> `e_in(S)` induced edges: `rank(DN₊) ≤ 2(m − e_in) + 3|S| − 3·comp(S)`,
> hence `dim Z₊ ≥ (3n_c − 3) − 2m + 2·e_in(S) − 3|S| + 3·comp(S)`. At a
> tight **balanced** colouring (`2m = 3n_c − 3`) this says `Z₊ = 0`
> requires the class-blind `(2,3)`-count **`2·e_in(S) ≤ 3|S| − 3·comp(S)`
> for every `S`**, whose sharpest failure witness is a **mixed digon**: a
> cycle of `G` with exactly two `A`-edges from *different* classes (its
> `B`-arcs contract to two nodes, so four rows act on one 3-dimensional
> difference space).
>
> None of the three subsumes another: the monochromatic hub violates (a)
> but neither count; the mixed digon violates (c) but neither (a) nor (b);
> the global balance count is (b) at `F = E_A`.

*Proofs.* (a): supports over distinct classes are disjoint and each vector
is an `s`-eigenvector, as in (GR-2). (b): the restriction of the tensor map
to `⊕_{X⊆F} K^X` has image inside `H_F ⊗ K³`. (c): the rows split into the
`e_in(S)` induced ones (killing the constants of each induced component)
and the rest. ∎

### Step G4 — (GR-4): at generic parameters the two families are exact — and the concrete construction's parameters are NOT generic

> **(GR-4)** *(conjectured in general; **exact at all 688 pool instances**,
> driver `--counts`)* At generic per-class parameters,
> `dim Z = max(bound (a), bound (b), bound (c), 0)`, for both blocks.

Two measured facts sharpen this.

1. **Label genericity is real and cheap to miss.** The concrete recipe
   (`closure.build_fixed_config`) uses component indices as ruling
   parameters. At 10 of the 688 pool instances that *specific* parameter
   point overshoots the generic `dim Z` by 1 (first flagged as a possible
   "conic-specific third mechanism"; re-testing at seeded random rational
   parameters collapses all 10 to the bound — a special-value artifact).
   Consequence, binding on any future use: **a rank miss of the literal
   construction at one parameter point is not a miss of the recipe** — the
   census (Step G5) retries every miss at random parameter draws before
   calling it structural.
2. **On filter-passing colourings the criterion is trivially met on the
   pool**: all 62 legal filter-passing pool colourings have generic
   `dim Z₊ = dim Z₋ = 0` (both blocks; measured). So on the pool the
   filter (balance + both forests + no monochromatic hub + distinct
   bodies) is already sufficient — but (GR-3)(c)'s mixed digon shows it
   cannot be sufficient in general, and the counts are the correct
   hypothesis.

**Why (GR-4) is stated as a conjecture, precisely.** The ≥ direction is
(GR-3). The ≤ direction is a generic-arrangement statement of matroid-union
type: for *fully generic* lines `ℓ_X ⊂ K³` and singleton classes it is the
classical realization of the 3-fold union of the linear matroid of
`{π(δ_e)}` (matroid union: Edmonds; the tensor-realization argument is the
one used for body-bar frameworks, cf. Whiteley, *Some matroids from
discrete applied geometry*, in *Matroid Theory*, Contemp. Math. **197**
(1996), 171–311, whose subjects include exactly the parallel-drawing and
cofactor matroids these direction networks and splines sit between). Two
genuine gaps separate that from (GR-4): (i) the class
structure (repeated `ℓ` within a class) is *not* the free union — it is
exactly what lets the class-cut family (a) survive; (ii) the lines are
confined to the **conic**, and the moment curve contains only two of the
three coordinate directions a partition-specialization proof would use, so
the standard specialization argument needs a valuation/degeneration
refinement. The pool evidence (688/688, including every unbalanced and
every count-violating colouring) is that neither gap changes the answer.
*(Superseded in two directions by Steps G8–G11, 2026-08-06, direction G:
gap (ii) is DISSOLVED — any three distinct moment-curve points form a basis
of `K³`, so the partition-specialization step works on the conic verbatim —
and the equality conjecture is REFUTED as stated and repaired as (GR-4′),
which the discharge path no longer consumes.)*

### Step G5 — the census: 907/907, no kill

> *(driver `--census`, seed 20260806, probe cap 48 filter-passing
> colourings/shape, early exit at the first legal target-rank hit, every
> non-hit retried at 3 random parameter draws)* Over **907 tight class
> shapes** — the three tight thetas (θ(2,5,5) **new**, not in §(K-clos)'s
> pinned 21-shape pool; θ(3,4,5); θ(4,4,4)), the **exhaustive `K4`
> stratum** (every length assignment in `{1..5}⁶` summing to 18 with a
> length-3 split edge that passes the class predicate `shape_ok`), and a
> seeded `|V°| ≤ 5` / `|V°| = 6` sweep of `kslidecomb.candidate_graphs` —
> **an admissible target-rank nondegenerate colouring exists at every
> shape**: 907/907, no misses, structural or otherwise. First-hit
> histogram: 835 shapes hit at the first filter-passing colouring, 60 at
> the second, 9/2/1 at the third/fourth/fifth.

Read with the right polarity: this is the ∃-per-shape statement (the
recipe's), tested against `hK`'s own habitat predicates (`shape_ok` =
tight + `def = 0` + `hnoRigid`; `hcard` and no-two-hub-triangle asserted
per shape). It extends §(K-clos)'s 15/15 by two orders of magnitude and
adds the previously unprobed θ(2,5,5). It is **not** a proof, and the
∀-colouring question is settled *negatively* by (GR-2) — existence of a
*good* colouring is the right open form, named (GR-6) below.

### Step G6 — (GR-5): chart-image membership, proven and verified — `hK`'s conclusion object is reached

`hK`'s conclusion (`Escape.lean:555`) asks for `∃ hubSel q s` with
`hubSel w` a correct `Fin 3`-selector of `closedHubNbhd w` at every body,
`s ⊆ E(G) × (…)²`, `|s| = 6(|V|−1) − def`, and the `pencilRow hubSel
G.endsOf q` family linearly independent on `s`. `pencilRow` reads **only**
the chart's constructed points (`Engine.lean:318`: `hingeRow ∘ annihRow` of
`extensor ![point u, point v]`); normals never enter it, and nondegeneracy
is not required.

> **(GR-5)** *(proven-informally, class-uniformly; machine-verified at 5
> shapes, driver `--chart`)* Let `G` satisfy `hcard` and let `pt` be a
> σ-fixed grid configuration from an admissible colouring (all bodies
> distinct) such that at every body `v` the point set
> `{pt_w : w ∈ closedHubNbhd(v)}` is linearly independent. Then there are
> `hubSel` and an explicit seed `q` over `ℚ(i)` with
>
> `pencilChartPoint (PencilSeed.ofCoord q) hubSel v ∝ pt_v` at **every**
> body, and `pencilChartNormal … v ∝ pt_v` (= the σ-fixed normal) at every
> body.
>
> Consequently the `pencilRow` family at `q` has the same rank as the
> configuration's body-hinge matrix; at a target-rank grid this **is**
> `hK`'s conclusion at `G` over `ℚ(i) ⊆ ℂ̄` — and over every infinite
> characteristic-0 field, since the certifying maximal minor is a
> `ℤ`-coefficient polynomial in the seed ((AC-7)'s argument, applied
> per-shape).

*Proof.* Take `hubNormal w := pt_w` (read only at hubs, since
`closedHubNbhd` contains only hubs). At any body `v`, every selected input
of the point construction lies in the 3-space `pt_v^⊥`: `pt_v` itself
because grid points are isotropic, and each hub-neighbour's `pt_w` because
adjacent grid points are conjugate ((AC-2)); `hcard` caps the selected
inputs at 3, and the LI hypothesis lets the unused slots be filled inside
`pt_v^⊥` keeping the triple independent (`fillHub`). `cross₃ x y z`
represents `w ↦ det[x,y,z,w]`, so it spans the 1-dimensional
`{x,y,z}^⊥` (nonzero by `cross₃_ne_zero_iff_linearIndependent`), which
contains `pt_v` — hence `∝ pt_v`. For normals: at a hub the chart returns
the seed's `hubNormal v = pt_v`; at a non-hub (degree 2, closed
neighbourhood of exactly 3 members on a 2-edge-connected class shape) it
returns `cross₃` of the three neighbouring chart points
`∝ cross₃(pt_v, pt_u, pt_w) ∝ pt_v` by the same isotropy/conjugacy
argument, the star-rank-3 condition supplying the LI. Rank transfer:
per-body scalars rescale each `pencilRow` row by a nonzero factor
(`annihRow` is linear in the extensor, the extensor bilinear in the
points), preserving linear independence; the per-edge row spans of the
harness's rigidity builder and of `annihRow` are both the full 5-dimensional
annihilator of the hinge extensor — the Lean side by the landed
`span_annihRow_eq_dualAnnihilator` (`PanelLayer.lean`) composed with
`hingeRow u v r = r(S u − S v)` (`RigidityMatrix/Basic.lean:494`), the
harness side by `perp_basis` coordinatizing the same annihilator through the
Euclidean pairing — so the ranks agree. The `ofCoord`
coupling `fillNbr = fillHub` (`Engine.lean`) is vacuous here: `nbrSel`
leaves no slot unassigned at a non-hub, and is never read at a hub. ∎

The driver verifies, at the first target colouring of each of the five pool
shapes: selector correctness (the three `IsFin3SelectorOf` clauses),
proportionality of the *chart-built* point and normal to the grid data at
every body, and — the end-to-end check — that the rigidity matrix rebuilt
**from the chart output** has rank exactly the Tay target (`ds-K4` 90,
`ds-(K5−M)` 120, the three thetas 60). §(K-clos) *Step Z6*'s "argued, not
verified" clause is retired; the second small-Lean-spike instrument named
there is no longer needed at the informal tier.

**Witness class, per (AC-9)'s discipline:** every configuration here is
σ-fixed, hence never composite-guard generic; every claim above is an
existence witness or an exact identity — no rates are quoted, and
rank-attainment at a σ-fixed point certifies the generic chart rank by
lower semicontinuity.

### Step G7 — what remains, named exactly: (GR-6)

> **(GR-6)** *(open — the tight-stratum residual in its final combinatorial
> form)* At every tight class shape there exists an admissible ruling
> colouring — alternating at degree-2 bodies, all bodies distinct, balanced,
> both classes forests — satisfying (GR-3)(a)/(b)/(c) in both blocks.

Together with (GR-4), (GR-6) implies target rank at every tight class
shape; with (GR-5) and (AC-7), that discharges `hK` on the tight stratum
over every infinite characteristic-0 field. Both remaining gaps are
geometry-free: (GR-4) is a generic-arrangement/matroid-union statement,
(GR-6) a colouring-existence statement whose counts are Nash-Williams/
Edmonds-shaped (the packing side of the arc already lives in Phases 12–15
machinery, cf. §(K-slide-comb) (C6)). Evidence for (GR-6): 907/907 with
first-hit concentrated at the first filter-passing colouring — the good
colourings are not rare. The honest caveat cuts the other way: every
class-uniform *combinatorial-existence* claim this arc has previously
relied on has eventually been either proven by a min-max or refuted by a
parity/chromatic flank ((AC-6) itself, (K-slide-comb)); (GR-6) has no
min-max yet, and until it does the base-rate warning of
`Pencil-strategy.md` §2.3 applies to it.
*(Merged into **(GR-10)** — Step G11, 2026-08-06, direction G — which
strengthens the colouring target from "(GR-3) holds" to "tree-triple
certificates in both blocks" and in exchange deletes the (GR-4)
dependency entirely.)*

### Verification

`notes/scripts/w4/grid.py` (**new with this section**; imports `closure.py`
and the catalogued §1 primitives read-only; exact ℚ and ℚ(i); the census
rng and the generic-label draws seeded, seeds printed; no `set` printed).
Every sampled object carries the standing guards (isotropy, conjugacy,
eigen-sign, span dimensions) through `closure.probe`/`extensors`.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --mech      # 1 s   (GR-2): 20 balanced-forest / 8 below target / 8 mono-hub; 12 filter-passing = the pinned sweep's 12
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --spline    # 21 s  (GR-1): rank identity, 688/688
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --counts    # 6 s   (GR-3)/(GR-4): 688/688 at generic labels; 10 construction-label overshoots; filter-passing 62/62
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --census    # 86 s  907/907 (877 K4 + 6 V5 + 21 V6 + 3 theta); first-hit histogram 1:835, 2:60, 3:9, 4:2, 5:1
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --chart     # 6 s   (GR-5): 5/5 end-to-end through the landed chart constructions
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --validate  # all five (~2 min)
```

*Confidence verdict.* **(GR-1) proven** (informal proof + 688/688 exact
identity). **(GR-2) proven refutation** of the gap-map sentence, mechanism
complete on the pool. **(GR-3) proven.** **(GR-4) true-modulo-named-gap**
(the ≤ direction at conic labels; exact at every censused instance).
**(GR-5) proven-informally** class-uniformly, machine-verified at 5 shapes
(the Lean-tier transcription remains future work, as for every section of
this workbook). **(GR-6) open**, with 907/907 evidence. The tight-stratum
question of (AC-6) is thereby **reduced, with proven reductions, to
(GR-4) + (GR-6)**; nothing here re-opens the habitat-level refutation
(`C11` is permanent).

*What would change this.* (i) A tight class shape where the census's
early-exit + random-parameter retry finds no target colouring — refutes
(GR-6) and the tight-stratum residual with it. (ii) A colouring-block
anywhere with generic `dim Z` strictly above the (GR-3) max — a third
obstruction family, refuting (GR-4) as stated. (iii) A proof of (GR-4)
(most plausibly: the matroid-union tensor realization pushed through the
moment-curve confinement by a valuation argument) — upgrades the criterion
to a theorem. (iv) A min-max proof of (GR-6) — closes the tight stratum,
and with it `hK` there, over every infinite characteristic-0 field.

### Steps G8–G13 (2026-08-06, fan-out direction G) — the (GR-4) refutation and repair, the tree-triple certificate theorem, and the merged residual (GR-10)

Driver `notes/scripts/w4/gridwit.py` (imports `grid.py` and `closure.py`
read-only), new this pass; labels **(GR-7)–(GR-11)** plus the primed
successor **(GR-4′)** (per the (Λ0f′) precedent). §(K-pack) was **not**
opened — everything fits this section's own family. Everything cited that
this pass did not mint is qualified: (C6) is §(K-slide-comb)'s; (AC-4)/
(AC-7)/(AC-9) are §(K-clos)'s; (ANH-9)/(ANH-14) are §(K-ann)'s; (OC-16) is
§(K-out)'s.

**Headline, stated before the mathematics.**

- **Cheap kill (ii) FIRES — (GR-4) is REFUTED as stated, and repaired in the
  same pass.** On a widened colouring pool (176 shapes, 4200 legal
  both-forest colouring-blocks, including non-filter-passing ones), generic
  `dim Z` strictly exceeds max((GR-3)(a),(b),(c)) at **185 blocks** — 59 of
  them on filter-passing colourings. All 185 are explained **exactly** by one
  proven unified obstruction family ((GR-8): sub-multigraph cycle spaces),
  of which (GR-3)(b) and (c) are the two boundary cases; the rank-1 mechanism
  is characterized in closed form — **a cycle of the contracted multigraph
  whose edges lie in at most two classes** — and the workbook's mixed digon
  is its 2-edge special case.
- **The discharge path no longer needs (GR-4).** A **tree-triple certificate
  theorem** ((GR-9), proven): if a legal alternating colouring's classes
  partition, in both blocks, into three groups whose pairwise unions are
  spanning trees of the contracted multigraph, then the grid reaches the Tay
  target at generic parameters — no generic-arrangement statement consumed.
  The proof is the valuation/degeneration refinement *What would change this*
  item (iii) predicted, in its simplest instance: collapse the class
  parameters to three values (legitimate by semicontinuity), invert a
  Vandermonde, observe that no group contains a bond.
- **(GR-4)-instances and (GR-6) merge into ONE geometry-free residual**
  ((GR-10), open): every tight class shape admits an admissible colouring
  carrying tree-triple certificates in both blocks. Measured **907/907** over
  the full census pool, first-certified histogram concentrated at the first
  filter-passing colouring (859/907). The certificate *implies* every
  filter condition (balance, both forests, no monochromatic hub) and implies
  (GR-3) throughout, so (GR-10) is stated over plain admissible colourings.
- **The min-max obstruction is named exactly.** Group-independence ("the
  union of the group's classes is independent in the bond matroid of `H₊`")
  is **not** a matroid on the classes — the exchange axiom fails at an
  explicit 4-element example — so Edmonds' partition theorem does not apply
  off the shelf; (GR-10) is a *partition-constrained* base packing, one
  grouping constraint away from §(K-slide-comb) (C6)'s reachable machinery.
  Until a min-max exists, `Pencil-strategy.md` §2.3's base-rate warning
  applies to (GR-10) exactly as it did to (GR-6).
- **The §2.3 prediction lands on its informative branch.** The strategy doc's
  blockquote predicted a third independent route would terminate on a rank
  lower bound over a contraction of `H`. Direction G's residual is **not** of
  that shape: it is a colouring-existence statement on `G` itself, with the
  geometry fully discharged by (GR-9) wherever the colouring exists. Per the
  prediction's own terms, that is the outcome that deserves attention.

Notation as in Steps G1–G7: one colouring-block at a time; `H₊ = G/E_B` the
contracted multigraph (connected, no loops, no same-class parallel pairs at a
legal colouring), `n_c` nodes, `m = |E_A|` edges partitioned into classes `X`
(the ruling-A components), `h = m − n_c + 1` the cycle rank, `π : K^{E_A} →
H₁` the quotient by the cut space, `H_X = π(K^X)`, `s : E_A → K` the
class-parameter function, `Z = {c : c, sc, s²c ∈ cut(H₊)}`. Everything
dualizes with `A ↔ B`.

### Step G8 — (GR-7): the interpolation factorization of the deficit

> **(GR-7)** *(proven; driver `gridwit.py --formula`, 1376/1376 exact at
> construction and at random labels)* Let
> `a := Σ_X dim(cut(H₊) ∩ K^X)` and `M := Σ_X dim H_X = m − a`. Then, at
> every parameter assignment (no genericity),
>
> `dim Z = a + (M − 3h) + dim W`,
>
> where `W` is the **interpolation space**: triples `(φ₀, φ₁, φ₂)` of
> cycle-space vectors of `H₊` such that the polynomial
> `Ψ(t) = φ₀ + tφ₁ + t²φ₂` satisfies `Ψ(t_X)_e = 0` for every class `X` and
> every edge `e ∈ X` — vector-valued quadratics through prescribed
> subspaces at the class parameters.

*Proof.* `Z` is the kernel of `ψ : K^{E_A} → H₁ ⊗ K³`,
`c ↦ Σ_e c_e·π(δ_e) ⊗ (1, s_e, s_e²)` (Step G1's tensor form). `ψ` factors
as `Φ ∘ ρ` with `ρ : ⊕_X K^X → ⊕_X H_X` the per-class `π` (surjective,
kernel `⊕_X (cut ∩ K^X)` of dimension `a`) and
`Φ((u_X)) = Σ_X u_X ⊗ d(t_X)`, so `dim Z = a + dim ker Φ` and
`dim ker Φ = M − dim Σ_X H_X ⊗ ℓ_X`. The annihilator of the image inside
`(H₁ ⊗ K³)* = H₁* ⊗ (K³)*`: identify `H₁*` with the cycle space by the
standard pairing (`⟨γ, πδ_e⟩ = γ_e`) and `(K³)*`-components with polynomial
coefficients; a functional `(φ₀, φ₁, φ₂)` kills `H_X ⊗ d(t_X)` iff
`(φ₀ + t_Xφ₁ + t_X²φ₂)` kills `H_X` iff its edge-coordinates vanish on `X`.
So `dim Σ = 3h − dim W`, and `dim Z = a + M − 3h + dim W`. ∎

Two remarks that power everything below. **(i) Semicontinuity.** The matrix
of `Z` (and of `W`) is polynomial in the parameters, so `dim Z` at *any*
assignment — collisions included — is `≥` its generic value; in particular
**one exact rational point with `dim Z = 0` proves generic vanishing**. (The
census's exact hits were therefore already per-shape *proofs* of the generic
statement, the τ-side analogue of §(K-ann) (ANH-9)'s one-point decidability;
what was missing was uniformity, not rigor.) **(ii) The `P¹` reading,
recorded for the literature interface.** `W = H⁰(P¹, E)` for `E` the
elementary modification (Hecke transform) of `O(2) ⊗ H₁*` at the points
`t_X` along the subspaces `H_X^⊥`; `χ(E) = 3h − M`, so (GR-7) says the
deficit beyond `a` is `h¹`-jumping of a generic modification along the
*cographic* arrangement, and (GR-4)-type statements are statements about
generic splitting types (Grothendieck's splitting theorem is the classical
backdrop). Nothing below uses this language; it locates the problem.

### Step G9 — (GR-8): one obstruction family instead of two; the (GR-4) refutation and its repair

> **(GR-8)** *(proven)* For every sub-multigraph `P` of `H₊`, with `C(P)`
> its cycle space and, for each class `X`,
> `r_X(P) := dim C(P) − dim C(P ∖ X)`:
>
> `dim W ≥ g(P) := 3·dim C(P) − Σ_X r_X(P)`,
>
> hence by (GR-7) `dim Z ≥ a + (M − 3h) + g(P)`. The family subsumes
> (GR-3)(b) and (GR-3)(c). Its rank-1 members are characterized exactly:
> a 1-dimensional witness exists iff `H₊` has a **cycle meeting at most two
> classes** — the mixed digon of (GR-3)(c) is the case of two parallel
> edges.

*Proof of the bound.* Take `Ψ` with all `φ_p ∈ C(P)`. Coordinates off
`E(P)` vanish identically, so only classes meeting `P` impose conditions;
class `X` imposes `Ψ(t_X)|_{K^{X∩E(P)}} = 0`, a system of rank
`≤ dim C(P) − dim ker` on each of the three... on the value `Ψ(t_X) ∈ C(P)`,
where the kernel of the restriction map `C(P) → K^{X∩E(P)}` is exactly
`C(P∖X)`: a cycle vector of `P` supported off `X` is orthogonal to every
cut of `P`, hence to their restrictions, which exhaust the cuts of `P∖X`.
So the conditions number at most `Σ_X r_X(P)` on the `3·dim C(P)`-dimensional
space `C(P)³`. ∎ *Subsumption.* (b) at a class union `F`: take `P` = (all
nodes, edges `∪F`); then `C(P)` is precisely the annihilator of `H_{F^c}`
(cycle vectors supported in `F`), `r_X(P) = 0` off `F`, and unwinding
dimensions reproduces `dim Z ≥ |F| − 3·dim H_F` with slack
`m − M ≥ |F| − M_F`. (c) at a node set `S`: take `P = H₊[S]`; then
`Σ_X r_X(P) ≤ e_in(S)` and `dim C(P) = e_in − |S| + comp(S)` give
`g(P) ≥ 2e_in − 3|S| + 3·comp(S)`, and `a + M = m` turns (GR-7) into
(GR-3)(c)'s general form. ∎ *Rank-1 members.* A 1-dimensional space of
witnesses valued in a line `⟨γ⟩` is `Ψ = p(t)·γ` with `p` of degree ≤ 2
vanishing at `t_X` for every class `X` with `γ_e ≠ 0` somewhere on `X`;
a nonzero `p` has at most two roots, so `γ` (which one may take a single
cycle) meets at most two classes — and conversely any such cycle gives
`p = (t − t_X)(t − t_Y)`. ∎

> **Refutation of (GR-4) as stated** *(measured; driver `--wide`, seed
> 20260806)*. Over 176 census shapes × ≤ 12 legal both-forest colourings
> (4200 blocks, non-filter-passing included): generic `dim Z` **strictly
> exceeds** max((GR-3)(a),(b),(c)) at **185 blocks** — 59 of them
> filter-passing — every candidate confirmed at 8 extra parameter draws.
> **All 185 equal the (GR-8) maximum exactly; zero remain unexplained.**
> Smallest exemplar (`K4(1,1,5,5,3,3)`, B block): a 6-edge cycle of `H₊`
> meeting exactly two classes (2 + 4 edges, `r_X = 1` each),
> `g = 3·1 − 2 = 1 > 0` where all of (GR-3) sees `1` against a measured
> generic `dim Z = 2`. The 5-shape pool could not see this: at its 688
> blocks the (GR-8) maximum coincides with max((GR-3)) (688/688,
> `--formula`) — the two-class-confined long cycles need the widened
> length profiles.

> **(GR-4′)** *(the repaired equality; conjectured in general, exact at all
> 688 + 4200 probed blocks)* At generic per-class parameters,
> `dim Z = a + (M − 3h) + max(0, max_P g(P))`, `P` over sub-multigraphs
> of `H₊`.

What is proven toward (GR-4′), beyond `≥`: **(i) at most three classes**
(then `Σ` is a direct sum by independence of any ≤ 3 moment-curve points,
and `max g` is attained at `P = H₊`); **(ii) singleton classes** (the free
case): the classical 3-fold matroid-union tensor realization goes through
**on the conic verbatim**, because the partition-specialization step needs
only three distinct conic points, and any three distinct points of the
moment curve form a basis of `K³` (matroid partition/union: Edmonds,
*Minimum partition of a matroid into independent subsets*, J. Res. Nat.
Bur. Standards 69B (1965) 67–72; the tensor argument as in the Whiteley
reference already cited at Step G4). This **dissolves Step G4's named gap
(ii)** — the "only two of the three coordinate directions" worry — for
every argument that specializes to at most three simultaneous values; the
live gap in (GR-4′) is only the class structure, and in sheaf terms it is
the difference between constant-coefficient witnesses (the (GR-8) family)
and *moving* ones (general subsheaves — every `h⁰` jump on `P¹` is
witnessed by a subsheaf of positive Euler characteristic, but not
necessarily by a constant one). Since the discharge path below no longer
consumes (GR-4′), its resolution is **off the critical path**.

### Step G10 — (GR-9): the tree-triple certificate theorem

> **(GR-9)** *(proven; driver `--treetriple` asserts the consequence at
> every certified shape, 907/907, 0 failures)* Let a legal colouring-block
> (other class a forest) admit a partition of its classes into three groups
> `F₁, F₂, F₃` such that `H₊ ∖ F_j` is connected for each `j`. Then
> `dim Z = 0` at generic parameters. At a tight balanced block the
> condition is equivalent to: **the three pairwise unions
> `F_i ∪ F_j (i ≠ j)` are spanning trees of `H₊`** (each edge lying in
> exactly two of the three trees), and a legal alternating colouring
> carrying such a partition in **both** blocks reaches the Tay target
> `6(|V|−1)` at every generic parameter draw; consequently — via (GR-5) and
> §(K-clos) (AC-7) — `hK`'s conclusion holds at that shape over every
> infinite characteristic-0 field.

*Proof.* Specialize the parameters to three distinct values: `s_X := a_j`
for `X ∈ F_j` (a legitimate comparison point by (GR-7) remark (i) —
collisions allowed, since only the generic value is being bounded from
above). Let `c ∈ Z` at this assignment and write `c = c₁ + c₂ + c₃` with
`c_j` supported on `F_j`'s edges. The conditions `Σ_j a_j^p c_j ∈ cut(H₊)`
for `p = 0, 1, 2` and the invertibility of the 3×3 Vandermonde in
`(a₁, a₂, a₃)` give `c_j ∈ cut(H₊)` for each `j`. A nonzero cut vector
supported inside `F_j` contains a bond of `H₊` in its support, i.e.
`H₊ ∖ F_j` is disconnected — excluded. So `c_j = 0`, `Z = 0` at the
collapsed point, and generically. *Equivalence at a tight balanced block:*
`H₊ ∖ F_j = F_i ∪ F_k` connected needs `≥ n_c − 1` edges; summing the three
gives `2m ≥ 3(n_c − 1)`, which balance makes an equality — so each
complement is connected with exactly `n_c − 1` edges, a spanning tree, and
conversely. *Target rank:* generic `dim Z₊ = dim Z₋ = 0` on the
intersection of two dense opens; pick exact rational parameters there with
all `(p_A, p_B)`-pairs distinct (legality is combinatorial at a legal
colouring plus distinctness of drawn values); (GR-1) gives
`rank_± = 3|E_∓| + 3n_c^± − 3`, which balance turns into `3(|V|−1)` per
block, and §(K-clos) (AC-4)'s decoupling sums them to the Tay target.
Chart membership and field descent are (GR-5) and (AC-7), quoted. ∎

Three consequences worth stating plainly. **(i) The certificate implies the
whole filter.** A monochromatic hub is a star bond inside one class, hence
inside one group — contradiction; a cycle inside one class lies inside both
pair-unions containing that class — contradiction; and the spanning-tree
count *is* balance. So certificate-existence may be quantified over plain
admissible (legal, alternating) colourings. **(ii) It implies (GR-3) and
(GR-8) vanish** (via `dim Z = 0` and the proven `≥`). **(iii) It consumes
no generic-arrangement statement**: (GR-4)/(GR-4′) is bypassed, not
assumed. The certificate is sufficient, not necessary — blocks with
`dim Z = 0` and no tree-triple exist already at `h = 1` in principle — so
(GR-10) below asks for more than vanishing, and buys a purely combinatorial
target in exchange.

### Step G11 — (GR-10): the merged residual, and what its min-max needs

> **(GR-10)** *(open — the tight-stratum residual in its new, single-
> statement form; measured 907/907)* Every tight class shape admits an
> admissible ruling colouring whose classes partition, in **both** blocks,
> into three groups with pairwise-union spanning trees of the respective
> contracted multigraph.

(GR-10) implies (GR-6) (the certificate implies the counts) and supplies
every instance of (GR-4) the discharge ever needed; with (GR-9), (GR-5) and
§(K-clos) (AC-7) it discharges `hK` on the tight stratum over every
infinite characteristic-0 field. **Evidence** (`--treetriple`, seed
20260806): over the full census pool — 877 exhaustive `K4`-stratum shapes,
6 + 21 sweep shapes, 3 tight thetas — a filter-passing colouring carrying
both-block certificates exists at **907/907**, found at the *first*
filter-passing colouring at 859 shapes (2nd: 44, 3rd: 2, 5th: 1, 8th: 1);
at every certified shape the driver re-verified the Tay target at a seeded
rational draw (the (GR-9) assertion, 0 failures).

**Why this is not yet Edmonds, exactly.** Call a set of classes
*co-independent* when the union of its edges is independent in the bond
matroid of `H₊` (equivalently: deleting it leaves `H₊` connected...
deleting it costs no connectivity, i.e. its union contains no bond). The
certificate is a partition of the class set into three co-independent
groups. But co-independence of *grouped* elements is not a matroid on the
classes: in `U_{2,4}` on `{1,2,3,4}` with classes `{1}, {2}, {3,4}`, the
sets `{{1},{2}}` and `{{3,4}}` are both co-independent... both independent
in the induced sense, yet neither element of the first extends the second
— the exchange axiom fails. So (GR-10) is a **partition-constrained base
packing** (each part must be a union of prescribed classes), for which
Edmonds' partition theorem and the Nash-Williams/Tutte pair (Nash-Williams,
*Edge-disjoint spanning trees of finite graphs*, J. London Math. Soc. 36
(1961) 445–450; Tutte, *On the problem of decomposing a graph into n
connected factors*, same volume, 221–230) supply the unconstrained
prototype but no off-the-shelf min-max; without the class constraint the
packing side is exactly the reachable territory §(K-slide-comb) (C6) lives
in (Phases 12–15 machinery). The necessary conditions (GR-3)(b) supplies —
`3(comp(G∖F) − 1) ≤ 2|F|` over class unions — are the natural min side; whether
they (plus admissibility) are sufficient at tight shapes **is** the open
question, and until a min-max exists `Pencil-strategy.md` §2.3's base-rate
warning applies to (GR-10) verbatim: every prior class-uniform
combinatorial-existence claim of this arc was eventually either proven by a
min-max or refuted by a structural flank ((AC-6)'s parity flank `C11`,
§(K-slide-comb)'s two flanks). The flank to hunt here: a tight shape whose
*every* admissible colouring leaves, in some block, a group-obstructing
pattern — none surfaced in 907 shapes.

> **(GR-11)** *(proven; the fallback if a shape ever misses)* Generic
> `dim Z` is bounded above by `dim Z` computed over `K((ε))` at **any**
> ε-adic parameter assignment `t_X = b_X + c_X ε^{v_X}` (semicontinuity at
> a `K((ε))`-point), and the leading-order analysis of a putative nonzero
> solution recurses: the order-0 system is the three-point collapse of
> (GR-9)'s proof, and the order-1 obstruction at each collapse point is the
> **degree-1** interpolation problem in the classes assigned to that point.
> So certificates refine hierarchically (a 3-way tree of collapses, one
> degree lost per level) — the general "valuation/degeneration refinement"
> of Step G4 item (iii), made precise. Not developed further: 907/907 left
> nothing for it to do.

### Step G12 — the shape of (GR-10) as a finite object (structure notes for a future min-max)

All proven, all elementary; recorded so a §(K-pack)-style development can
start from the right object. (i) Admissible colourings are exactly one free
bit per **branch** of `G` (alternation chains = branches; hubs break
chains; a tight shape has hubs, so no odd-cycle obstruction —
`closure.alternation_classes` is the landed form). (ii) A monochromatic
cycle visits only hubs, so "both classes forests" constrains only the
hub-hub (length-1-branch) subgraph of `G°`. (iii) Balance is a signed
subset-sum over the odd-length branches (even branches are phase-neutral).
(iv) Classes are the colour-components; their interaction with `H₊` is
determined by `(G°, length profile, phase vector)`. Hence (GR-10) is, per
hub multigraph `G°`, a finite CSP parametrized by the length profile — and
the class's infinitude lives entirely in the `G°` direction (§(K-ind)
(I4)), so a min-max must be uniform over `G°`, not over subdivisions.

### Step G13 — convergence rider (note, not a deliverable)

*(Since 2026-08-07 this rider is answered by direction J — §(K-frame): the
lemma shape is (FR-1), both cautions below are discharged, and the transport
works by regridding at `G′`.)*

Directions O and Q terminated on residues of one shape: **chart-to-frame
dominance** — §(K-out) (OC-16): the hard-stratum target-rank locus not
inside `{pt(b) ∈ C₀}` at degree-3 hubs; §(K-ann) (ANH-14): the bare-cycle
stratum's universal degree-12 polynomial nonzero somewhere on the frame's
reachable locus. A single lemma shape would serve both, and this
direction's technology is a candidate supplier for its witness half:
*"an explicit constructed rational point on the relevant stratum, off the
explicit bad divisor, plus irreducibility of the stratum, gives
dominance."* The (GR-5)/(GR-9) grid points are exactly such constructed
witnesses — closed-form, rational, with combinatorially certified rank
properties — and both bad divisors are **evaluable** at them ((OC-16)'s
`Δ = [a,u,b]·C₀(pt b)` is closed-form at degree-3 hubs; (ANH-14)'s `C` is
one universal bracket polynomial). Two cautions bind any such attempt:
the witness must certify through **rank semicontinuity off a divisor**,
never through guard genericity — σ-fixed points are never composite-guard
generic (§(K-clos) (AC-9)) — and the grid points live at the *pencil*
placement of `G`, so serving (OC-16)/(ANH-14) needs the construction
transported to their contracted objects (`H/{e₂,e₃,e₄}`, `H/P − β`), which
is not attempted here. Assessment: evaluability *can* be assessed by one
evaluation battery per residue; irreducibility of the hard-stratum locus is
the ingredient none of the three directions owns. Finally, the record for
`Pencil-strategy.md` §2.3's prediction: direction G's residual (GR-10) is
**not** a rank lower bound on a contraction of `H` — the geometry is fully
discharged by (GR-9) wherever the colouring exists — so the prediction's
"genuinely informative" branch is the one that fired, and the productive
question it points at is the partition-constrained packing, not the wall.

### Verification (Steps G8–G13)

`notes/scripts/w4/gridwit.py` (**new with this pass**; imports `grid.py`
and `closure.py` read-only; exact ℚ throughout, ℚ(i) only inside closure's
rank probes; rngs seeded per mode, seeds printed; no `set` printed; σ-fixed
configurations are constructed existence witnesses — nothing is quoted as a
rate over sampled placements, so `repin.star_generic` does not bind any
figure here, per §(K-clos) (AC-9)'s discipline).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --formula    # 11 s   (GR-7) 1376/1376; (GR-8) max == max((a),(b),(c)) at all 688 pool blocks
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --treetriple # ~5 min (GR-9)/(GR-10): 907/907 both-block certificates; first-certified 1:859, 2:44, 3:2, 5:1, 8:1; target rank asserted at every certified shape
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --wide       # ~3.5 min  cheap kill (ii): 185/4200 overshoots (59 filter-passing), 185/185 = the (GR-8) max, 0 unexplained
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridwit.py --validate   # all three, ~8.5 min total
```

*Confidence verdict.* **(GR-7) proven** (informal proof + 1376/1376 exact
through two independent matrices). **(GR-8) proven** (the bound, the
subsumption of (GR-3)(b)/(c), and the rank-1 characterization).
**(GR-4) as stated REFUTED** (measured: 185 exact overshoot witnesses with
mechanism; this is the section's own *What would change this* item (ii),
delivered together with its repair). **(GR-4′) true-modulo-named-gap**
(the ≤ direction for ≥ 4 non-singleton classes; proven at ≤ 3 classes and
at singleton classes on the conic; exact at all 4888 probed blocks) — and
**off the critical path**. **(GR-9) proven** (and its testable consequence
asserted at 907 shapes, 0 failures). **(GR-10) open** — the tight-stratum
residual in final form, one statement, geometry-free, 907/907 evidence,
no min-max yet (the grouped-exchange failure is the named obstruction).
**(GR-11) proven**, undeveloped. Nothing here re-opens the habitat-level
(AC-6) refutation (`C11` is permanent), and no σ-fixed witness is read as
generic.

*What would change this.* (i) A tight class shape with **no** admissible
colouring carrying both-block tree-triples — refutes (GR-10); (GR-11)'s
hierarchical certificates and the (GR-4′) route would then both re-enter
the critical path, in that order. (ii) A widened-pool block with generic
`dim Z` strictly above the (GR-8) maximum — a mechanism beyond
sub-multigraph witnesses (a "moving subsheaf"); none in 4888 blocks.
(iii) A min-max for the partition-constrained packing (GR-10) — closes the
tight stratum, and with it `hK` there, over every infinite
characteristic-0 field. (iv) A transport of the grid witness supply to the
contracted objects of §(K-out) (OC-16) / §(K-ann) (ANH-14) — would test
the convergence rider's dominance-lemma shape.

### Steps G14–G18 (2026-08-06, fan-out direction E) — the (GR-10) min-max question, settled at its own level of generality: the counting min side is provably insufficient — on the habitat itself — the grouped packing is NP-complete, and the honest residual re-aims at the weakened (GR-15)

**Headline, stated before the mathematics.**

- **The min-max the dispatch asks for cannot exist as posed.** (GR-10)'s
  inner problem — partition the classes of a balanced block into three
  groups with pairwise-union spanning trees — is **NP-complete** on grouped
  instances at exact balance ((GR-13), an explicit reduction from graph
  3-colourability). An Edmonds-type min-max is a good characterization,
  i.e. membership in NP ∩ coNP; for an NP-complete problem that forces
  NP = coNP. So **no polynomially-checkable min side — (GR-3)(b), the full
  (GR-8) family, or any counting condition whatever — can be sufficient in
  general**, and the fan-out question "is (GR-3)(b) plus admissibility
  sufficient?" is answered **NO** twice over: abstractly by the explicit
  chain `C(K4)` ((GR-13)), and **on the habitat** by 18 real
  filter-passing colouring blocks of two censused tight class shapes
  (Step G16) at which *every* counting obstruction vanishes — generic
  `dim Z = 0`, proven at exact rational points — yet **no tree-triple
  exists**.
- **(GR-10) itself is NOT refuted — and is now measured strictly harder
  than what the discharge needs.** An exhaustive-colouring sweep (no probe
  cap, vs the census's 48) still finds a certified colouring at **every**
  swept shape: 903 shapes, 16600/17772 filter-passing colourings certified,
  scarcest shape 12/16. But per block the tree-triple is **strictly
  stronger than rank attainment** (the separators), so proving (GR-10)
  means proving more than `hK` needs, against a target whose per-block
  theory is NP-complete.
- **The honest residual is minted as (GR-15)**: every tight class shape
  admits an admissible colouring with generic `dim Z₊ = dim Z₋ = 0` in
  both blocks. Implied by (GR-10); discharges `hK` on the tight stratum
  through the same chain ((GR-1) + §(K-clos) (AC-4) assembly, (GR-5)
  membership, (AC-7) descent); **one-point-decidable per shape** (an exact
  rational hit proves generic vanishing by (GR-7) remark (i) — the
  τ-side analogue is §(K-ann) (ANH-9)), so the census's 907/907 exact hits
  already prove it per censused shape. Its per-block min-max question is
  (GR-4′)'s equality — counting-shaped, and **untouched by the hardness
  above** (the separators satisfy (GR-4′) exactly).
- **Two structural by-products, both proven.** (GR-12): at balance the
  tree-triple is equivalent to a partition of the classes into three
  **co-independent** groups (bases of the bond matroid; the size condition
  is automatic), equivalently a 3-colouring of the classes under which
  **every circuit of the contracted multigraph sees ≥ 3 colours** — the
  polychromatic-circuit form the exemplar exhausts — and the necessity of
  `a = 0` plus the whole (GR-8) family is re-derived **purely matroidally**
  (submodularity of graphic rank; no geometry, no (GR-9) detour). (GR-14):
  a second combinatorial rank certificate (an edge-disjoint **rainbow-Δ
  cycle basis** forces `dim W = 0` at every injective parameter point) —
  the proof mechanism behind the (GR-13) chains — whose habitat
  applicability is **measured nil** (0/400 first-certified blocks, 0/18
  separators), recorded so nobody re-hunts it.
- **The §2.3 record.** `Pencil-strategy.md` §2.3's base-rate warning
  predicted every class-uniform combinatorial-existence claim of the arc
  gets proven by a min-max or refuted by a flank. (GR-10) lands on a
  **third branch the arc has not seen before**: not refuted (the sweep is
  exhaustive where it runs), but its min-max is **impossible as posed**,
  and the repair is not a stronger min side but a **weaker target**
  ((GR-15)) for which the min-max question re-opens in counting form.
  The wall here is complexity-theoretic, not a rank bound on a contraction
  of `H` — the "genuinely informative" branch of the strategy doc's
  prediction, for the second time in one fan-out cycle.

Notation as in Steps G1–G13: one balanced legal colouring-block at a time;
`H₊ = G/E_B` (dually `A ↔ B`), `n_c` nodes, `m = |E_A|` edges in classes
`X` (ruling-A components), `h = m − n_c + 1`, balance `2m = 3(n_c − 1)`
(equivalently `3h = m`), `a = Σ_X dim(cut(H₊) ∩ K^X)`,
`Z = {c : c, sc, s²c ∈ cut(H₊)}`, `W` the interpolation space of (GR-7),
`g(P) = 3·dim C(P) − Σ_X r_X(P)` the (GR-8) functional.

### Step G14 — (GR-12): three equivalent forms of the certificate, and the counting necessity made matroidal

> **(GR-12)** *(proven; driver `packmm.py --restate`, 212/212 balanced
> pool blocks, both witness directions cross-validated)* At a tight
> balanced legal block, the following are equivalent:
>
> (i) a tree-triple: a partition of the classes into `F₁, F₂, F₃` with
> every pairwise union `F_i ∪ F_j` a spanning tree of `H₊`;
>
> (ii) a partition of the classes into three **co-independent** groups —
> `H₊ ∖ F_j` connected for each `j` (i.e. each group independent in the
> bond matroid of `H₊`);
>
> (iii) a 3-colouring of the classes under which **every circuit of `H₊`
> sees at least 3 colours** (the polychromatic-circuit form).
>
> Moreover any of these forces `a = 0` and `g(P) ≤ 0` for **every**
> sub-multigraph `P` — the full (GR-8) necessity — by a purely matroidal
> argument.

*Proof.* (i) ⟹ (ii): `H₊ ∖ F_j = F_i ∪ F_k` is a spanning tree, in
particular connected. (ii) ⟹ (i): a co-independent set is independent in
the bond matroid, whose rank is `m − (n_c − 1) = (n_c − 1)/2` at balance;
so `|F_j| ≤ (n_c − 1)/2` for each `j`, and since the three sizes sum to
`m = 3(n_c − 1)/2`, each is **exactly** `(n_c − 1)/2` — the size condition
is automatic. Then `H₊ ∖ F_j` is spanning connected with exactly
`n_c − 1` edges: a spanning tree. (i) ⟺ (iii): `F_i ∪ F_j` acyclic for
all pairs ⟺ no circuit has all its classes inside two groups ⟺ every
circuit sees ≥ 3 groups (a one-colour circuit also lies inside a pair
union). *Necessity.* `a = 0`: a class `X ∈ F_j` containing a bond makes
`H₊ ∖ F_j ⊆ H₊ ∖ X` disconnected. `g(P) ≤ 0`: fix `P`; each `P ∖ F_j` is
a subgraph of the tree `F_i ∪ F_k`, hence acyclic, so the deletion drop
`r_{F_j}(P) := dim C(P) − dim C(P ∖ F_j)` equals `dim C(P)`. Deletion
drops are **subadditive**: `dim C(·)` is supermodular on edge subsets
(`dim C(A) = |A| − r(A)` with `r` the graphic matroid rank, submodular),
and applying supermodularity to `A ∖ X` and `B` for `X ⊆ B ⊆ A` gives
`dim C(B) − dim C(B∖X) ≤ dim C(A) − dim C(A∖X)`; telescoping over the
classes of `F_j` inside `P` yields `r_{F_j}(P) ≤ Σ_{X∈F_j} r_X(P)`.
Summing over `j`: `3·dim C(P) = Σ_j r_{F_j}(P) ≤ Σ_X r_X(P)`, i.e.
`g(P) ≤ 0`. ∎

Two remarks. **(a)** The necessity was previously available only through
the geometry ((GR-9) gives `dim Z = 0`, (GR-8) bounds it below); this
derivation is matroid-theoretic end to end, so it survives into any purely
combinatorial development of the packing question. **(b)** Form (iii) is
the working form: it makes (GR-10)'s inner problem a **polychromatic
hypergraph 3-colouring** (hyperedges = circuit class-sets), which is what
Steps G15–G16 exploit in both directions. The driver checks (i) ⟺ (ii)
by two genuinely independent DFS criteria (acyclicity of pair-unions —
`gridwit.tree_triple` — vs connectivity of complements — `coind_triple`),
cross-validating each witness against the other criterion at all 158
triple-carrying balanced pool blocks, and asserts the necessity
(`a = 0`, structured (GR-8) max ≤ 0) at every one.

### Step G15 — (GR-13): the triangle-chain family — an explicit counting-blind obstruction, and NP-completeness of the grouped packing

For a graph `Γ` with edges `e₁, …, e_k` (any fixed order), the **chain**
`C(Γ)` is the balanced grouped instance: vertices `t₀, s₁, t₁, …, s_k,
t_k`; triangle `i` on `{t_{i−1}, s_i, t_i}` with side `(t_{i−1}, s_i)` in
class `X_{u_i}`, side `(s_i, t_i)` in class `X_{v_i}` (where
`e_i = (u_i, v_i)`), and chord `(t_{i−1}, t_i)` a singleton class. Then
`n = 2k + 1`, `m = 3k`, so `2m = 3(n − 1)` exactly.

> **(GR-13)** *(proven; driver `--hard`: 3-colourability equivalence at
> 6 named `Γ`, exhaustive `max_P g(P) = 0` over all `2^18` / `2^15` edge
> subsets at `C(K4)` / `C(C5)`, `dim Z = 0` at the construction labels and
> at random injective draws, both DFS routes agreeing)*
>
> (a) `C(Γ)` is balanced and legal-block-shaped (simple, no loops), with
> `a = 0` and `g(P) ≤ 0` — in fact `= 0` — for **every** sub-multigraph
> `P`, and `dim W = 0` (hence `dim Z = 0`) at **every injective**
> parameter assignment.
>
> (b) `C(Γ)` admits a tree-triple **iff `Γ` is 3-colourable**.
>
> (c) Consequently the partition-constrained base packing at exact balance
> is **NP-complete**, and no Edmonds-type min-max (good characterization)
> exists for it unless NP = coNP. With `Γ = K4`: an explicit balanced
> instance where **every counting obstruction vanishes and the rank
> criterion is satisfied generically, yet no tree-triple exists** — the
> certificate and the rank statement genuinely diverge blockwise.

*Proof.* (a) The chain is a cactus whose blocks are the `k` triangles, so
every circuit is a single triangle. A class has at most one edge per
triangle (its two sides lie in distinct classes since `Γ` is loopless, the
chord is private), so deleting one class leaves ≥ 2 edges of each
triangle, which keep each triangle's three vertices connected — `a = 0`.
For any `P`: `dim C(P)` = the number of complete triangles in `P`, and
`Σ_X r_X(P)` counts, over each complete triangle, the classes owning an
edge of it — exactly 3 — so `g(P) = 0`. For `W`: the triangle cycles
`z₁, …, z_k` have pairwise **disjoint supports** and form a basis, so
writing `Ψ = Σ_p t^p Σ_i λ_{p,i} z_i`, the (GR-7) conditions decouple into
`q_i(t_X) = 0` per triangle `i` and per class `X` meeting it, where
`q_i(t) = λ_{0,i} + λ_{1,i} t + λ_{2,i} t²`; each triangle meets 3
distinct classes, whose parameters are distinct at an injective
assignment, so each `q_i` has three distinct roots and vanishes: `W = 0`.
At balance `dim Z = a + (M − 3h) + dim W = dim W = 0`. (b) *Triple ⟹
colouring:* two edges of one triangle in one group `F_j` disconnect
`H ∖ F_j` (the two sides isolate `s_i`; a side plus the chord cut the
chain between `t_{i−1}` and `t_i`, since the triangle is the only local
passage in the cactus), so each group has ≤ 1 edge per triangle; sizes
(`k` each, by (GR-12)) force **exactly one edge per triangle per group** —
a rainbow condition — so at triangle `i` the classes `X_{u_i}`, `X_{v_i}`
lie in different groups, and `c(u) := group(X_u)` is a proper 3-colouring
of `Γ`. *Colouring ⟹ triple:* put `X_u` in group `c(u)` and each chord in
the third group of its triangle; each group takes one edge per triangle,
its complement keeps two per triangle and is spanning connected (the
cactus argument again), and (GR-12)(ii) upgrades co-independence to the
tree-triple. (c) Membership in NP is trivial; hardness is (b) with the
classical NP-completeness of graph 3-colourability (chromatic number is
one of Karp's 21 — Karp, *Reducibility among combinatorial problems*, in
*Complexity of Computer Computations*, Plenum, 1972, 85–103;
3-colourability stays NP-complete even for planar graphs of maximum degree
4 — Garey, Johnson, Stockmeyer, *Some simplified NP-complete graph
problems*, Theoret. Comput. Sci. **1** (1976) 237–267). A min-max in the
Edmonds sense supplies a polynomially-verifiable certificate for the
negative side, i.e. coNP membership. ∎

Three boundary remarks, recorded so the next pass does not re-derive them.
**(i) The chain's classes are disconnected** as subgraphs (a class `X_u`
scatters over `u`'s triangles), while real ruling classes are connected in
`H₊`. The hardness statement does **not** immediately transfer to the
connected-class subfamily — but Step G16 shows the *insufficiency of the
counting min side* transfers to the habitat regardless, which is what the
min-max question needed. **(ii) Connected-class hardness is obstructed by
a local-excess fact worth knowing:** if a feasible instance contains a
piece `Q` attached to the rest at `t` vertices, then each
`F_j ∩ Q`-removal must leave every private vertex of `Q` connected to an
attachment vertex, forcing `m_Q − |F_j ∩ Q| ≥ n_Q − t` for each `j`, hence
`2m_Q ≥ 3(n_Q − t)` — **no gadget region can carry negative local
excess**. An anchor-star construction (classes = stars at private
anchors, one conflict apex per `Γ`-edge) therefore balances only when the
gadget-connection pattern is a tree, and padding by pendant cycles
(`ℓ ≥ 4`), pendant thetas, or long subdivided fillers (length ≥ 4) is
infeasible outright, while length-≤ 3 fillers cap the padding capacity
below the `3·cr(Γ)` needed. Whether the grouped packing stays NP-complete
with **connected** classes is left open; the candidate route (class
spines through degree-≥ 3 private vertices, with inter-spine fillers) is
recorded here and **not claimed**. **(iii)** Feasible chains also carry
the (GR-14) certificate below — the chain *is* the rainbow-Δ mechanism.

### Step G16 — the separators are ON THE HABITAT: 18 real blocks where every counting obstruction vanishes and no triple exists

> *(measured; driver `--sep`, seed 20260806, exhaustive colouring
> enumeration per shape — no probe cap, colouring cap `2^12` per shape, K4
> stride 1)* Over the full census pool (903 shapes swept; the 4 V6-sweep
> shapes with more than `2^12` admissible colourings are skipped here and
> remain covered by the census's capped probe): **17772** filter-passing
> colourings, of which **16600** carry both-block tree-triples; scarcest
> shape `K4(1,2,5,5,2,3)` at 12/16. Of the **1720** triple-less blocks,
> **1702** are counting-VISIBLE (generic `dim Z > 0`, i.e. a (GR-8)-type
> obstruction), and **18** — four blocks of `V6m10(3,3,3,3,3,3,3,3,3,3)`
> and fourteen of `V6m11(3,3,3,3,3,3,3,3,4,4,4)` — are **SEPARATORS**:
> generic `dim Z = 0` (11 exact rational draws; each zero draw is a
> *proof* of generic vanishing by (GR-7) remark (i)), no tree-triple
> (re-verified through the landed slow route). **No shape misses
> (GR-10)** under exhaustive enumeration. Fast/slow triple-search
> agreement asserted at 532 blocks.

> *(proven per instance; driver `--exemplar`, the first separator pinned)*
> The exemplar — shape `V6m10`, all branch lengths 3; block with `m = 15`,
> `n_c = 11`, `h = 5`, `L = 11` classes of sizes `(2,2,2,2,1,…,1)` — has
> `a = 0`, structured (GR-8) max ≤ 0, and `dim Z = 0` at three exact
> rational parameter points; and **no 3-colouring of its classes makes
> every circuit polychromatic** — exhausted over all `3^11` assignments
> against its 18 distinct circuit class-sets (22 simple cycles), an
> independent proof of triple-nonexistence through (GR-12)(iii) that uses
> neither DFS. A greedy unsatisfiable core of 13 circuit class-sets is
> printed by the driver as the conflict structure; the smallest members
> (`{1,2,4,5}`, `{4,5,8,9}`, `{1,2,8,9}`, `{0,6,7,10}`, `{0,3,7,10}`) are
> 4-class circuits pairwise overlapping in 2 classes — the habitat's own
> version of the `C(Γ)` conflict pattern.

Read with the right polarity, this is the pass's sharpest finding: **the
habitat itself realizes counting-blind obstructions to the certificate.**
The fan-out's cheap kill (a shape whose *every* admissible colouring is
group-obstructed) did **not** fire — (GR-10) survives, now against
exhaustive enumeration rather than a 48-colouring probe — but the
per-block min side that a (GR-10) min-max would need is dead on habitat
ground, not just on constructed instances. At these 18 blocks the rank
target is *reached* (that is what `dim Z = 0` at an exact point proves)
while the certificate is *absent*: the discharge loses nothing, the
certificate theory does.

### Step G17 — (GR-14) and (GR-15): the second certificate, and the re-aimed residual

> **(GR-14)** *(proven; habitat applicability measured NIL)* If `H₊`
> admits an edge-disjoint cycle basis each of whose cycles meets ≥ 3
> classes, then `dim W = 0` at every injective parameter assignment, so
> `dim Z = a`; with `a = 0` the block reaches its (GR-1) rank bound. At a
> **balanced** block the hypothesis pins down completely: `3h = m` forces
> such a basis to be a **partition of `E(H₊)` into `h` rainbow 3-edge
> cycles** (disjoint circuits are automatically independent, hence a
> basis). Proof: the decoupling argument of (GR-13)(a) verbatim.
> Measured: **0** of 400 first-certified census blocks and **0** of the
> 18 separators carry one — the certificate proves the (GR-13) chains and
> nothing on the habitat; recorded so it is not re-hunted.

> **(GR-15)** *(open — the re-aimed tight-stratum residual; measured
> 907/907)* Every tight class shape admits an admissible colouring with
> generic `dim Z₊ = dim Z₋ = 0`. (GR-10) ⟹ (GR-15) (via (GR-9));
> (GR-15) + (GR-1)/§(K-clos) (AC-4) + (GR-5) + (AC-7) discharges `hK` on
> the tight stratum over every infinite characteristic-0 field — the same
> chain as (GR-10)'s, with the certificate step replaced by per-block
> generic vanishing. It is **one-point-decidable per shape**: an exact
> rational parameter draw with both blocks at rank is a proof ((GR-7)
> remark (i); the τ-side analogue is §(K-ann) (ANH-9)), so the census's
> 907/907 exact hits are already per-shape proofs, and the uniformity gap
> — not rigor — is what remains, exactly as for (GR-10).

Why re-aim rather than strengthen: (GR-15)'s per-block criterion is the
(GR-4′) equality question (`dim Z = a + max(0, max_P g(P))` at generic
parameters), which is **counting-shaped and untouched by (GR-13)'s
hardness** — the separators satisfy it exactly (`a = 0`, `max g = 0`,
`dim Z = 0`). Nothing above forbids a min-max *there*; what (GR-13)
forbids is a counting characterization of the **triple**. The two
combinatorial certificates in hand ((GR-9) tree-triples, (GR-14)
rainbow-Δ) both certify instances of (GR-15); the 18 separators are the
first natural test set for a (GR-11)-style hierarchical certificate,
which is the one instrument that could make (GR-15) combinatorially
certifiable where the triple fails.

### Step G18 — where the min-max question now stands (hand-off)

1. **As posed, closed.** "Prove (GR-10) by a min-max for the
   partition-constrained base packing" is unavailable: the packing's
   decision problem is NP-complete at balance ((GR-13)), and its
   counting min side fails on real blocks (Step G16). Any proof of
   (GR-10) must be an **existence-of-good-colouring argument** — exploit
   the free bit per branch (Step G12's structure) to *avoid* the
   non-polychromatic circuit hypergraphs, not to characterize them.
   The measured margin is comfortable (93.4 % of filter-passing
   colourings certify; every shape certifies), but §2.3's base-rate
   warning now attaches to a statement whose per-block theory is hard —
   caution is warranted in both directions.
2. **The flank that would refute (GR-10)** is now sharply described by
   (GR-12)(iii): a tight shape whose every admissible colouring yields,
   in some block, a circuit hypergraph with no polychromatic
   3-colouring. None exists in the censused strata (exhaustive sweep);
   the two separator-carrying shapes show single colourings can fail
   this way, so the question is whether the branch bits always steer
   around it. That is the precise open combinatorial question this
   direction leaves.
3. **The discharge-relevant residual is (GR-15)**, where the min-max
   question re-opens in counting form as (GR-4′) — off the critical
   path for direction G, back-lit now: proving (GR-4′) plus a
   colouring-existence argument for "some admissible colouring satisfies
   `a = 0 ∧ max g ≤ 0` in both blocks" would close the tight stratum
   without ever deciding a triple. Alternatively (GR-11)'s hierarchy,
   developed on the 18 separators, could re-combinatorialize the gap.

### Verification (Steps G14–G18)

`notes/scripts/w4/packmm.py` (**new with this pass**; imports `gridwit.py`
/ `grid.py` / `closure.py` read-only; exact ℚ throughout — integers and
`fractions.Fraction`, no floats; rngs seeded per mode, seeds printed; no
`set` printed; nothing samples a placement, so no figure is a rate gated
by `repin.star_generic` — the one geometric call, `rank_at_params`, is
reached only on a (GR-10)-miss shape, and none occurred). The fast triple
search (`fast_triple`, incremental rollback union-find) is a same-job
divergence from `gridwit.tree_triple` (README rule 3: different name);
agreement is asserted per-block on the whole `--restate` pool, at 532
sweep blocks, and at all 18 separators.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --restate  #   2 s  (GR-12): 212/212 balanced pool blocks; witnesses cross-validated both ways at 158
PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --hard     #  10 s  (GR-13): 6/6 Gamma equivalences; exhaustive max g = 0 at C(K4)/C(C5); dim Z = 0
PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --sep      # 118 s  903 shapes exhaustive; 16600/17772; 1702 visible + 18 SEPARATORS; no (GR-10) miss
PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --exemplar #   1 s  the pinned separator: dim Z = 0 proven at 3 exact points; 3^11 exhaust, no polychromatic colouring
PYTHONHASHSEED=0 python3 notes/scripts/w4/packmm.py --validate # all four, ~2 min
```

*Confidence verdict.* **(GR-12) proven-informally** (proof above; driver
212/212 with two independent criteria and witness cross-validation).
**(GR-13) proven-informally** (proof above; the NP-completeness rests on
the cited classical 3-colourability hardness; driver-verified equivalence
at 6 `Γ`, exhaustive `g`-sweeps at two chains). **The habitat separators:
proven per instance** (exact-rational-point semicontinuity for
`dim Z = 0`; exhaustive polychromatic failure for triple-nonexistence at
the pinned exemplar; the other 17 verified by both DFS routes + 11-draw
vanishing). **(GR-14) proven-informally**; its nil habitat applicability
is *measured* (400 + 18 blocks). **(GR-15) open**, measured 907/907, with
per-shape one-point decidability proven. **(GR-10): stays open as a
statement** — strictly stronger than (GR-15), exhaustively certified on
the censused strata — **but its min-max as posed is refuted.** Nothing
here re-opens the habitat-level (AC-6) refutation (`C11` is permanent),
and no σ-fixed witness is read as generic (§(K-clos) (AC-9)).

*What would change this.* (i) A tight shape whose every admissible
colouring fails (GR-12)(iii) in some block — refutes (GR-10) (the flank
of Step G18 item 2); (GR-15) would survive unless the rank also drops,
which no evidence suggests. (ii) A polynomial certificate for
triple-nonexistence **on the habitat's connected-class instances** — would
revive a (GR-10) min-max by escaping the (GR-13) hardness class; the
connected-class NP-completeness question (Step G15 remark (ii)) decides
whether that door is open. (iii) A proof of (GR-4′) — would make (GR-15)'s
per-block criterion a theorem and reduce the tight stratum to one
colouring-existence statement about counting conditions. (iv) A (GR-11)
hierarchical certificate succeeding at the 18 separators — would restore
a purely combinatorial route to (GR-15) where triples fail.

### Steps G19–G23 (2026-08-07, fan-out direction TCOL) — (GR-15) is NOT proven, but the problem loses the subdivision: `dim Z` becomes a square system on the **hub multigraph**, the per-circuit necessity becomes a **run count** that girth 7 makes vacuous except at two length profiles, the tree-triple is exactly a **grouping of a 6-spanning-tree decomposition of `Ĝ` that always exists**, and the **collapse hierarchy at order 4 certifies all 18 habitat separators** — so the certificate theory is not stuck where the triple is

Answering `notes/Pencil-fanout-archive.md` §"Fifth fan-out" → Direction TCOL, i.e.
§(K-grid) *Step G18* items 1 and 3. Read against *Steps G7–G18*
((GR-4′)/(GR-7)/(GR-8)/(GR-9)/(GR-10)/(GR-12)/(GR-13)/(GR-15), *Step G12*'s
finite-object notes and *Step G16*'s 18 separators); §(K-slide-comb) (C6);
§(K-frame) (FR-10)(i); §(K-clos) (AC-4)/(AC-7)/(AC-9); §(K-ind) (I1)/(I4);
and the *Shared dictionary*'s (R3), (R4) and (SD-6).

**Headline, stated before the mathematics.**

- **(GR-15) is NOT proven, and no flank was found.** The cheap kill was run
  on the strata the census structurally cannot reach —
  `kslidecomb.candidate_graphs` yields only **simple** hub graphs and the
  theta family only at 3 branches, so *every* hub multigraph with a parallel
  branch pair, and every generalized theta, is outside the 907 — and
  **7653 further class shapes over 11 families all carry a good colouring**,
  93 % of them at the *first* filter-passing colouring. Widening the pool is
  evidence, not progress; it is reported because the dispatch's cheap kill
  asked for it, and because the (FR-14) precedent showed the sweep has real
  family-level gaps.
- **(GR-16): the subdivision leaves the problem.** At a legal colouring the
  contracted multigraph `H₊` is *exactly* the subdivision of `G° / Γ_B` in
  which branch `β` becomes a path of `A(β) = |E_A ∩ β|` edges, and (GR-7)'s
  interpolation space is
  `W₊ ≅ { Q ∈ C(G°) ⊗ K[t]_{≤2} : R_β | Q_β }`, `deg R_β = |K_A(β)|`.
  At balance `dim Z₊ = dim W₊`, a **square `3c × 3c` system read off
  `(G°, length profile, branch bits)` alone** — the granularity *Step G12*
  says a uniform argument must have, delivered. Asserted against the landed
  `grid.dim_Z` at **57 840 colouring-blocks**, at construction labels and at
  seeded random labels (115 680/115 680).
- **(GR-17): the per-circuit necessity is a RUN COUNT, and girth makes it
  nearly vacuous.** Along the cycle of `G` under a circuit `γ` of `G°`,
  colours change at *every* degree-2 body; so with `L` the cycle length, `r`
  the number of branches and `h_≠(γ)` the number of hubs of `γ` where the two
  cycle edges differ, the number of maximal A-runs = the number of maximal
  B-runs = `((L − r) + h_≠)/2`, and (absent a `Γ_A`-merge off `γ`) that
  number **is** the count of distinct classes on `γ` in *both* blocks. By
  (GR-8) at `P = γ` it must be `≥ 3`. Since `h_≠ ≡ L − r (mod 2)`, the
  condition is **automatic whenever `Σ_{β∈γ}(ℓ_β − 1) ≥ 5`** — and when
  `Λ = ∅` the girth-7 bound forces `Σ(ℓ_β − 1) ≥ 4`, so the *only* binding
  circuit length-profiles are `(2,2,3)` and `(2,2,2,2)`. Measured over
  **1 158 344** (circuit, colouring) instances: 98.6 % of circuits are in the
  free regime and every violation has `Σ(ℓ−1) = 4`.
- **(GR-18): the packing half is never the obstruction for (GR-10) either.**
  Let `Ĝ` be `G°` with branch `β` given multiplicity `6 − ℓ_β`. Then
  `def(G) = 0` alone forces `Ĝ` to **partition into exactly 6 spanning trees
  of `G°`** — the Nash-Williams computation of §(K-slide-comb) (C6) with all
  six matroids equal to `M(G°)`. And a both-block tree-triple **is** such a
  partition: its six class-groups' complements are spanning trees of the HUB
  multigraph, branch `β` lying in `3 − A(β)` of the A-trees and `3 − B(β)` of
  the B-trees. So (GR-10) is a **3+3 grouping problem over an object that
  always exists**; the obstruction is the grouping, and the grouping is where
  `hcard` and girth enter. Asserted at 907/907 census shapes (Nash-Williams
  exhaustively over branch subsets; the grouping identity at every located
  certificate).
- **(GR-19): the collapse hierarchy, and COLLAPSE ORDER 4 at all 18 habitat
  separators.** Assigning one value `a_j` per group of an `r`-part partition
  of the classes bounds generic `dim Z` from above ((GR-7) remark (i)); at
  `r = 3` this family is *exactly* (GR-9)'s tree-triple, and it is **monotone
  in `r`**. Its counting content is uniform: `dim W_coll ≥ Σ_j comp(H₊ ∖ F_j)
  − r`, so a certificate needs all `r` complements connected. At **`r = 4`
  the hierarchy certifies every one of *Step G16*'s 18 separators** — the
  blocks where every counting obstruction vanishes and no tree-triple exists
  — and at the pinned exemplar the certificate is **value-independent**
  (0 failures over all 840 distinct integer 4-tuples from `{1..7}`), hence
  genuinely combinatorial. Combined with *Step G16*'s own classification
  (1720 triple-less blocks = 1702 counting-visible + these 18), **collapse
  order ≤ 4 holds at every `dim Z = 0` colouring-block of the census pool.**
  This is *Step G18* item 3's second route and *What would change this* item
  (iv), delivered — in a cleaner form than the ε-adic one.
- **What does NOT move.** (GR-15) stays open; (GR-4′) is untouched and stays
  off the critical path; (GR-10) stays open as the strictly stronger
  statement with its min-max refuted as posed. Class uniformity of `hK` is
  untouched and **no gap-map *status* moves**.

**Notation (on top of *Steps G1–G18*).** `G` a tight class shape:
`5|E| = 6(|V| − 1)`, `def = 0`, `hnoRigid`, plus the habitat conditions
`hcard` and no two-hub triangle. `c = |E| − |V| + 1`, so `(|V|, |E|) =
(5c + 1, 6c)` (§(K-ind) (I1)). `G°` is the **hub multigraph**, `n = n_hub`,
its edges the **branches** `β` of length `ℓ_β ∈ [1, 5]` ((SD-6));
`M := |E(G°)| = c + n − 1` and `Σ_β ℓ_β = 6c`. `Λ` = the length-1 branches
(hub-hub edges), of maximum degree ≤ 2 by (R4); `Γ_A`, `Γ_B` its two colour
classes. For `c ≥ 2`, `girth(G) ≥ 7` — a cycle of length ≤ 6 is rigid by
(R3) and would be a proper rigid subgraph. An **admissible** colouring is
one free bit per branch (*Step G12*(i)); `A(β) := |E_A ∩ β|`,
`B(β) := ℓ_β − A(β)`; `K_A(β)` is the set of A-classes meeting `β`.
Everything dualizes with `A ↔ B`, `+ ↔ −`.

---

### Step G19 — (GR-16): the branch-level reduction — `dim Z` is a square system on the hub multigraph

> **(GR-16)** *(proven; every clause asserted per block at 57 840
> colouring-blocks of the census pool, `--branch`)* Let `col` be admissible
> with `E_B` a forest, and work in the `+` block.
>
> **(i) The A-count law.** Each degree-2 body carries exactly one A- and one
> B-edge. Hence `A(β) = ℓ_β/2` for even `ℓ_β` (bit-independent), and for odd
> `ℓ_β`, `A(β) = (ℓ_β + 1)/2` if the branch's two end-edges are A and
> `(ℓ_β − 1)/2` if they are B. Balance `|E_A| = |E_B| = 3c` ⟺
> `Σ_β A(β) = 3c` ⟺ the signed subset-sum over the **odd** branches vanishes
> (*Step G12*(iii)).
>
> **(ii) `H₊` is a subdivision of the hub multigraph.** `H₊ = G/E_B` is
> exactly the subdivision of `G° / Γ_B` in which branch `β` becomes a path of
> `A(β)` edges: its nodes are the `Γ_B`-components of the hubs together with
> `A(β) − 1` interior nodes per branch, and **every non-hub node of `H₊` has
> degree exactly 2**. At balance `n_c = 2c + 1`, `m = 3c`, and
> `h = c(H₊) = c(G°) = c`.
>
> **(iii) The component law** (= §(K-frame) (FR-10)(i), which holds verbatim
> at any shape). Only hub-hub edges propagate a ruling component: every
> A-class is `star_A(u₁) ∪ … ∪ star_A(u_p)` over the hubs of a `Γ_A`-path of
> `Λ`, or a single **singleton** interior edge. The classes on one branch's
> A-path are pairwise distinct unless two of them are `Γ_A`-linked through
> hubs outside the branch; in particular `|K_A(β)| = A(β)` whenever
> `Λ = ∅`.
>
> **(iv) The interpolation space lives on `G°`.** Under `C(H₊) ≅ C(G°)`,
>
> > `W₊ ≅ { Q ∈ C(G°) ⊗ K[t]_{≤2} : R_β | Q_β for every branch β }`,
> > `R_β(t) = ∏_{X ∈ K_A(β)} (t − t_X)`, `deg R_β = |K_A(β)| ≤ A(β)`,
>
> and therefore, by (GR-7) and balance,
> **`dim Z₊ = dim W₊ = 3c − rank(Θ₊)`** with `Θ₊` the
> `(Σ_β |K_A(β)|) × 3c` matrix of those divisibility conditions in a
> fundamental-cycle basis of `G°`. At balance with no merging the system is
> **square**. Equivalently, writing `Q_β = R_β·p_β` with
> `deg p_β ≤ 2 − |K_A(β)|`, `W₊` is the kernel of the
> `3(n − 1) × 3(n − 1)` **hub** system
> `Σ_{β ∋ v} ε_{β,v} R_β(t) p_β(t) ≡ 0` (one polynomial identity per hub).

*Proof.* (i) is conjunct 4 of (AC-2) at every degree-2 body, restated. (ii):
contracting `E_B` merges each degree-2 body with exactly one neighbour, so
the surviving A-edges of `β` form a path from `[u]` to `[w]` whose interior
nodes are the B-edges of `β`'s interior — each of `H₊`-degree 2. Two hubs
share a B-component iff joined by a B-path, and by alternation a
monochromatic path turns only at hubs, so it lies inside `Λ`: the hub-nodes
of `H₊` are the `Γ_B`-components of the hubs. Counting nodes and edges gives
the balance figures. (iii) is (FR-10)(i)'s argument verbatim: within a branch
two same-family edges are never adjacent, so component propagation happens
only across hub-hub edges. (iv): contracting the forest `E_B` and then the
branch subdivisions is an isomorphism of cycle spaces (contracting a
non-loop edge preserves the cycle space), under which a cycle vector is
constant along each branch; (GR-7)'s condition `Ψ(t_X)_e = 0` for `e ∈ X`
becomes `Q_β(t_X) = 0` for every branch `β` meeting `X`, i.e. `R_β | Q_β`.
At balance `m = 3h`, so `a + (M − 3h) = a + (m − a) − m = 0` and (GR-7) reads
`dim Z = dim W`. The hub form is the same system re-coordinatized by the cut
space, whose dimension is `n − 1`; its unknown count is
`Σ_β (3 − |K_A(β)|) = 3M − Σ_β |K_A(β)|`, which equals `3M − 3c = 3(n − 1)`
— matching the `3(n − 1)` equations — **exactly when no merging occurs**
(when it does, the unknowns strictly outnumber the equations and
`dim W₊ > 0` outright, which is the branch-model face of `a > 0`). ∎

**Why this is the right object, said plainly.** *Step G12* records that
"the class's infinitude lives entirely in the `G°` direction (§(K-ind) (I4)),
so a min-max must be uniform over `G°`, not over subdivisions". (GR-16)
carries that from a *desideratum* to a *computation*: the subdivision is
gone, `dim Z` is the corank of a `3c × 3c` matrix built from `G°`'s cycle
space and one root-set per branch, and the branch bits enter only through the
degrees `A(β)` and through which hub stars the roots are shared by. The two
matrices are genuinely different objects — the landed `grid.dim_Z` is a
`3h × m` kernel over the *contracted edge space* and `gridwit.dim_W` its
`m × 3h` transpose; `--branch` runs the identity through both.

**Two immediate consequences, recorded because later steps use them.**
**(a)** `Q_β ≡ 0` whenever `|K_A(β)| = 3`, which needs `ℓ_β = 5` with both
end-edges A. So the support of any nonzero `Q ∈ W₊` avoids those branches and
is a **bridgeless** subgraph of `G°` (a union of supports of cycle vectors).
**(b)** Evaluating the hub relation at `t = t_{star_A(v)}` kills every branch
of `N_A(v)`, leaving `Σ_{β ∈ N_B(v)} ε_{β,v} Q_β(t_{star_A(v)}) = 0`: at a
hub with exactly one B-end branch this **forces an extra root** on that
branch. Neither is used below; both are the natural handles for a future
uniform argument.

---

### Step G20 — (GR-17): the circuit law, and the two profiles at which it binds

> **(GR-17)** *(proven; asserted over 1 158 344 (circuit, colouring)
> instances of the census pool, `--runs`)* Let `γ` be a circuit of `G°` with
> `r` branches and total length `L = Σ_{β ∈ γ} ℓ_β ≥ 7`, and let `C(γ)` be
> the corresponding cycle of `G`. Write `h_≠(γ)` for the number of hubs of
> `γ` at which the two `C(γ)`-edges carry different colours.
>
> **(a) The run law.** The colours change at *every* degree-2 body of
> `C(γ)`, so the number of maximal A-runs equals the number of maximal
> B-runs equals
> > `runs(γ) = ((L − r) + h_≠(γ)) / 2`,  and `h_≠(γ) ≡ L − r (mod 2)`.
>
> **(b) Runs are classes.** `D_A(γ) := #{A-classes meeting γ} ≤ runs(γ)`,
> with equality unless two A-runs of `γ` are joined by a `Γ_A`-path **off**
> `γ`; likewise for B. So when no `Γ_A`- (resp. `Γ_B`-) edge lies off `γ` —
> in particular always when `Λ = ∅` — **`D_A(γ) = D_B(γ) = runs(γ)`: the two
> blocks impose the same circuit condition.**
>
> **(c) Necessity.** (GR-8) at `P = γ` gives `dim Z_± ≥ 3 − D_{A/B}(γ)`.
> Hence `dim Z₊ = dim Z₋ = 0` forces `D_A(γ), D_B(γ) ≥ 3` at **every**
> circuit of `G°` — call this **(NC1)**.
>
> **(d) The binding list.** In the unmerged case (NC1) is **automatic**
> whenever `Σ_{β ∈ γ}(ℓ_β − 1) ≥ 5`: then `2·runs = (L − r) + h_≠ ≥ 5 + h_≠`
> and `h_≠ ≡ 1 (mod 2)`, so `2·runs ≥ 6`. When `Λ = ∅` every branch has
> `ℓ ≥ 2`, so `Σ(ℓ_β − 1) ≥ r` and `L ≥ 7` give `Σ(ℓ_β − 1) ≥ ⌈L/2⌉ ≥ 4`;
> the binding case `Σ(ℓ_β − 1) = 4` then forces `r ≤ 4` and `L = r + 4 ≥ 7`,
> leaving exactly the two length profiles
> > **`(2,2,3)`  and  `(2,2,2,2)`.**
>
> At those, (NC1) says exactly `h_≠(γ) ≥ 2` — a condition on the branch bits
> alone.

*Proof.* (a): at a degree-2 body the two incident edges alternate, so every
one of the `L − r` degree-2 bodies of `C(γ)` is a colour change; the hubs
contribute `h_≠`. The changes around a cycle are even in number and separate
the A-runs from the B-runs alternately, so each family has half of them.
(If there is no change at all, `C(γ)` is monochromatic, which needs `L = r`,
i.e. a monochromatic `Λ`-cycle — excluded by "both ruling classes forests".)
(b): two A-edges of `C(γ)` lie in one class iff they are joined by an A-path;
by (GR-16)(iii) such a path turns only at hubs, so within `γ` it merges
exactly the *adjacent* A-edges, i.e. the runs; any further merge uses a
`Γ_A`-edge off `γ`. (c) is (GR-8) with `P = γ`: `dim C(P) = 1` and
`r_X(P) = 1` exactly for the classes meeting `γ`, so `g(γ) = 3 − D_A(γ)`.
(d) is the arithmetic above. ∎

**Measured, `--runs`, whole census pool** (1 158 344 circuit×colouring
instances, all 907 shapes): the run identity `2·runs = (L − r) + h_≠` holds
at 1 158 344/1 158 344; `D_A = D_B = runs` at 1 150 894, and every one of the
7 450 shortfalls has an off-circuit `Λ`-edge of the failing colour, exactly
as (b) requires. **1 141 846 of the 1 158 344 circuits (98.6 %) sit in the
free regime `Σ(ℓ − 1) ≥ 5`.** The circuits carrying fewer than 3 distinct
classes occur at exactly five length profiles, *all* with `Σ(ℓ − 1) = 4`:

| profile | `Σ(ℓ−1)` | instances |
|---|---|---|
| `(1,1,5)` | 4 | 72 |
| `(1,2,4)` | 4 | 1008 |
| `(1,3,3)` | 4 | 156 |
| `(2,2,3)` | 4 | 1296 |
| `(1,2,2,3)` | 4 | 144 |

(The three profiles containing a `1` are the `Λ ≠ ∅` cases the proof's
`Λ = ∅` clause does not cover; no instance with `Σ(ℓ−1) ≥ 5` ever failed,
merged or not.) And the necessity direction is exact on the pool: of the
2 676 balanced blocks carrying a sub-3 circuit, **0** have generic
`dim Z₊ = dim Z₋ = 0`.

**The constructed carrier, and the adversarial test (README §4 convention 6 /
dispatch-log F13).** `--runs` builds the hub multigraph `K4` with the
triangle `0–1–2` at lengths `(2,2,3)` and the apex legs at `(4,4,3)`
(`Σ ℓ = 18`, so `c = 3` and the subdivision is tight), certifies it a class
shape, and confirms it carries exactly one `(2,2,3)` circuit. Of its
filter-passing colourings, **2 are rejected** by (NC1) — the criterion's
adversarial witnesses — and both are measured at `dim Z₊ = dim Z₋ = 1`; the
other **14 are accepted**, with a negative control at `D_A = D_B = 3`,
`dim Z₊ = dim Z₋ = 0`. Parity, not size, is the mechanism: the rejected pair
is exactly `h_≠ = 0`, which the branch bits are free to avoid.

---

### Step G21 — (GR-18): the tree-triple is a grouping of a 6-tree decomposition that always exists

> **(GR-18)** *(proven; asserted at 907/907 census shapes, `--pack`)* Let
> `Ĝ` be the hub multigraph with branch `β` given multiplicity `6 − ℓ_β`
> (positive by (SD-6)); `|E(Ĝ)| = 6M − 6c = 6(n − 1)`.
>
> **(i)** `def(G) = 0` alone forces `Ĝ` to **partition into exactly 6
> spanning trees of `G°`**.
>
> **(ii)** A both-block tree-triple ((GR-10)) at a colouring **is** such a
> partition: writing `T_j := {β : no class of the A-group `F_j` meets β}` and
> `T'_j` for the B-groups, all six are spanning trees of `G°`, and branch `β`
> lies in exactly `3 − A(β)` of the `T_j`, `3 − B(β)` of the `T'_j`, hence in
> `(3 − A(β)) + (3 − B(β)) = 6 − ℓ_β` of the six.
>
> **(iii)** Conversely a partition of `Ĝ` into 6 spanning trees, a 3+3
> grouping in which every branch's tree-set splits as `(3 − A(β), 3 − B(β))`
> for a length-legal `A(β)`, an A-end choice for each even branch and a
> consistent hub colouring, rebuild a both-block tree-triple. So **(GR-10)'s
> obstruction is never the packing; it is the grouping.**

*Proof of (i).* By Tutte and Nash-Williams (Tutte, *On the problem of
decomposing a graph into n connected factors*, J. London Math. Soc. **36**
(1961) 221–230; Nash-Williams, *Edge-disjoint spanning trees of finite
graphs*, same volume, 445–450 — the pair already cited at *Step G11*), `Ĝ`
has 6 edge-disjoint spanning trees iff `Σ_{β ∈ F}(6 − ℓ_β) ≤ 6·r_{M(G°)}(F)`
for every branch set `F`. Let `F` span `W` with `k` components. 5/6-sparsity
of `G` (which `def(G) = 0` gives at a tight shape) applied to a single
component `F′` spanning `W′` reads
`5·Σ_{F′} ℓ ≤ 6(|W′| + Σ_{F′}(ℓ − 1) − 1)`, i.e.
`Σ_{F′}(6 − ℓ) ≤ 6(|W′| − 1)`; summing over the `k` components gives
`Σ_F(6 − ℓ) ≤ 6(|W| − k) = 6·r(F)`. Since the total is exactly `6(n − 1)` =
6·rank, the packing is a **partition** and every part a spanning tree. ∎

*Proof of (ii).* Counting: `Σ_{j=1}^{3} |E(G°) ∖ B(F_j)| = 3M −
Σ_β #{j : F_j meets β}` and `#{j : F_j meets β} ≤ |K_A(β)| ≤ A(β)`, so
`Σ_j |T_j| ≥ 3M − 3c = 3(n − 1)`. Each `T_j` is spanning connected: a
`Γ_B`-branch has `A(β) = 0` and lies in all three `T_j`; and `H₊ ∖ F_j`
connected (the (GR-12)(ii) form of the certificate) says the hub-nodes are
joined by the branches carrying no colour-`j` class, i.e. by `T_j`.
Spanning connected with `≤ n − 1` edges apiece and `≥ 3(n−1)` in total
forces `|T_j| = n − 1` and each a spanning tree — and forces every branch to
be **rainbow** (its `|K_A(β)|` classes get distinct groups), which is also
what stops an interior node of `H₊` from being isolated. Adding the B-side
gives multiplicity `6 − ℓ_β`. ∎ *(iii) is the same bookkeeping read
backwards; the driver checks the multiplicity half of it.)*

**Relation to §(K-slide-comb) (C6), stated so the two are not conflated.**
(C6) is the *refinement* of (i) in which three of the six parts are bases of
`M(G°)/e₀` (2-component forests separating `b|c`) rather than of `M(G°)`;
its proof's `b ≁ c` case **is** the computation above. So the statement the
tight-stratum residual needs is strictly weaker than the one
§(K-slide-comb) already owns, and (C6) remark (b)'s observation — that this
is Phase-12/13/14 landed machinery (`Matroid/Constructions/{Submodular,
Union}.lean`, `BodyBar/TreePacking.lean`, `BodyBar/KFrame.lean`) — transfers
verbatim. (C6) remark (c) said *"a route that needed only (C6) would be in
reach of landed machinery. The route that is actually needed is not."*
(GR-18) is the first place in the arc where the route that is actually
needed **does** rest on it — for its packing half.

**Measured** (`--pack`, all 907 census shapes): the Nash-Williams inequality
verified **exhaustively over all `2^M` branch subsets** at every shape
(0 skipped); a both-block tree-triple located at 907/907 (not a new (GR-10)
measurement — `packmm --sep` owns that figure — but the vehicle for the
assertion), and at every one of them the six groups asserted to be spanning
trees of the **hub** multigraph with multiplicities `3 − A(β)` / `6 − ℓ_β`.

**What (iii) leaves as the live combinatorics.** Writing `C_β ⊆ {1..6}` for
the trees containing `β`, the 3+3 split `J` must satisfy `|C_β ∩ J| = 3 −
A(β)`: automatic at `ℓ_β ∈ {1, 5}`, and at `ℓ_β ∈ {2, 3, 4}` it says the
complementary set `D_β` (`|D_β| = ℓ_β`) is split by `J` as evenly as
possible. So the residual grouping problem is an **equitable bisection of a
6-element tree set against a `c`-regular hypergraph whose edges are the
branches** — with the freedom to re-choose the packing (matroid-union
exchange) and the even branches' bits. That is the shape of the argument a
successor should attack.

---

### Step G22 — (GR-19): the collapse hierarchy, and collapse order 4 at the 18 separators

> **(GR-19)** *(proven, plus a measured verdict at *Step G16*'s separators;
> `--hier`)* Fix a colouring-block. For a partition of its classes into `r`
> groups `F_1, …, F_r` and distinct values `a_1, …, a_r`, put
> `W_coll(F, a) := { Ψ ∈ C(H₊) ⊗ K[t]_{≤2} : Ψ(a_j)|_{∪F_j} = 0 }`.
>
> **(i)** `dim Z_generic ≤ dim W_coll(F, a)` for every `(F, a)` — the
> parameter assignment is a point, and (GR-7) remark (i) makes `dim Z` upper
> semicontinuous. So `dim W_coll = 0` **proves** generic `dim Z = 0`.
>
> **(ii)** `dim W_coll ≥ Σ_j comp(H₊ ∖ F_j) − r ≥ 0`, with the first
> inequality an equality of counts: a certificate requires **every one of the
> `r` complements connected** (`r` **co-independent** groups, in (GR-12)(ii)'s
> sense).
>
> **(iii)** At `r = 3` the family is *exactly* (GR-9): Lagrange makes
> `W_coll` the direct sum `⊕_j C(H₊ ∖ F_j)`, zero iff all three complements
> are spanning trees. At `r ≥ 4` it is **strictly stronger** — the count is
> square and the vanishing is a determinant, not a direct sum.
>
> **(iv)** The hierarchy is **monotone in `r`**: refining a certifying
> partition still certifies (the coarser point is a specialization of the
> finer one). So the **collapse order** `κ(block) :=` the least `r` admitting
> a certificate is well defined, `κ = 3` ⟺ a tree-triple exists, and
> `κ ≤ #classes` ⟺ generic `dim Z = 0`.
>
> **(v) Measured.** At **all 18 habitat separators** of *Step G16* — where
> every counting obstruction vanishes, generic `dim Z = 0` is proven at exact
> rational points, and **no tree-triple exists** — a **4-group collapse
> certifies**: `κ = 4`, 18/18. At the pinned exemplar (`V6m10(3¹⁰)`,
> `m = 15`, `n_c = 11`, `h = 5`, 11 classes) the `r = 3` search is
> **exhausted** over all 29 525 canonical partitions with **0**
> co-independent triples, while 257 of the 20 967 canonical 4-partitions are
> co-independent and the first of them certifies, at the partition
> `{0,1,4} | {2,3,7,8} | {5,6,9} | {10}`. That certificate is
> **value-independent**: `dim W_coll = 0` at every one of the 840 distinct
> integer 4-tuples from `{1..7}`.

*Proof.* (i) is semicontinuity. (ii): `dim W_coll ≥ 3h − Σ_j (h − dim
C(H₊ ∖ F_j))`, and at a balanced block `m = 3h`, `n_c = 2h + 1`, so
`Σ_j dim C(H₊∖F_j) = Σ_j [(m − |F_j|) − n_c + comp_j] = (r−1)m − r n_c +
Σ_j comp_j = rh − 3h − r + Σ_j comp_j`; substituting gives
`dim W_coll ≥ Σ_j comp_j − r`. (iii): with three evaluation points a
quadratic curve is free (Lagrange), so `W_coll = ⊕_j C(H₊ ∖ F_j)`; that is
(GR-9)'s proof read as a dimension count, and the equality shows why `r = 3`
is *both* necessary and sufficient there. With `r ≥ 4` the values
`Ψ(a_1), Ψ(a_2), Ψ(a_3)` determine `Ψ(a_4), …`, so extra conditions land on
an already-determined vector: the system is square when all complements are
connected, and its vanishing is a genuine determinant condition. (iv):
setting two of the finer partition's values equal specializes the finer point
to the coarser one, and `dim W` is upper semicontinuous. ∎

**Why (v) is the finding.** *Step G17* recorded that the 18 separators "are
the first natural test set for a (GR-11)-style hierarchical certificate,
which is the one instrument that could make (GR-15) combinatorially
certifiable where the triple fails", and *Step G18*'s *What would change
this* item (iv) asked exactly for a hierarchical certificate succeeding
there. **It succeeds, at order 4, at all 18.** Together with *Step G16*'s
own classification of the 1720 triple-less blocks (1702 counting-visible,
i.e. generic `dim Z > 0`, plus these 18) and the 16 600 filter-passing blocks
that do carry tree-triples, this says:

> **collapse order ≤ 4 holds at every `dim Z = 0` colouring-block of the
> census pool.**

So the gap between the certificate theory and the rank statement, which
(GR-13) opened blockwise and *Step G16* realized on the habitat, **closes at
one extra collapse level**. The (GR-11) ε-adic hierarchy is the same
instrument in infinitesimal form; the `r`-value collapse is its finite,
purely combinatorial shadow, and it is what the driver tests.

**Two honest limits.** (a) `κ ≤ 4` is *measured* on the census pool, not
proven; nothing here bounds `κ` in general, and the search at `r = 4` is a
DFS over canonical partitions with a per-block time budget (no block hit it).
(b) Value-independence was verified **at the pinned exemplar's exhibited
partition** over 840 tuples, and at the other 17 separators the certificate
was accepted on 3 independent seeded draws — i.e. the *combinatorial*
reading of the `r = 4` certificate is established at one separator and
strongly evidenced at the rest, not proven in general. A proof would say:
*at a balanced block, `r` co-independent groups certify iff <combinatorial
condition>* — which is the natural successor question and is **not** a
corollary of anything here.

---

### Step G23 — (GR-20): where (GR-15) stands (hand-off)

> **(GR-20)** *(the residual, restated on the hub multigraph)* (GR-15) holds
> at a tight class shape iff there are branch bits, balanced with both `Γ_A`
> and `Γ_B` forests, such that in **both** blocks the square system
> `Θ_± ` of (GR-16)(iv) has full rank at generic class parameters.
> Sufficient combinatorial certificates in hand, in increasing strength of
> hypothesis and decreasing strength of conclusion:
>
> 1. a tree-triple ((GR-9)) = collapse order 3 — implies it;
> 2. any collapse order `r` certificate ((GR-19)) — implies it, and covers
>    every `dim Z = 0` block of the census pool at `r ≤ 4`;
> 3. `a = 0 ∧ max_P g(P) ≤ 0` — implies it **modulo (GR-4′)**, which stays
>    open and off the critical path.
>
> Necessary conditions, all now readable off `(G°, ℓ, bits)`: no
> monochromatic hub; both `Λ`-colour classes forests; balance = a signed
> subset-sum over the odd branches; and (NC1) = `runs(γ) ≥ 3` at every
> circuit, which by (GR-17)(d) binds only at circuits with
> `Σ_{β∈γ}(ℓ_β − 1) ≤ 4`.

**Route (a) (the dispatch's first named route), status.** (GR-4′) was not
attacked and is unchanged. Its colouring-existence half is now a statement
about `G°`: *choose bits with `a = 0` and `max_P g(P) ≤ 0` in both blocks*.
(GR-17) settles the `P = circuit` instance of that — it is free at 98.6 % of
circuits and reduces to `h_≠ ≥ 2` at two length profiles when `Λ = ∅` — but
the general `P` instance is untouched, and blocks satisfying (NC1) with
`dim Z > 0` do occur: *measured in a scoping probe over the first 45 census
shapes, **script not retained** (`notes/scripts/README.md`'s standing rule;
the figure is orientation, not evidence, and no claim above rests on it)* —
16 of 572 balanced, no-monochromatic-hub, (NC1)-satisfying blocks had
generic `dim Z > 0`, each with `a = 0` and structured (GR-8) maximum 1 —
**corrected** (*Step G30*, direction GCAP): **not** "all on `Λ ≠ ∅`
shapes", as originally recorded here. That clause was a sample-bias
artifact of this probe's own 45-shape prefix (the census generator requires
a length-3 branch and orders the `K4` stratum lexicographically, so the
prefix is all `K4(1,…)`); the full 907-shape census has 955 such hits, of
which 675 — most of them — live on `Λ = ∅` shapes. So the sub-circuit
members of the (GR-8) family really do bite, and (NC1) alone is not the
colouring-existence target — but the binding non-circuit family is not a
`Λ ≠ ∅` phenomenon; *Step G30* is its canonical home.

**Route (b) (the dispatch's second named route), status: DELIVERED at the
target it named.** (GR-19) is the (GR-11) hierarchy in finite form, and it
certifies all 18 separators at order 4. What it does **not** do is give a
uniform statement: there is no bound on `κ` and no colouring-existence
argument, so (GR-15) is not closed.

**The residual, in one sentence.** After (GR-16)–(GR-19), (GR-15) is a
statement about branch bits on a hub multigraph, whose sufficiency side has a
finite certificate hierarchy that is measured adequate (`κ ≤ 4`) and whose
packing side is free ((GR-18)); **what is missing is an existence argument
over the bits** — the same shape of gap (GR-10) has, now against a strictly
weaker target and with two more certificate levels available.

---

### Does direction PEX's technique transfer? (the dispatch's flagged F14 hypothesis)

**Partially — in exactly the weak form PEX itself predicted, and the strong
form is refuted.** PEX's *What would change this* item (iv) said the
transferable technique is "not the recipe but its two enablers: *reduce the
colouring question to a statement about `Λ` alone*, and *use `hcard` + girth
to bound `Λ` so hard that the statement becomes vacuous*", while the
finiteness half does not transfer. Measured against what happened here:

- **(FR-10)(i)'s component law transfers verbatim** and is load-bearing: it
  is (GR-16)(iii), and it is what makes the classes readable off `(G°, ℓ,
  bits)` at all.
- **"`hcard` + girth make the statement vacuous" transfers, in a weakened
  form.** It does not become vacuous; it becomes vacuous *at 98.6 % of
  circuits*, and the residue is two explicit length profiles ((GR-17)(d)).
  That is the same mechanism (girth 7 against a short-cycle count, `hcard`
  bounding `Λ`) doing a smaller job.
- **The reduction is to `G°`, not to `Λ`.** (FR-R1) reduced to `Λ` because
  its whole content was the 3–3 split of six frame edges; (GR-15)'s content
  is a rank condition on the full cycle space, so the best available
  reduction keeps `G°`.
- **The finiteness half does not transfer**, as PEX said: `c` is unbounded on
  the tight stratum, hence so are `n_hub` and the number of branches, and no
  exhaustive enumeration is available at any granularity.
- **The decisive difference is the one PEX named**: (FR-R1) has no
  spline/rank side, so its combinatorial criterion was an *equivalence*
  ((FR-10)(ii)) and a recipe closed it. Here (GR-17) is only *necessary*;
  sufficiency needs (GR-9)/(GR-19), which have no counterpart in (FR-R1).
  **So the coordinator's F14 hypothesis is confirmed for the exports and
  refuted for the conclusion**: PEX's technique supplies the reduction, not
  the proof.

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as PEX's, and for the same reason: everything above is a statement about
*colourings of a fixed graph* and about a *constructed* σ-fixed
configuration's rank, never about `PencilNondegFeasible G`. (GR-17) is a
necessary condition on a colouring for one constructed grid point to reach
target rank; nothing propagates a feasibility proposition, so the landed
refutation `not_pencilNondegFeasible_of_triangle_two_hubs` is not in tension
with anything here.

---

### Verification (Steps G19–G23)

`notes/scripts/w4/gridcol.py` (**new with this pass**, untracked; imports
`packmm.py` / `gridwit.py` / `grid.py` / `closure.py` read-only plus the
catalogued §1 primitives `exactcore.rank`, `kbare_common.verts_of` /
`rank_modp`, `nogood_subdiv`'s `deficiency` / `hcard_ok` / `hub_set` /
`rigid_vertex_sets` / `triangles`, and `kslide.no_rigid_branch_union` — all
already in `grid.py`'s import closure. Exact ℚ for every asserted identity;
GF(p) (`rank_modp`) only in the `--wide` screen, as a **certified lower
bound** for the rational rank — a full GF(p) rank proves full rational rank
for an integer matrix, hence generic `dim Z = 0` — with an exact-ℚ recheck of
the attaining draw at every reported hit, per README §4 convention 2. Rngs
seeded per mode, seeds printed; no `set` is printed. Nothing samples a
placement, so no figure is a rate and `repin.star_generic` gates nothing
here, exactly as for `gridwit.py` / `packmm.py` under §(K-clos) (AC-9).)

Four local devices, each named as such in its docstring: `branch_decomp`
(the branch decomposition **with named hub ends and edge order** —
`closure.alternation_classes` returns a branch as an edge set with parities
and never names its two ends); `subdivide` + `class_shape` (`kslidecomb.
shape_data` hard-asserts `specs[0] == (0,1,3)`, i.e. a length-3 *split*
branch, which the widened pool deliberately drops); `multigraphs`
(`kslidecomb.candidate_graphs` walks subsets of the vertex *pairs* and so
yields only **simple** hub graphs — the family gap `--wide` exists to close);
and `dim_W_branch` / `collapse_search`. Nothing existing is modified
(`git diff --name-only` empty).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --branch    # 130 s  (GR-16) 57840 blocks, identity 115680/115680 at construction and random labels
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --runs      #  24 s  (GR-17) 1158344 circuit x colouring instances; binding profiles all at sum(ell-1) = 4; constructed carrier + control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --pack      #  98 s  (GR-18) Nash-Williams exhaustive at 907/907; every certificate a 6-tree decomposition of Ghat
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --hier      #  98 s  (GR-19) collapse order 4 at 18/18 separators; exemplar r = 3 exhausted; 840-tuple value-independence
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --wide      # 159 s  the cheap kill: 7653 shapes over 11 unswept families, 7653/7653
PYTHONHASHSEED=0 python3 notes/scripts/w4/gridcol.py --validate  # all five, 509 s
```

All five modes byte-identical under `PYTHONHASHSEED` 0 and 999; every
invocation, and `--validate` itself, inside the 600 s budget (F15 does not
bind).

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-16)(i) | — | **proof-level** (one line of alternation); its consequence `Σ A(β) = m` is asserted per block |
| (GR-16)(ii) | `--branch` | per block: `\|V(H₊)\| == #hub-components + Σ_β (A(β) − 1)`, and **every** non-hub node of `H₊` asserted of degree exactly 2 |
| (GR-16)(iii) | `--branch` | per own-colour edge: a hubless edge is asserted to be a singleton class; `\|K_A(β)\| ≤ A(β)` per branch |
| (GR-16)(iv) | `--branch` | `dim Z` from `grid.dim_Z` (3h × m, contracted edge space) `== a + (M − 3h) + dim W_branch` (branch system, 3c columns) at the construction labels **and** at seeded random labels; and `dim Z == dim W_branch` at every balanced block |
| (GR-17)(a) | `--runs` | `2·runs == (L − r) + h_≠` asserted per (circuit, colouring) |
| (GR-17)(b) | `--runs` | `D_A, D_B ≤ runs`, and a shortfall **on a side** asserted to require an off-circuit `Λ`-edge *of that colour* (the exact contrapositive) |
| (GR-17)(c) | `--runs` | blocks carrying a sub-3 circuit are re-measured for generic `dim Z` in both blocks: 0 of 2676 have both zero |
| (GR-17)(d) | `--runs` | every sub-3 circuit asserted to have `Σ(ℓ−1) ≤ 4`; and `runs ≥ 3` asserted at **every** circuit with `Σ(ℓ−1) ≥ 5` |
| (GR-17) as a guard | `--runs` | the **constructed** `(2,2,3)` carrier: 2 filter-passing colourings rejected (each asserted `dim Z > 0`), 14 accepted with a `dim Z = 0` negative control (F13) |
| (GR-18)(i) | `--pack` | the Nash-Williams inequality asserted **exhaustively over all `2^M` branch subsets** at every shape, plus `Σ(6 − ℓ) == 6(n − 1)` |
| (GR-18)(ii) | `--pack` | at every located both-block certificate: each of the six groups asserted a spanning tree of the **hub** multigraph, and each branch's multiplicity asserted `== 6 − ℓ_β` and its A-side share `== 3 − A(β)`; `fast_triple` vs `gridwit.tree_triple` existence agreement asserted per block |
| (GR-19)(i)/(ii) | — | **proof-level** (semicontinuity; the dimension count); (ii) is the search's exact pre-filter |
| (GR-19)(iii) at `r = 3` | `--hier` | the exemplar's `r = 3` search **exhausted**: 0 co-independent triples over all 29 525 canonical partitions |
| (GR-19)(iv) | `--hier` | a refinement of the certifying 4-partition into 5 groups asserted still certifying |
| (GR-19)(v) | `--hier` | the 18 separators **re-found** from the two carrier shapes by the *Step G16* recipe (triple-less + generic `dim Z = 0` at 3 then 8 draws), and `r = 4` certification asserted 18/18; the exemplar's certificate re-evaluated at all 840 distinct integer 4-tuples from `{1..7}`, 0 failures |
| the cheap kill | `--wide` | 7653 class-certified shapes over 11 families, exhaustive over branch bits, each hit re-checked in exact ℚ through **both** the branch system and `grid.dim_Z` |
| (GR-4′) | — | **untouched and not driver-testable here**: no mode probes the equality |

**Pool caveats, stated because the arc has been bitten by them.**
`--wide`'s 7653 is a **labelled-instance count**, not a count of isomorphism
classes (README §4 convention 7 / §(K-frame) (FR-14)): hub multigraphs are
canonicalized up to isomorphism, but length profiles are enumerated on a
labelled edge list, so a graph automorphism permuting branches produces
duplicates. Length profiles are exhaustive where the solution set is small
and **seeded rejection-sampled** (unbiased over the solution set) where it is
not — a lexicographic prefix would have been all-1-heavy, exactly the
profiles `hcard` kills. Class certification uses
`kslide.no_rigid_branch_union` (the census's own branch-granularity
`hnoRigid` test), which accepts a **superset** of class shapes — the safe
direction for a kill hunt. The families are `theta` (n = 2 at 3–6 parallel
branches; only m = 3 is in the census), `V3m5/V3m6/V3m7`, `V4m6` (parallel
pairs only — the simple `K4` stratum *is* the census), `V4m7`, `V4m8`,
`V5m8`, `V5m9`, `V6m10`, `V6m11`.

---

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(GR-16)** | the branch-level reduction: `H₊` is the subdivision of `G°/Γ_B`; `dim Z = a + (M − 3h) + dim W_branch`; at balance a square `3c × 3c` system on `G°` | **proven** (informal proof + the identity exact at 115 680 evaluations over 57 840 blocks, through two structurally different matrices) |
| **(GR-17)(a)–(c)** | the run law, runs = classes up to off-circuit `Λ`-merges, and `runs(γ) ≥ 3` necessary | **proven** ((a)/(b) elementary; (c) is (GR-8) at `P = γ`); asserted at 1 158 344 instances |
| **(GR-17)(d)** | the binding list: free above `Σ(ℓ−1) ≥ 5`; at `Λ = ∅` exactly the profiles `(2,2,3)`, `(2,2,2,2)` | **proven** for the unmerged case (the `Λ = ∅` clause is where girth 7 is consumed); the merged case is **measured nil** (no `Σ(ℓ−1) ≥ 5` failure in 1 158 344 instances), not proven |
| **(GR-18)(i)** | `Ĝ` partitions into 6 spanning trees of `G°`, from `def(G) = 0` alone | **proven** (Tutte/Nash-Williams + 5/6-sparsity; = §(K-slide-comb) (C6)'s `b ≁ c` case), verified exhaustively at 907/907 |
| **(GR-18)(ii)** | a both-block tree-triple **is** such a partition, with multiplicity `3 − A(β)` / `3 − B(β)` | **proven-informally** (the counting + connectivity argument), asserted at every certificate of 907/907 shapes |
| **(GR-19)(i)–(iv)** | the collapse hierarchy: semicontinuity, the connectivity count, `r = 3` ⟺ tree-triple, monotone in `r` | **proven** |
| **(GR-19)(v)** | collapse order 4 at all 18 habitat separators; the exemplar's certificate value-independent | **proven per instance** (each certificate is an exact-point vanishing, hence a proof of generic vanishing; the exemplar's `r = 3` non-existence is exhausted, its value-independence exhausted over 840 tuples) — the *18/18* is a measurement over a pinned finite set |
| **`κ ≤ 4` on the census pool** | every `dim Z = 0` block of the pool has collapse order ≤ 4 | **measured**, resting on *Step G16*'s classification (1702 + 18 of 1720) plus 18/18 here; **not proven in general** |
| **(GR-15)** | every tight class shape admits an admissible colouring with generic `dim Z₊ = dim Z₋ = 0` | **OPEN** — unchanged in status. Evidence now 907 + 7653 shapes (the second batch on families the census cannot reach); the cheap kill did not fire |
| **(GR-10)** | the tree-triple form | **open**, unchanged; (GR-18) reframes it as a grouping of a guaranteed packing |
| **(GR-4′)** | the per-block equality | **untouched**, still true-modulo-named-gap and off the critical path |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**
Nothing here re-opens the habitat-level (AC-6) refutation (`C11` is
permanent), the (GR-10) min-max refutation ((GR-13) is untouched — (GR-19)
does not contradict it, because a *collapse* certificate is not a
polynomially-checkable characterization of the **triple**; it certifies the
weaker rank statement), or (GR-14)'s measured-nil applicability. No σ-fixed
witness is read as generic.

---

### What would change this

*(i)* **A bound on the collapse order.** A proof that `κ ≤ 4` (or `≤ 5`) at
every balanced block satisfying the counting conditions would turn (GR-19)
into a *finite* combinatorial criterion for `dim Z = 0`, replacing (GR-4′) on
the critical path and reducing (GR-15) to a single colouring-existence
statement over an order-4 certificate — a statement with far more slack than
(GR-10)'s. The measured `κ ≤ 4` on the census pool is the evidence; the
obstruction is that no argument here bounds `κ`.

*(ii)* **A characterization of when `r` co-independent groups certify.** At
`r = 3` co-independence *is* the certificate ((GR-9)). At `r = 4` it is
necessary and the residue is a determinant; 257 of the exemplar's
4-partitions are co-independent and at least one certifies. A combinatorial
criterion separating the certifying ones would make the whole hierarchy
combinatorial. Not a corollary of anything above.

*(iii)* **The grouping half of (GR-18).** An exchange argument showing that
some 6-tree decomposition of `Ĝ` admits a length-compatible 3+3 split and a
consistent hub colouring would prove (GR-10), hence (GR-15). The packing
exists unconditionally; the split is an equitable-bisection problem on 6
elements against the branch hypergraph, and matroid-union exchange is the
natural tool (Phase-12/13/14 machinery, per §(K-slide-comb) (C6) remark (b)).

*(iv)* **The `Λ ≠ ∅` half of (GR-17)(d).** The binding-profile list is proven
only when no hub-hub edge lies off the circuit. A circuit with a long
`Γ_A`-path off it could in principle merge runs below 3 at
`Σ(ℓ−1) ≥ 5`; none occurred in 1 158 344 instances. Either a proof (girth 7
plus `hcard` bounding `Λ`-paths against the branch-length budget, the
(FR-12) style of argument) or a witness would close the clause.

*(v)* **A structural flank.** A tight class shape whose *every* admissible
colouring leaves `dim Z > 0` in some block refutes (GR-15). After (GR-16)
this is a search over `(G°, ℓ, bits)` and is cheap per shape; the natural
places to look are the two binding circuit profiles of (GR-17)(d) — shapes
whose `G°` is rich in `(2,2,3)` and `(2,2,2,2)` circuits sharing branches, so
that the `h_≠ ≥ 2` requirements conflict — and hub multigraphs with many
parallel branch pairs. `--wide` sampled both and found nothing; a targeted
adversarial construction has not been attempted.

*(vi)* **(GR-4′).** Unchanged: a proof would make (GR-15)'s per-block
criterion a counting theorem and reduce the tight stratum to one
colouring-existence statement about `a = 0 ∧ max_P g(P) ≤ 0` — which
(GR-16)/(GR-17) have now made a statement about `(G°, ℓ, bits)`.

### Steps G24–G28 (2026-08-07, direction CFLANK) — the targeted flank against (GR-15) does **not** exist where TCOL said to look, and the reason is an exact **length-budget law**: `Σ_β(ℓ_β − 2) = 2·Σ_v(deg v − 3) + 6` pins the binding-circuit-rich stratum to the **cubic** hub multigraphs, five caps bound how many binding circuits the habitat can carry there, a **flip injection** and a **private-branch repair theorem** turn NC1-satisfiability from *measured* into *proven* at every shape reached, and **40 742 class shapes** of that stratum — exhaustive over length profiles and over all `2^M` branch bits — every one carries an admissible colouring at generic `dim Z₊ = dim Z₋ = 0`

Answering `notes/Pencil-fanout-archive.md` §"Sixth direction — CFLANK", i.e. §(K-grid)
*Step G23*'s *What would change this* item **(v)** — "a targeted adversarial
construction has not been attempted". Read against *Steps G19–G23*
((GR-16)/(GR-17)/(GR-18)/(GR-19)/(GR-20)), *Steps G8–G18* ((GR-7)/(GR-8)/
(GR-9)/(GR-10)/(GR-15)), §(K-clos) (AC-6)/(AC-9), §(K-frame) (FR-10)(i),
§(K-ind) (I1)/(I4), and the *Shared dictionary*'s (R3)/(R4)/(SD-6).

**Headline, stated before the mathematics.**

- **No flank, and the obstruction is named — most of it proven, not
  measured.** TCOL named two places to look: `G°` rich in `(2,2,3)` and
  `(2,2,2,2)` circuits sharing branches so the `h_≠ ≥ 2` requirements
  conflict, and hub multigraphs with many parallel branch pairs. Both are
  now closed: the first by (GR-21)–(GR-24) plus an exhaustive sweep, the
  second outright — **two parallel length-2 branches are never sparse**, so
  a parallel pair costs three units of a six-unit global budget.
- **(GR-21) the excess law.** At every tight class shape,
  `Σ_β (ℓ_β − 2) = 2·D + 6` with `D := Σ_v (deg_{G°}(v) − 3)`. So the whole
  length budget above "every branch is a single subdivided edge" is
  **`2D + 6`, independent of `n_hub`**, and every unit of hub degree above
  cubic costs two of it. Since a binding circuit needs
  `Σ_{β∈γ}(ℓ_β − 2) ≤ 4 − r ≤ 1`, the binding-circuit-rich stratum is
  exactly `D = 0`. Asserted at 907/907 census shapes and at 4920/4920
  constructed pool shapes.
- **(GR-22) five caps on how many binding circuits the habitat allows.**
  Write `H` for the sub-multigraph of length-2 branches. Then `H` is
  **simple**; **no two hubs have three common `H`-neighbours**; two binding
  triangles share **at most a length-1 branch** (so at `Λ = ∅` they are
  branch-disjoint); the `(2,2,2,2)` circuits are exactly the 4-cycles of `H`
  and number `½ Σ_{u<w} C(j^H_{uw}, 2) ≤ ¼ Σ_v C(deg_H v, 2) ≤ ¾ n_hub` at
  `D = 0`; and `T ≤ #{ℓ = 3} ≤ 2D + 6`. Every clause is a two-line sparsity
  computation, and every clause is asserted shape by shape.
- **(GR-23) the flip injection, and a *proven* NC1 criterion.** Flipping the
  bits of an independent set of **even** branches of a binding circuit
  carries an admissible NC1-violating colouring to an admissible
  NC1-passing one, injectively. Hence at most `1/3` of admissible colourings
  are bad at a given binding triangle and at most `1/4` at a given
  `(2,2,2,2)` circuit, so **`4T + 3Q < 12` implies NC1 is satisfiable**. On
  the census and on the whole `D = 0` stratum the load `4T + 3Q` never
  exceeds **8**.
- **(GR-24) the private-branch repair theorem, which has no bound at all.**
  If every binding circuit owns an even branch lying in no other binding
  circuit, the violated circuits can be repaired **simultaneously and
  independently**, so NC1 is satisfiable however many there are. The
  hypothesis holds at **4920/4920** shapes of the `Λ = ∅` stratum, and it is
  what carries the two families where (GR-23) provably runs out: the ladder
  `CL8` (`4T + 3Q = 12`) and the truncated prism (`T = 6`, the (GR-21) cap,
  `4T = 24`).
- **(GR-25) the cut criterion.** At `D = 0`, habitat membership is
  `2·∂(W') + Σ_{E(W')}(ℓ − 2) ≥ 7` for every proper `W'` inducing a
  connected subgraph with `|W'| ≥ 2`, plus `hcard`. Asserted **equivalent**
  to the canonical `gridcol.class_shape` at 16 270 + 1 294 shapes. It is a
  `2^{n_hub}` test where the canonical one is `2^M` with a matroid rank
  inside, and it is what makes the 18-hub / 45-vertex targets reachable at
  all.
- **The hunt itself.** `--cubic` + `--lam` + `--lam6` sweep **40 742 class
  shapes** of the `D = 0` stratum — every hub multigraph up to isomorphism
  at `n_hub ∈ {2,4,6}`, every length profile *enumerated* (never sampled),
  every one of the `2^M` branch-bit patterns — and `--tight` carries 14
  named constructions up to **18 hubs / 51 vertices**. **Zero NC1-
  unsatisfiable shapes and zero (GR-15) misses**, each hit certified by an
  exact rational parameter point, which by (GR-7) remark (i) is a per-shape
  **proof** of (GR-15) at that shape.
- **What does NOT move.** (GR-15) stays **open** as a class statement;
  (GR-10) is untouched; (GR-4′) is untouched and off the critical path.
  Class uniformity of `hK` is untouched and **no gap-map *status* moves**.

**Notation (on top of *Steps G19–G23*).** `G` a tight class shape; `G°` the
hub multigraph on `n := n_hub` hubs with `M` branches of lengths
`ℓ_β ∈ [1,5]`, `c = M − n + 1`, `Σ_β ℓ_β = 6c`. `D := Σ_v (deg_{G°}(v) − 3)`
is the **hub-degree excess**; `exc(β) := ℓ_β − 2` and
`exc(F) := Σ_{β∈F} exc(β)` the **length excess**. `Λ` = the length-1
branches. `H := (V(G°), {β : ℓ_β = 2})`, `j^H_{uw}` the number of common
`H`-neighbours of `u, w`, `∂(W')` the number of branches of `G°` with
exactly one end in `W'`. `T` = the number of binding triangles, `Q` = the
number of binding 4-circuits (binding = `Σ_{β∈γ}(ℓ_β − 1) ≤ 4`, i.e. the
circuits (GR-17)(c) can obstruct). A **binding circuit is violated** by a
colouring when `min(D_A(γ), D_B(γ)) ≤ 2`, which by (GR-8) at `P = γ` and
(GR-16)(iv) at balance **proves** generic `dim Z > 0` in that block.

---

### Step G24 — (GR-21): the excess law, and why it locates the whole flank hunt

> **(GR-21)** *(proven; asserted at 907/907 census shapes and at every one of
> the 4920 constructed `D = 0` pool shapes, `--law`)* At a tight class shape,
> > `Σ_β (ℓ_β − 2) = 2·D + 6`,  `D = Σ_v (deg_{G°}(v) − 3) ≥ 0`.
>
> Equivalently `Σ_β (6 − ℓ_β) = 6(n − 1)` re-read through `2M = 3n + D`. In
> particular:
>
> **(i)** the number of branches of length `≥ 3` is at most `2D + 6 + |Λ|`;
> **(ii)** a binding circuit `γ` has `exc(γ) = Σ_{β∈γ}(ℓ_β − 2) ≤ 4 − r`, so
> **at most one** unit of excess at `r = 3` and **none** at `r = 4`;
> **(iii)** the binding-circuit-rich stratum is `D = 0` — cubic `G°` with a
> total length budget of exactly **6**, no matter how large `n` is.

*Proof.* Tightness `5|E| = 6(|V| − 1)` with `|E| = Σℓ` and
`|V| = n + Σ(ℓ − 1)` gives `Σ_β(6 − ℓ_β) = 6(n − 1)`, i.e.
`Σ_β(ℓ_β − 2) = 4M − 6n + 6`; substituting `M = (3n + D)/2` gives `2D + 6`.
(i): branches of length `≥ 3` contribute `≥ 1` each and length-1 branches
`−1` each. (ii) is `Σ_γ ℓ ≥ 7` (girth, (R3) + `hnoRigid`) minus `2r`. (iii)
is (ii) plus the observation that the budget is what pays for the long
branches. ∎

**Why this is the load-bearing step.** *Step G23* left (GR-15) as "a
statement about branch bits on a hub multigraph", and TCOL's item (v) asked
for shapes rich in binding circuits. (GR-21) says how rich they can be: the
excess budget is a **constant**, so a shape with many hubs is a shape whose
branches are almost all of length 2, and — crucially — a shape whose hubs
are almost all of degree 3. The census (884 of 907 at `D = 0`, all at
`n_hub ∈ {2,4}`) and `gridcol --wide` (whose `WIDE_PLAN` has no `(6,9)`
entry at all, and which samples length profiles) both miss this stratum
almost entirely; it is where the whole hunt belongs, and it is finite per
`n` because the excess distribution is a composition of 6.

---

### Step G25 — (GR-22): five caps, each a two-line sparsity computation

Throughout, sparsity + `hnoRigid` at a branch-closed set with hub set `W'`
(`q := |W'| ≥ 2`, proper) and branch set `F` reads

> `f(F) = Σ_{β∈F}(6 − ℓ_β) − 6(q − 1) ≤ −1`.

> **(GR-22)** *(proven; every clause asserted per shape at 907 census shapes
> and at every constructed shape, `--law`)*
>
> **(i) `H` is simple.** Two parallel length-2 branches give
> `f = 8 − 6 = 2 > 0`. (So TCOL's second named place to look — "hub
> multigraphs with many parallel branch pairs" — is closed at the source: a
> parallel pair needs `Σℓ ≥ 7`, hence `exc ≥ 3`, half the entire `D = 0`
> budget.)
>
> **(ii) No two hubs have three common `H`-neighbours.** Six length-2
> branches on `q = 5` give `f = 24 − 24 = 0 > −1`. Hence `j^H ≤ 2`.
>
> **(iii) Two binding triangles share at most a length-1 branch.** If they
> share `β`, then `Σ_F(6−ℓ) ≥ 11 + 11 − (6 − ℓ_β)` on `q = 4`, so
> `f ≥ 22 − (6 − ℓ_β) − 18 = ℓ_β − 2`; `f ≤ −1` forces `ℓ_β ≤ 1`. At
> `Λ = ∅` binding triangles are therefore **branch-disjoint**.
>
> **(iv) The `(2,2,2,2)` circuits are exactly the 4-cycles of `H`, and**
> > `Q_2 = ½ Σ_{u<w} C(j^H_{uw}, 2) ≤ ¼ Σ_v C(deg_H v, 2)`,
>
> the inequality by (ii); at `D = 0`, `Σ_v C(3,2) = 3n`, so
> `Q_2 ≤ ¾ n_hub`. **Any two binding 4-circuits share at most one branch**
> (sharing two adjacent branches is (ii); sharing two opposite ones is the
> same circuit), and at `D = 0` **each branch lies in at most two of them**
> (a second 4-circuit through `βuv` must use a different branch at `u` *and*
> at `v`, and a cubic hub has only two others).
>
> **(v) `T ≤ #{ℓ = 3} ≤ 2D + 6`** at `Λ = ∅`, by (iii) and (GR-21)(i).

**Measured (`--law`).** Over the 907 census shapes the load `4T + 3Q` peaks
at **8** (`T = 2, Q = 0`, at `K4(1,1,3,5,3,5)`); over the 4920 shapes of the
constructed `Λ = ∅` `D = 0` stratum its distribution is
`0:2350, 3:1213, 4:1080, 6:25, 7:144, 8:108` — again a maximum of **8**, and
`max T = max Q = 2`. The census's own hub-degree profile is `D = 0` at 884
of 907, then a long thin tail out to `D = 12`.

---

### Step G26 — (GR-23): the flip injection, and NC1 satisfiability as a *proven* criterion

> **(GR-23)** *(proven; the repair asserted at 222/222 violating colourings
> and the resulting bound asserted per binding circuit over the whole pool,
> `--adv` / `--dens`)* Fix a tight class shape with `Λ = ∅` and let `γ` be a
> binding circuit with branches `β_1, …, β_r` in cyclic order. Let `S` be a
> nonempty set of branches of `γ` that is **independent** in the cyclic order
> and consists of **even** branches. Then flipping the bits of `S`
> (*Step G12*(i)'s free bit, one per branch) sends
>
> > {admissible, violated at `γ`}  →  {admissible, not violated at `γ`}
>
> and the induced map on pairs `(x, S)` is at most `mult`-to-one, where
> `mult = 2` when `S` and its complement in `γ` are both allowed and `1`
> otherwise. Consequently, writing `N` for the number of admissible
> colourings and `N_γ` for those violated at `γ`,
>
> > `N_γ · (|𝒮| / mult + 1) ≤ N`, i.e. `N_γ ≤ N/3` at a `(2,2,3)` triangle
> > and `N_γ ≤ N/4` at a `(2,2,2,2)` circuit.
>
> Hence **`4T + 3Q < 12` ⟹ an NC1-passing admissible colouring exists**.

*Proof.* *Admissibility.* Balance is `Σ_{β odd} δ_β = 0` (*Step G20*'s
signed subset-sum), and flipping an **even** branch leaves `A(β) = ℓ_β/2`
untouched, so balance survives; both ruling classes stay forests because at
`Λ = ∅` a monochromatic cycle would have to lie inside `Λ` ((GR-17)(a)'s
proof); and no hub becomes monochromatic — at a hub `v ∈ γ` with exactly one
of its two `γ`-branches flipped the two `γ`-darts now differ, and
independence of `S` forbids flipping both, while hubs off `γ` see no change
because both ends of a branch of `γ` lie on `γ`.
*Repair.* `h_≠(γ)` after the flip is `2|S| ≥ 2` (each flipped branch
contributes its two ends, and independence keeps those `2|S|` hubs
distinct), so `runs(γ) = ((L − r) + h_≠)/2 ≥ (4 + 2)/2 = 3`, and at `Λ = ∅`
`D_A = D_B = runs` by (GR-17)(b).
*Injectivity.* If `x + 1_S = x' + 1_{S'}` with `x, x'` both violated at `γ`,
then `x + x'` is supported inside `γ` and lies in the direction space of the
violation locus, which is the constants on `γ`; so `S △ S' ∈ {∅, γ}`. The
first gives `S = S', x = x'`; the second is possible only when `S` and
`γ ∖ S` are both in `𝒮`, which is the `mult = 2` case.
*Counting.* `|𝒮|·N_γ ≤ mult·(N − N_γ)`. At a `(2,2,3)` triangle the even
branches are the two length-2 ones and every pair of a triangle is adjacent,
so `𝒮` is the two singletons, `mult = 1`, giving `2N_γ ≤ N − N_γ`. At a
`(2,2,2,2)` circuit `𝒮` is the four singletons plus the two opposite pairs,
`mult = 2`, giving `6N_γ ≤ 2(N − N_γ)`. ∎

**Measured (`--dens`).** Over the 2570 pool shapes carrying a binding
circuit (2847 binding circuits, 151 168 admissible colourings): the pooled
violation rate is **6.57 %**, the **median** per-circuit kill fraction is
**0.0667** and the **maximum** is **1/7 ≈ 0.1429** — against the proven cap
of 1/4. Every per-circuit instance of the bound is asserted, not just the
pooled figure. Read forward: an NC1-driven flank needs the kill fractions to
sum past 1 at a **single** shape, i.e. **more than 7 binding circuits** at
the measured density (and more than 3 at the proven one); (GR-22)(iv)(v) cap
that count at `T ≤ 2D + 6` and `Q ≤ ¾ n_hub`, and the exhaustive sweep never
found a shape past `4T + 3Q = 8`.

**The F13 adversarial witness (`--adv`).** A guard observed only passing is
untested, so the detector is exercised on a **constructed** shape it must
reject: `K4` with **every** branch of length 2. Its 24 admissible colourings
are **all** NC1-violating (0 pass), so the detector reports a miss — and the
miss is **correct behaviour**, exactly as at the θ(1,2,9) precedent under
§(K-clos) (AC-6). The witness is out of habitat on three counts:
`5|E| = 60 ≠ 54 = 6(|V| − 1)` (not tight), each of its four triangles is a
length-6 circuit (girth `< 7`), and each is a proper rigid subgraph
(`Σ(6 − ℓ) = 12 = 6(3 − 1)`, so `hnoRigid` fails). **Pinned counter-fact:**
(GR-17)(d)'s two-profile list is proven only under girth 7, and here the
binding profiles are `(2,2,2)` and `(2,2,2,2)`; it is the `(2,2,2)`
triangles — the ones the habitat forbids — that carry the kill, and at a
`(2,2,2)` triangle `L − r = 3` so (NC1) demands `h_≠ = 3`, a `3/4`-density
condition instead of `(GR-23)`'s `1/3`. **Negative control:** the same hub
graph inside the habitat, `K4(3,3,3,3,3,3)`, has 12 admissible colourings
and **all 12** pass NC1.

---

### Step G27 — (GR-24) the private-branch repair theorem, and (GR-25) the cut criterion

> **(GR-24)** *(proven; hypothesis asserted at 4920/4920 shapes of the
> `Λ = ∅` stratum and at all 14 named targets, `--cubic` / `--tight`)*
> Suppose every binding circuit `γ` of a tight class shape with `Λ = ∅` owns
> an **even** branch `b(γ) ∈ γ` lying in **no other** binding circuit. Then
> NC1 is satisfiable — **with no bound whatever on `T` or `Q`**.
>
> *Proof.* Take any admissible colouring and flip `b(γ)` for every violated
> `γ`, simultaneously. Each flip is (GR-23)'s singleton flip, so each
> preserves admissibility and repairs its own circuit. It disturbs no other
> binding circuit: flipping `b(γ)` changes `s_v = χ(β,v) + χ(β',v)` only at
> the two ends of `b(γ)` and only for the pairs containing `b(γ)`, and by
> privacy no other binding circuit contains it. The no-monochromatic-hub
> argument is local to `γ`'s own hubs and survives a simultaneous flip at a
> third branch of the same hub, because the two `γ`-darts there differ after
> the flip regardless. ∎

> **(GR-25)** *(proven; asserted **equivalent** to `gridcol.class_shape` at
> 16 270 (multigraph, excess profile) pairs of the `Λ = ∅` stratum and at
> 1 294 shapes with `Λ` included, `--law` / `--lam`)* At `D = 0`, and given
> (GR-21), a hub multigraph with lengths is a tight `def = 0` `hnoRigid`
> class shape in the habitat **iff**
>
> **(i)** `2·∂(W') + exc(E(W')) ≥ 7` for every proper `W'` with `|W'| ≥ 2`
> inducing a connected subgraph, and **(ii)** the length-1 branches form a
> subgraph of maximum degree `≤ 2` (`hcard`, (R4)).
>
> *Proof of (i).* For a branch-closed set with hub set `W'`, `q = |W'|`, and
> induced branch set `F`, cubicity gives `|F| = (3q − ∂)/2` and
> `Σ_F(6 − ℓ) = 4|F| − exc(F)`, so
> `f(F) = Σ_F(6−ℓ) − 6(q−1) = 6 − 2∂(W') − exc(F)`. Sparsity plus `hnoRigid`
> is `f ≤ −1`. Non-induced `F` only lowers `Σ_F(6−ℓ)`; disconnected `F` is
> handled component by component; a partial branch of `j` edges contributes
> `5j − 6j = −j < 0`. Girth is the `q = 2` and `q = 3` instances
> (`∂ = 2` needs `exc ≥ 3`, i.e. a digon of total length `≥ 7`; `∂ = 3` needs
> `exc ≥ 1`, i.e. a triangle of total length `≥ 7`), and the two-hub triangle
> ban follows from the digon instance. ∎

**Why (GR-25) matters operationally.** The canonical habitat certificate
`gridcol.class_shape` runs `kslide.no_rigid_branch_union`, a `2^M` scan with
an exact matroid rank inside; it is out of reach past `M ≈ 12`. (GR-25) is a
`2^{n_hub}` scan of `O(M)` arithmetic. It is **not** taken on trust: `--law`
asserts the two agree on **every** (multigraph, excess profile) of the
`D = 0` stratum at `n_hub ≤ 6`, and `--lam` re-asserts it with `Λ` included
at every `M ≤ 6` shape. Only after that does `--tight` use it to reach 18
hubs / 51 vertices.

**The 14 named targets (`--tight`), and what each is aimed at.** These are
constructions, not a pool: each is the shape the (GR-21)/(GR-22) analysis
singles out as a way to defeat one of the two proven criteria.

| target | `n_hub` | `T` | `Q` | `4T+3Q` | carried by |
|---|---|---|---|---|---|
| cube `Q3`, excess on two opposite top branches | 8 | 0 | 3 | 9 | (GR-23)+(GR-24) |
| cube `Q3`, excess `2+2+2` on the top square | 8 | 0 | 2 | 6 | both |
| Wagner `V8`, excess on two rim branches | 8 | 0 | 3 | 9 | both |
| Wagner `V8`, excess on two spokes | 8 | 0 | 0 | 0 | both |
| ladders `CL5`, `CL6`, `CL7` (two placements each) | 10–14 | 0 | 1–3 | 3–9 | both |
| **ladder `CL8`** (two placements) | 16 | 0 | **4** | **12** | **(GR-24) only** |
| **truncated `K4`** | 12 | **4** | 0 | **16** | **(GR-24) only** |
| **truncated prism** (`T = 6`, the (GR-21) cap) | 18 | **6** | 0 | **24** | **(GR-24) only** |

At every one of the 14, (GR-24)'s repair is run **constructively** on a
seeded admissible colouring, its output is asserted still admissible and
NC1-clear, and the repaired colouring is then certified at generic
`dim Z₊ = dim Z₋ = 0` by an exact rational point through **both** the branch
system (GR-16)(iv) and the landed `grid.dim_Z`. One placement — the cube
with the excess on two *adjacent* top branches — is rejected by (GR-25) and
reported as such rather than silently skipped.

**The cube is not a coincidence.** (GR-24)'s hypothesis can fail at a
binding 4-circuit `C = v_1v_2v_3v_4` only if each `v_iv_{i+1}` lies in a
second binding circuit. If all four seconds are 4-circuits, then writing
`y_i` for the third neighbour of `v_i` one gets `y_iy_{i+1} ∈ E(G°)` for all
`i` with every branch involved of length 2; the `y_i` are forced distinct
and of degree 3, so `G° = Q_3` **with all twelve branches of length 2** —
excess `0 ≠ 6`, contradicting (GR-21). The triangle analogue is the same
kind of computation: if both even branches of a `(2,2,3)` triangle
`v_1v_2v_3` are shared with binding 4-circuits, the six hubs
`{v_1,v_2,v_3,x,y,z}` carry at least eight branches, seven of them of length
2, so `∂ ≤ 2` and `exc ≤ 1` and (GR-25) gives `f ≥ 1 > −1`. That
computation, run as a construction, is why `--tight` contains a cube and a
Wagner graph and not a random sample: it is the only local configuration in
which the hypothesis could fail, and it does not survive the budget.

---

### Step G28 — (GR-26): the hunt, and where a flank could still live (hand-off)

> **(GR-26)** *(the exhaustive result; `--cubic` / `--lam` / `--lam6`)* Over
> the `D = 0` stratum at `n_hub ∈ {2, 4, 6}` — every hub multigraph up to
> isomorphism, every length profile **enumerated** (with `Λ = ∅` complete at
> all three, and `Λ ≠ ∅` complete at `n_hub ≤ 4` and at `|Λ| ≤ 1` for
> `n_hub = 6`), and **all `2^M` branch-bit patterns at each** — there are
> **40 742 class shapes**, and
>
> **(i)** not one has all its admissible colourings NC1-violating;
> **(ii)** every one of the 4920 `Λ = ∅` shapes satisfies (GR-23) or
> (GR-24), so NC1-satisfiability there is **proven, not measured**;
> **(iii)** every one of the 40 742 carries an admissible colouring at
> generic `dim Z₊ = dim Z₋ = 0`, exhibited by an exact rational point —
> which by (GR-7) remark (i) is a **per-shape proof of (GR-15)** at that
> shape.
>
> Of the 40 742, **35 822 have `Λ ≠ ∅`** and **1608 carry a binding circuit
> with no even branch at all** — the profiles `(1,1,5)` and `(1,3,3)`, where
> (GR-23)/(GR-24)'s balance-preserving flip **does not exist** and only the
> exhaustive scan carries the shape. Those 1608 are also the shapes where
> (GR-17)(d)'s binding list is only measured and where an off-circuit merge
> can push `D_A` below the run count; the driver therefore reads `D_A`, `D_B`
> off `grid.block_data` directly at every `Λ ≠ ∅` shape and never off the
> run count.

**Which mechanism actually killed the flank, said plainly.** Not the
sampling — the sampling only confirms. It is (GR-21): the length budget
`2D + 6` is a **constant**, while the number of admissible colourings grows
exponentially in `n_hub` (the `Λ = ∅` pool alone enumerated 284 512 of them
over 4920 shapes) and the number of binding circuits grows only **linearly**
(`Q ≤ ¾ n_hub`, `T ≤ 6` at `D = 0`), each killing at most a `1/4` — measured
`1/7` — fraction. The two named places to look are the two places the budget
is tightest, and the budget is exactly what stops them from being rich
enough. TCOL's item (v) is therefore **closed as a route**, not merely
searched.

**Where a flank could still live — the honest residual, in decreasing
order of plausibility.**

1. **A non-circuit (GR-8) obstruction.** (NC1) is only the `P = γ` member of
   the (GR-8) family, and *Step G23* already recorded (in a scoping probe)
   16 of 572 blocks with `a = 0`, (NC1) satisfied and a **structured**
   (GR-8) maximum of 1 — all on `Λ ≠ ∅` shapes. Everything proven here is
   about circuits; nothing here bounds `max_P g(P)` over general
   sub-multigraphs. A flank could be a shape whose every admissible
   colouring has `g(P) > 0` at some **non-circuit** `P`. That is the single
   most promising successor target, and it needs a (GR-22)-style cap on the
   *structured* (GR-8) family, not on circuits.
2. **`D > 0` with a large hub.** Everything above is `D = 0`. A shape with
   one hub of degree `k` spends `2(k−3)` of its budget but gains
   `C(k,2)` pairs at that hub, and at a degree-`k` hub the "two darts agree"
   event has probability `→ 1/2` rather than `1/3`, so (GR-23)'s constants
   degrade. The census's `D > 0` tail (23 shapes, out to `D = 12`) is
   swept by `--law` for the caps but not by the exhaustive hunt.
3. **`n_hub ≥ 8` at `Λ = ∅`.** The sweep stops at `n_hub = 6` because
   `gridcol.multigraphs` is exponential in the *pair* count. (GR-24) covers
   every shape whose binding circuits own private even branches, and the two
   configuration computations above say the hypothesis can only fail in a
   cube-like or over-dense local pattern; but "only fail there" is argued by
   hand for two cases and not exhaustively for the mixed
   triangle-meets-4-circuit case.
4. **`|Λ| ≥ 2` at `n_hub = 6`.** `--lam6` stops at `|Λ| ≤ 1` (24 846 of the
   142 740 length tuples); the remaining 117 894 are unswept. This is the
   cheapest gap to close — it is one longer run, not new mathematics.

---

### Verification (Steps G24–G28)

`notes/scripts/w4/cflank.py` (**new with this pass**, untracked; imports
`gridcol.py` / `packmm.py` / `grid.py` / `closure.py` read-only, plus the
catalogued §1 primitive `kbare_common.verts_of` — all already in
`gridcol.py`'s import closure. Exact ℚ for every asserted identity; GF(p)
only inside the imported `gridcol.block_generic_zero`, as a **certified
lower bound** for the rational rank, with an exact-ℚ recheck of the
attaining draw at **every** reported hit, through both the branch system and
the landed `grid.dim_Z`, per README §4 convention 2. Rngs seeded per mode,
seeds printed; no `set` is printed. Nothing samples a placement, so no
figure is a rate over sampled placements and `repin.star_generic` gates
nothing here, exactly as for `gridcol.py` / `gridwit.py` under §(K-clos)
(AC-9).)

Six local devices, each named as such in its docstring: `excess_profiles`
(exhaustive distribution of the `2D + 6` budget — deliberately **not**
`gridcol.length_profiles`, which enumerates length tuples and falls back to
seeded rejection sampling above a cap; an exhaustive claim is the whole
point of this pass); `length_tuples` (its `Λ`-admitting companion);
`hub_model` (the branch decomposition + circuits + binding walks in one
object); `cubic_habitat` ((GR-25), cross-validated against
`gridcol.class_shape` before any target relies on it); `private_even` /
`repair` ((GR-24)); and `one_admissible` (a single admissible colouring
drawn from the canonical `closure.alternation_classes`, needed because
`2^M` enumeration is out of reach past `n_hub = 6`). Nothing existing is
modified (`git diff --name-only` empty).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --law     #  161 s  (GR-21)/(GR-22) at 907 census + 4920 pool; (GR-25) 16270/16270
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --adv     #    4 s  (GR-23) 222/222 repairs; the F13 witness + counter-fact + control
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --cubic   #  155 s  the hunt at Lambda = empty: 4920 shapes, 284512 admissible colourings
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam     #    9 s  Lambda != empty at n_hub <= 4: 1294 shapes, all length tuples
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --lam6    # 1288 s  OVER THE 600 s CEILING (F15): n_hub = 6 at |Lambda| <= 1, 39448 shapes
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --dens    #   93 s  the kill density; (GR-23)'s bound asserted per binding circuit
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --tight   #    3 s  the 14 named targets, up to 18 hubs / 51 vertices
PYTHONHASHSEED=0 python3 notes/scripts/w4/cflank.py --validate#  384 s  all but --lam6
```

`--lam6` is the one **over-ceiling** invocation (dispatch-log **F15**): it
is started backgrounded first and collected before the turn ends, never
waited on. Every other mode, and `--validate` (384 s), sits inside the
600 s budget. **Every figure `--validate` computes is identical under
`PYTHONHASHSEED` 0 and 999; the only differing bytes are the two printed
elapsed-time annotations (`cflank.py:726`, `:914`), which are wall-clock and
inherently non-deterministic** — corrected here from the draft's overstated
"byte-identical" claim (coordinator-caught by actually running both seeds
and diffing; see `notes/dispatch-log.md`).

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-21) | `--law` | per shape: `Σ(ℓ−2) == 2·Σ(deg−3) + 6`, at all 907 census shapes and every constructed shape |
| (GR-22)(i) | `--law` | per shape: no two length-2 branches share both ends |
| (GR-22)(ii) | `--law` | per hub pair: `j^H ≤ 2` |
| (GR-22)(iii) | `--law` | per pair of binding triangles: every shared branch asserted of length 1 |
| (GR-22)(iv) | `--law` | per shape: `#(2,2,2,2)-circuits == ½ Σ_{u<w} C(j^H, 2)` — the counting identity, not an inequality |
| (GR-22)(v) | `--law` | per shape at `Λ = ∅`: `T ≤ #{ℓ=3} ≤ 2D + 6` |
| (GR-23) the repair | `--adv` | per NC1-violating admissible colouring of the pool: **some** nonempty independent even-branch flip is asserted to land back in the admissible set with that circuit repaired (222/222) |
| (GR-23) the bound | `--dens` | per binding circuit at `Λ = ∅`: `N_γ·(\|𝒮\|/mult + 1) ≤ N` computed from the exhaustive per-circuit violation count |
| (GR-23) the criterion | `--law` | `4T + 3Q < 12` asserted at every census and every pool shape |
| (GR-23) as a guard | `--adv` | the **constructed** all-length-2 `K4`: 24 admissible colourings, **0** NC1-passing, so the detector reports a miss; plus the pinned counter-fact and the in-habitat `K4(3,3,3,3,3,3)` control (12/12 pass) |
| (GR-24) | `--cubic`, `--tight` | hypothesis asserted at 4920/4920 pool shapes; at the 14 targets the repair is **run** and its output asserted admissible and NC1-clear |
| (GR-25) | `--law`, `--lam` | asserted **equivalent** to `gridcol.class_shape` at 16 270 (multigraph, excess profile) pairs and at 1 294 `Λ`-inclusive shapes; both directions, no skips |
| (GR-26)(i) | `--cubic`, `--lam`, `--lam6` | per shape: the exhaustive count of admissible colourings and of NC1-passing ones; a shape with the second zero and the first nonzero is printed as a MISS |
| (GR-26)(ii) | `--cubic` | per shape: `private_even is not None or 4T + 3Q < 12`, asserted |
| (GR-26)(iii) | `--cubic`, `--lam`, `--lam6`, `--tight` | per shape: an exact rational `sval` at which `dim_W_branch == 0` in both blocks, re-asserted through `grid.dim_Z` |
| the `Λ ≠ ∅` exactness | `--lam`, `--lam6` | at every `Λ ≠ ∅` shape the classes `D_A, D_B` are read off `grid.block_data`, never off the run count — so (GR-17)(d)'s unproven clause is never relied on |
| (GR-4′), (GR-10) | — | **untouched and not driver-testable here**: no mode probes either |

**Scratch probes (`notes/scripts/README.md`'s standing rule).** Five throwaway
probes were run during this pass and are **not retained**: the census
excess-law spot-check, an all-length-2 multigraph scan at `n_hub ≤ 6`
(measuring how many admissible orientations a maximal binding-circuit load
kills — `K_{3,3}` at nine binding 4-circuits kills 18 of 102), a
habitat-dropped NC1-unsatisfiability hunt over the girth-legal tight shapes
at `(n,M) ≤ (4,7)` (**0** unsatisfiable in 41 983 shapes), the F13 witness
search that produced the all-length-2 `K4` and the all-length-2 octahedron
(23 binding circuits, 1894 admissible colourings, 0 passing), and the
labelled-cubic-multigraph count behind *Step G28* item (iv). Every figure
those probes produced that any claim above rests on has been re-derived
inside `cflank.py`; the rest is orientation and is flagged as such here.

**Pool caveats, stated because the arc has been bitten by them.** The 40 742
is a count of **class shapes on labelled branch lists**, not of isomorphism
classes (README §4 convention 7): hub multigraphs are canonicalized up to
isomorphism by `gridcol.multigraphs`, but length profiles are enumerated on
a labelled edge list, so a graph automorphism permuting branches produces
duplicates. That inflates the count and costs time; it cannot manufacture a
missing shape, which is the direction an exhaustive **kill** hunt needs.
Coverage is exhaustive over *length profiles* and over *bits*, and complete
over hub multigraphs only at `n_hub ∈ {2,4,6}` — see *Step G28*'s residual
items 3 and 4 for exactly what is unswept.

---

### Confidence verdict (Steps G24–G28)

| | claim | standing |
|---|---|---|
| **(GR-21)** | the excess law `Σ(ℓ−2) = 2D + 6` | **proven** (two lines from tightness); asserted at 907 census + every constructed shape |
| **(GR-22)(i)–(v)** | `H` simple; `j^H ≤ 2`; binding triangles share at most a length-1 branch; the `(2,2,2,2)`-count identity; `T ≤ 2D + 6` | **proven** (each a sparsity computation at one branch-closed set); every clause asserted per shape |
| **(GR-23)** | the flip injection and `N_γ ≤ N/3` / `N/4`; hence `4T + 3Q < 12 ⟹ NC1 satisfiable` | **proven** at `Λ = ∅`; the repair asserted 222/222 and the bound asserted per binding circuit over the pool. **Not** proven at `Λ ≠ ∅` (an off-circuit merge can keep `D_A < runs` after the flip) |
| **(GR-24)** | private even branches ⟹ NC1 satisfiable, with no bound on `T`, `Q` | **proven** at `Λ = ∅`; hypothesis verified 4920/4920 on the stratum and at all 14 targets. Its *universality* on the habitat is **argued for two configurations and open in the mixed case** (*Step G27*, *Step G28* item 3) |
| **(GR-25)** | the cut criterion is habitat membership at `D = 0` | **proven**; asserted equivalent to the canonical oracle at 17 564 shapes with no disagreement |
| **(GR-26)** | 40 742 `D = 0` class shapes, exhaustive over bits: no NC1-unsatisfiable shape, no (GR-15) miss, each hit an exact-ℚ certificate | **proven per shape** (each certificate is an exact-point vanishing, hence a proof of generic vanishing by (GR-7) remark (i)); the *40 742/40 742* is a measurement over an enumerated finite set |
| **(GR-15)** | every tight class shape admits an admissible colouring with generic `dim Z₊ = dim Z₋ = 0` | **OPEN** — unchanged in status. The evidence is now 907 (census) + 7653 (TCOL `--wide`) + 40 742 (here, exhaustive over the binding-circuit-rich stratum) + 14 constructed large targets; the targeted flank **did not fire**, and item (v) of *Step G23* is closed as a route |
| **(GR-10)**, **(GR-4′)** | the tree-triple form; the per-block equality | **untouched** |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**
Nothing here re-opens the habitat-level (AC-6) refutation, the (GR-13)
min-max refutation, or (GR-14)'s measured-nil applicability. No σ-fixed
witness is read as generic: every `dim Z` figure is a rank of a combinatorial
matrix at rational parameters of a *constructed* grid point, exactly as in
*Steps G19–G23*.

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as TCOL's and PEX's, and for the same reason: everything above is a
statement about *colourings of a fixed graph* and about a *constructed*
σ-fixed configuration's rank, never about `PencilNondegFeasible G`. The
landed refutation `not_pencilNondegFeasible_of_triangle_two_hubs` is not in
tension with anything here — indeed the two-hub triangle ban is *used*, as
one clause of (GR-25).

---

### What would change this (Steps G24–G28)

*(i)* **A cap on the structured (GR-8) family, not just on circuits.** This
is the successor target. (GR-22) bounds how many *circuits* can be binding;
nothing bounds how many sub-multigraphs `P` can have `g(P) > 0`
simultaneously, and *Step G23*'s scoping probe already saw `a = 0`,
NC1-satisfied blocks with a structured (GR-8) maximum of 1. A (GR-22)-style
budget argument for `max_P g(P)` would either close (GR-15) at `D = 0` or
locate the flank that (NC1) cannot see.

*(ii)* **The mixed case of (GR-24)'s universality.** *Step G27* proves the
hypothesis cannot fail when a binding 4-circuit's four seconds are all
4-circuits (forces `G° = Q_3` at zero excess) or when a binding triangle's
two even branches are both shared with 4-circuits (forces an over-dense
6-set). The mixed case — a branch shared between a binding triangle and a
binding 4-circuit, chained — is not closed. Closing it would upgrade
(GR-24) from "verified on the swept stratum" to "**(NC1) is satisfiable at
every `D = 0`, `Λ = ∅` class shape**", which is a clean unconditional
theorem and would retire item (v) permanently.

*(iii)* **`D > 0`.** Every proven statement here is at `D = 0`. The
degradation is quantifiable: a degree-`k` hub makes the per-hub agreement
probability `(2^{k−1} − 2)/(2^k − 2) → 1/2` instead of `1/3`, so (GR-23)'s
constants worsen, while (GR-21) charges `2(k − 3)` units of budget. Whether
the trade is ever favourable to the adversary is a one-parameter question
and is not answered here.

*(iv)* **`|Λ| ≥ 2` at `n_hub = 6`, and `n_hub ≥ 8`.** Both are compute, not
mathematics: 117 894 unswept length tuples at `n_hub = 6`, and no affordable
enumerator for cubic multigraphs at `n_hub = 8` (`gridcol.multigraphs`
distributes `m` over all `C(n,2)` pairs with the degree test only at the
leaf). A degree-pruned generator with isomorphism rejection would open
`n_hub = 8` and `10`; the counts say ~190 050 **labelled** cubic multigraphs
at `n_hub = 8`, so the dedup is the whole cost.

*(v)* **A `Λ`-side flip.** (GR-23)/(GR-24) need an **even** branch, and 1608
of the swept shapes carry a binding circuit — profile `(1,1,5)` or
`(1,3,3)` — with none. A balance-preserving repair there would have to flip
a *pair* of odd branches with opposite `δ`, and the second one need not be
on the circuit; whether such a pair always exists is open, and it is exactly
what would extend both theorems to `Λ ≠ ∅`, where (GR-17)(d) itself is only
measured.

*(vi)* **The one thing that would refute all of it:** a class shape at which
some binding circuit is violated by **every** admissible colouring, or (the
weaker and now more likely form) at which every admissible colouring leaves
`max_P g(P) > 0` for a non-circuit `P`. The detector for the first exists
and is exercised on a constructed witness it must reject (`--adv`); the
detector for the second does **not** exist yet — building it is item (i).

### Steps G29–G33 (2026-08-12/13, direction GCAP) — the (GR-8) family is exactly computable, *Step G23*'s probe becomes committed evidence **with its `Λ`-clause corrected**, a closed **defect formula** turns `max_P g(P)` into branch-bit arithmetic at `Λ = ∅`, NC1 caps the binding family at **`g = 1`** (proven at `k = 2`, exhaustive at all `k`), and the certificate-3 colouring-existence target holds at **every swept `D = 0` shape** with repair distance ≤ 2 — but the uniform existence statement, and with it (GR-15), stays **OPEN**

Answering `notes/Pencil-fanout-archive.md` §"Seventh direction — GCAP", i.e.
*Step G28* residual item 1 / *What would change this (Steps G24–G28)*
item (i): the general-`P` instance of *Step G23* (GR-20)'s certificate 3,
cap-proof-first. Read against *Steps G8–G13* ((GR-7)/(GR-8)/(GR-4′)),
*Steps G19–G23* ((GR-16)/(GR-17)/(GR-20)), *Steps G24–G28*
((GR-21)–(GR-26)), §(K-clos) (AC-4)/(AC-7)/(AC-9), and the *Shared
dictionary*'s (R3)/(R4)/(SD-6).

**Step 0 pin (mandatory, discharged before any derivation).** `g(P)` is
(GR-8)'s functional: for a sub-multigraph `P` of the contracted multigraph
`H₊`, `g(P) = 3·dim C(P) − Σ_X r_X(P)` with
`r_X(P) = dim C(P) − dim C(P∖X)`, and `dim W ≥ g(P)` at **every**
parameter assignment, hence `dim Z ≥ g(P)` at balance. "Structured" in
*Step G23* and *Step G28* item (i) means the two computable witness
families of `gridwit.structured_beta` — class unions and node-induced
subgraphs — a **proper subfamily** of all `P`, hence a lower bound for
the true maximum; (GR-27) below supersedes it with an exact computation
on every pool this pass touches. (GR-4′)'s proven-case boundary is
**≤ 3 classes total, or all classes singletons** (*Step G9*); a habitat
block at `c ≥ 2` has `Σ_β |K_A(β)| = 3c ≥ 12` class incidences with
non-singleton hub-star classes, so **neither proven case covers a single
habitat block** and the (GR-4′) rider below is genuinely load-bearing.
The target as specified is correctly stated against these definitions; no
re-aim was needed.

**The closure chain, with both riders, stated before anything is
claimed.** A cap/existence theorem "every tight class shape at `D = 0`
admits an admissible colouring with `a = 0 ∧ max_P g(P) ≤ 0` in both
blocks" implies (GR-15) at `D = 0` **modulo (GR-4′)** (certificate 3 of
(GR-20); (GR-4′) stays open and off the critical path, and its proven
cases exclude every habitat block, so the rider never dissolves silently);
(GR-15) at `D = 0` + (GR-1)/§(K-clos) (AC-4) + (GR-5) + (AC-7) would
discharge `hK` on the tight `D = 0` stratum over every infinite
characteristic-0 field; **`D > 0` stays unswept** (*What would change
this (Steps G24–G28)* item (iii)). Nothing here closes (GR-15) outright,
and nothing below claims to.

**Headline, stated before the mathematics.**

- **(GR-27): the (GR-8) family is block-additive and exactly
  computable.** `g` is additive over the 2-edge-connected blocks of `P`,
  bridges contribute `0`, and every 2-edge-connected `P` is a union of
  full branch paths — so `max(0, max_P g(P))` over **all** sub-multigraphs
  is an exact finite computation over branch subsets, and the "structured"
  proxy is retired on every pool this pass sweeps.
- **The *Step G23* probe is re-established as committed evidence — and
  corrected.** The recorded figure reproduces **exactly**: over the first
  45 census shapes, 572 balanced no-mono-hub NC1-satisfying colourings =
  1144 blocks, of which **16** have generic `dim Z > 0`, each `a = 0`,
  structured max = exact max = 1, all on `Λ ≠ ∅` shapes. But the "all on
  `Λ ≠ ∅` shapes" clause is a **sample-bias artifact** of the 45-shape
  prefix: over the full census, 675 of 955 hit blocks live on
  **`Λ = ∅`** shapes. The binding non-circuit family is not a
  `Λ ≠ ∅` phenomenon.
- **(GR-28): at `Λ = ∅`, `max_P g(P)` is a closed formula in the branch
  bits.** For a connected 2-edge-connected branch subset `S`,
  `g_A(S) = 3 − defect_A(S)` with
  `defect_A(S) = Σ_{β∈S}(A(β) − 1) + #{degree-2-in-S hubs whose two
  S-darts are not both A}`; `a = 0` holds at **every** admissible
  colouring of a `D = 0`, `Λ = ∅` shape; NC1 is exactly the circuit
  (`k = 1`) instance `defect ≥ 3`; and NC1 forces `defect(S) ≥ 2` at
  every theta (`k = 2`), i.e. **binding thetas have `g = 1` exactly,
  with path costs `(1, 1, 0)`** — proven. At `k ≥ 3` the same cap
  `max g ≤ 1` is **measured with zero exceptions** over the swept
  stratum (549 172 NC1-passing blocks) and the census; the `k ≥ 3` proof
  was this pass's named gap, and is **REFUTED since direction GUNIF**
  (*Steps G34–G37*): the cap is a **theorem exactly at `n_hub ≤ 6`**
  ((GR-29)) and **false from `n_hub = 8` on** ((GR-30)) — the sweep here
  covers exactly the `n_hub ≤ 6` stratum, which provably cannot exhibit
  the failure.
- **The certificate-3 target holds at every swept `D = 0` shape.** Some
  admissible colouring has `a = 0 ∧ max_P g(P) ≤ 0` (exact, all `P`) in
  both blocks at 4920/4920 `Λ = ∅` pool shapes, 884/884 census `D = 0`
  shapes (`Λ` mixed), and 972/972 `Λ ≠ ∅` `n ≤ 4` shapes — at 4029, 838
  and 924 of them respectively already at the **first** admissible
  colouring. Every binding colouring of the `Λ = ∅` stratum reaches a
  fully-good one by **at most two balance-preserving even-branch flips**
  (22 654 at distance 1, 1296 at distance 2, 0 beyond), and the
  no-even-branch binding circuits — CFLANK item (v), live only from
  `n = 6` — are repaired by the **balance-preserving odd-pair flip** at
  178/178 constructed violated instances.
- **The falsification control found no flank, and the g-detector now has
  its F13 witness.** 323 binding-rich constructions swept exhaustively
  over bits all keep a fully-good colouring (worst binding rate 0.179);
  and `θ(2,4,4)` — out of habitat, with a two-line hand proof — is a
  shape **every** admissible colouring of which has `max g > 0` while NC1
  is satisfiable: the detector *Step G28* item (vi) said did not exist is
  built, exercised on a witness it must reject, with the pinned
  counter-fact (the NC1 detector passes it) and an in-habitat control.
- **What does NOT move.** (GR-15) stays **OPEN** — the uniform
  colouring-existence statement (all `n_hub`) is not proven, no flank was
  found, and no gap-map *status* moves. (GR-4′), (GR-10) untouched.

**Notation (on top of *Steps G19–G28*).** One block at a time, `mine =
A`; everything dualizes. For a branch `β`, `A(β) = |E_A ∩ β|`; a branch's
two **darts** are the colours of its two end edges. For a branch subset
`S` of `G°` (at `Λ = ∅`; of `G°/Γ_B` in general), `P_S ⊆ H₊` is the union
of its branches' A-paths; `b = |S|`, `q` its hub count, `k = b − q + 1`
its cycle rank when connected. A subset/block is **binding** when
`g > 0`. `defect_A(S)` as in the headline; a **cost-0 path** of `S`'s
core-path decomposition is one with every branch at `A(β) = 1` and every
interior hub with both darts A.

---

### Step G29 — (GR-27): block additivity, and the exact computation that retires the structured proxy

> **(GR-27)** *(proven; formula-vs-`subgraph_g` cross-validated at 16 823
> seeded (block, subset) pairs, `--law`)* Fix a colouring-block. For any
> sub-multigraph `P ⊆ H₊`:
>
> **(i)** `r_X(P) = |X ∩ E(P)| − (comp(P∖X) − comp(P))`, hence
> `g(P) = 3·dim C(P) − |E(P)| + Σ_X Δcomp_X(P)` with
> `Δcomp_X(P) := comp(P∖X) − comp(P) ≥ 0`.
>
> **(ii) Block additivity.** `g(P) = Σ_B g(B)` over the 2-edge-connected
> blocks `B` of `P`; bridges and acyclic parts contribute `0`. In
> particular `max(0, max_P g(P))` is attained on 2-edge-connected `P`.
>
> **(iii) Branch support.** Every 2-edge-connected `P ⊆ H₊` is a union of
> **full branch A-paths** — it is `P_S` for a branch subset `S` of
> `G°/Γ_B` (of `G°` at `Λ = ∅`) that is 2-edge-connected after the
> `Γ_B`-contraction.
>
> Hence `max(0, max_P g(P))` over **all** sub-multigraphs equals the
> maximum of `g(P_S)` over branch subsets — a finite exact computation
> per block (`2^M` subsets, `subgraph_g` cycle-rank arithmetic, no rank
> over ℚ) — and on an NC1-passing block it suffices to scan the
> 2-edge-connected-after-contraction subsets with `k ≥ 2`, since a
> binding `k = 1` block is exactly an NC1 violation.

*Proof.* (i): `dim C = |E| − |V| + comp` on a fixed node set, applied to
`P` and `P∖X`. (ii): every cycle of `P` lies in one 2-edge-connected
block, so `C(P) = ⊕_B C(B)` and likewise `C(P∖X) = ⊕_B C(B∖X)` (a cycle
of `P∖X` is a cycle of `P`); hence `r_X` and `g` are sums over blocks. A
bridge `e` is its own block with `dim C = 0` and every `r_X = 0`.
(iii): a non-hub node of `H₊` has degree 2 ((GR-16)(ii)), so a cycle
through one interior edge of a branch traverses the branch's whole
A-path; in a 2-edge-connected `P` every edge lies on a cycle. ∎

**What this retires.** *Step G23*'s probe and *Step G28* item 1 could
speak only of the **structured** (GR-8) maximum — `structured_beta`'s two
witness families, a lower bound. (GR-27) makes the full maximum an exact
per-block figure. Measured: at every one of the 45-prefix probe's 16 hit
blocks, structured max = exact max = 1 (`--probe`), so nothing recorded
in *Step G23* moves; the gain is that "the (GR-8) maximum" now means the
real thing everywhere below.

---

### Step G30 — the *Step G23* scoping probe as committed evidence, and the correction of its `Λ`-clause

*Step G23* recorded its probe as *"measured in a scoping probe … script
not retained … the figure is orientation, not evidence"*. `--probe`
re-establishes it as evidence, with each side of the classification
**proven** rather than sampled: a hit block carries an explicit (GR-8)
witness `P` with `g(P) ≥ 1` (a proof of generic `dim Z ≥ 1` at balance,
valid at every parameter assignment), and a clean block carries an exact
rational parameter point with `dim Z = 0` through both the branch system
(GR-16)(iv) and the landed `grid.dim_Z` (a proof of generic vanishing by
(GR-7) remark (i)). A block failing both is retried at 6 further draws
(*Step G4* item 1, §(K-clos) (AC-9)) and would be reported as a
(GR-4′)-anomaly; **none occurred anywhere in this pass**.

**The reproduction (45-shape prefix, exactly as recorded).** 572
balanced, no-monochromatic-hub, NC1-satisfying colourings = 1144 blocks;
**16** with generic `dim Z > 0`; every hit `a = 0`, structured max =
exact max = **1**, all on `Λ ≠ ∅` shapes, every minimal witness a theta
(`k = 2`). *Step G23*'s "16 of 572" was a per-colouring count of the same
event; both readings are asserted.

**The full census, and the correction.** Over all 907 shapes: 32 388
NC1-passing admissible colourings = 64 776 blocks — 35 282 certified
`dim Z = 0` at exact points, **955 proven `dim Z > 0`**, and 28 539
formula-clean blocks at the census's two `> 4096`-colouring shapes
(`V6m14`, `V6m15`) carried by (GR-28)'s formula with a seeded 5 %
rank-certified sample; 0 unexplained. Of the 955 hits, **only 280 are on
`Λ ≠ ∅` shapes — 675 live at `Λ = ∅`**. *Step G23*'s "all on `Λ ≠ ∅`
shapes" clause is therefore a **sample-bias artifact**: the census
generator requires a length-3 branch and orders the `K4` stratum
lexicographically, so its 45-shape prefix is all `K4(1,…)`. The
dispatch-spec correction 1 (which relied on that clause to route the
direction toward `Λ ≠ ∅` first) loses its factual premise — the binding
non-circuit family is **not** a `Λ ≠ ∅` phenomenon, and the productive
stratum order is the one this pass ran: `Λ = ∅` law first.

**The decisive sub-question (finiteness of the binding family), answered
on the census.** Every hit has exact `gmax = 1` — none reaches 2. Minimal
witnesses have cycle rank `k ∈ {2, 3, 4, 5, 6}` (488/370/10/77/10) — the
`k ≥ 4` witnesses live outside the `D = 0`, `Λ = ∅` regime (on the
census's `D > 0` tail and its `Λ ≠ ∅` shapes: the `Λ = ∅` `D = 0`
stratum's own minimal witnesses are exhaustively `k ∈ {2, 3}`,
*Step G31*) — and realize **25 core-path length profiles** in total,
every one a union of core paths whose lengths the (GR-21) budget
`2D + 6` bounds. The family is finite per `D` exactly as
(GR-17)(d) bounded the binding circuits: bounded, enumerable, and now
enumerated.

---

### Step G31 — (GR-28): the defect formula at `Λ = ∅`, `a = 0` for free, and the `g ≤ 1` cap

> **(GR-28)** *(the formula and `a = 0` proven; the `k = 2` cap proven;
> the all-`k` cap measured exhaustively — 549 172 NC1-passing blocks of
> the `Λ = ∅` `D = 0` stratum with `max g` distribution
> `g = 0 : 523 476`, `g = 1 : 25 696`, `g ≥ 2 : 0`, `--law`)* Let `G` be
> a `D = 0`, `Λ = ∅` class shape with an admissible colouring, and `S` a
> connected 2-edge-connected branch subset of `G°`, `k = b − q + 1`.
>
> **(i) The closed form.**
> > `g_A(P_S) = 3 − defect_A(S)`,
> > `defect_A(S) = Σ_{β∈S}(A(β) − 1) + #{v : deg_S(v) = 2, not both
> > S-darts at v are A}`.
>
> Degree-3-in-S hubs contribute nothing. On a circuit (`k = 1`, all hubs
> degree-2) `defect_A(γ) = D_A(γ)`, so NC1 is exactly the `k = 1`
> instance "`defect ≥ 3`".
>
> **(ii) `a = 0` automatically.** At `D = 0` the cut criterion (GR-25)
> forbids a bridge of `G°` (each side would need excess ≥ 5 against a
> global budget of 6), so `H₊` — a subdivision of the cubic `G°` — is
> 2-edge-connected with maximum degree 3, hence 2-connected; a cut vector
> inside one class would be a bond of ≤ 2 edges at one hub (the
> mono-hub ban caps `j_v ≤ 2`), forcing that hub to be a cut vertex of
> degree 3 — impossible. So every admissible colouring of the stratum has
> `a = 0` in both blocks.
>
> **(iii) The `k = 2` cap, proven.** If the colouring satisfies NC1, then
> every theta `S` has `defect(S) ≥ 2`, i.e. `g(S) ≤ 1`; and a **binding
> theta has `g = 1` exactly, with path costs `(1, 1, 0)`** up to order.
>
> **(iv) The all-`k` cap, measured.** Over the whole stratum — 4920
> shapes, every admissible colouring, both blocks — no NC1-passing block
> has `max_P g(P) ≥ 2`; 25 696 blocks (4.68 %) on 2995 shapes are binding
> at `g = 1`, with minimal witnesses at `k = 2` (18 016) and `k = 3`
> (7680) realizing 35 core-path profiles, led by
> `((2,2),(2,2),(2,3))` (7776) and
> `((2),(2),(2,2),(2,3),(3),(3))` (2256).

**Forward pointer (2026-08-13, direction GUNIF).** (iv) as stated is
**REFUTED at `k ≥ 3`, with an exact boundary** — see *Step G35*
((GR-30)): four constructed habitat witnesses at `n_hub = 8, 10, 12, 16`
violate the cap; it survives as a **theorem** only on the swept
`n_hub ≤ 6` stratum, exactly (*Step G34*'s (GR-29) ledger).

*Proof of (i).* By (GR-27)(i), `g = 3k − |E(P_S)| + Σ_X Δcomp_X` and
`|E(P_S)| = Σ_S A(β)`. At `Λ = ∅` the classes are interior singletons and
single-hub stars ((GR-16)(iii)). A singleton on a non-bridge edge has
`Δcomp = 0`. A star class at `v` meets `P_S` in `j_v ≤ 2` edges (the
mono-hub ban excludes `j_v = 3`); if `deg_S(v) = 3` a positive `Δcomp`
would make the degree-3 node `v` a cut vertex of the 2-connected `P_S`
(2-edge-connected with max degree 3 forces 2-connected), impossible — so
`Δcomp_v = 0` there; if `deg_S(v) = 2` and both darts are A, deleting
both isolates `v` while `P_S − v` stays connected (2-connectivity), so
`Δcomp_v = 1` exactly; otherwise `j_v ≤ 1` and `Δcomp_v = 0`. Summing:
`g = 3k − Σ A(β) + aa₂(S)`, and substituting `b = q₂ + 3(k−1)` (from
`2b = 2q₂ + 3q₃`, `q₃ = 2(k−1)`) gives the defect form. ∎

*Proof of (iii).* A **cost-0 path** has every `A(β) = 1` and every
interior hub AA. Two cost-0 paths between the same core pair form a
circuit `γ` whose defect is `0 + 0 +` (its two corner hubs' non-AA
indicators) `≤ 2 < 3` — an NC1 violation. So under NC1 a theta has at
most one cost-0 path, hence `defect(θ) = Σ` (three path costs) `≥ 2`,
with equality only at costs `(1,1,0)`. ∎

**Why the cap does not yet extend to `k ≥ 3` by the same argument.** At
`defect(S) ≤ 1`, at least `3(k−1) − 1` of the core paths are cost-0, and
`3(k−1) − 1 > 2(k−1) − 1` forces a **circuit of cost-0 paths** in the
core; a 2-path circuit is dead by the argument above, but a `t ≥ 3`
circuit of cost-0 paths has defect = its non-AA **corner** count, which
NC1 only requires to be ≥ 3 — corners are free in `defect(S)` (they are
degree-3-in-S hubs). The mono-hub ban still constrains the dart menus
(cost-0 paths have length ≤ 4 and present an A-dart only when they are a
single length-2 branch), and every hand-attempt to realize `defect ≤ 1`
died on it, but the finite dart-menu case analysis is **not closed** in
this pass; the all-`k` cap stood as *true-modulo-named-gap* on the
exhaustive stratum sweep as its evidence. **RESOLVED 2026-08-13 (*Steps
G34–G37*, direction GUNIF): the case analysis IS closed ((GR-29)) and the
all-`k` cap is REFUTED** — the degree of freedom this paragraph describes
(a `t ≥ 3` circuit of cost-0 paths whose corners are free) is exactly
where the failure lives, realized from `n_hub = 8` on ((GR-30)); the cap
survives as a **theorem** exactly on the swept `n_hub ≤ 6` stratum.
A useful handle for the successor, recorded: for an open
ear `E` on `P`, `g(P ∪ E) = g(P) + 3 − #{X : X` breaks `E` or separates
its feet in `P∖X}` — the ear-law form of (GR-27)(i) — so `max g ≤ 0`
propagates whenever every ear carries three "cutting" classes; NC1 is its
base case.

**Consistency notes.** (a) `n_hub = 2` (theta shapes) carry **no**
binding block, by hand from (i): the stratum's three iso classes are
`θ(2,5,5)`, `θ(3,4,5)`, `θ(4,4,4)`; each path is a single branch, and at
every bit choice with total cost ≤ 2 some hub's three darts are all B —
e.g. at `θ(2,5,5)`, cost `(0,1,1)` forces both length-5 branches B-ended
and the length-2 branch's B-dart completes a mono hub. (The `--law`
sweep covers these shapes; its binding blocks all sit at `n ≥ 4`.) (b) The two `Γ`-class-forest conditions are automatic at `Λ = ∅`
((GR-17)(a)'s proof), so admissibility here is balance + no mono hub,
exactly `cflank.admissible`.

---

### Step G32 — the certificate-3 target at `D = 0`: measured everywhere, repair distance ≤ 2, and the odd-pair flip at CFLANK item (v)

**The target statement** (the general-`P` instance of (GR-20)'s
certificate 3): *every tight class shape at `D = 0` admits an admissible
colouring with `a = 0 ∧ max_P g(P) ≤ 0` in both blocks.* By (GR-8)'s
proven `≥` direction, any exact-point `dim Z = 0` certificate implies it
per shape — so (GR-26)(iii) already implied its measured truth on the
40 742-shape stratum; what `--cap` adds is the **direct combinatorial
verification** (exact `max_P g(P)` by (GR-27), `a` by `a_and_M`, no rank)
with first-hit statistics, on three pools:

| pool | shapes | target holds | first admissible colouring already good |
|---|---|---|---|
| `Λ = ∅` `D = 0` stratum (CFLANK's `--cubic` pool) | 4920 | 4920/4920 | 4029 (then 632/130/82/44/3 at indices 2–6) |
| census `D = 0` (`Λ` mixed) | 884 | 884/884 | 838 (then 44/2) |
| `Λ ≠ ∅`, `n ≤ 4`, all length tuples | 972 | 972/972 | 924 (then 48) |

with the g-certificate cross-checked against an exact rational
`dim Z = 0` point through both matrices at 68 seeded shapes. **No MISS.**

**Repair distance (`--flip`, half 1).** Over the `Λ = ∅` stratum, 23 950
admissible NC1-passing colourings are binding in some block; **every
one** reaches a fully-good colouring (a = 0 ∧ max g ≤ 0 both blocks) by
balance-preserving flips of at most two **even** branches — 22 654 at
distance 1, 1296 at distance 2, 0 unrepaired. This is the (GR-23)-shape
locality statement for the g-family: the binding obstruction is not just
avoidable somewhere in the bit cube, it is avoidable **locally** from any
NC1-passing start. (A proof-grade repair theorem — the analogue of
(GR-24) with a private-branch hypothesis — is not attempted here; the
measured distance-≤-2 bound plus (iii)'s witness characterization are its
raw material.)

**Scope note (2026-08-13, direction GUNIF, *Step G36*).** This
measurement is **sweep-local**: the `Λ = ∅` pool it ran over sits
entirely at `n_hub ≤ 6` (*Step G34*'s ledger), and the "≤ 2" bound is
**false beyond the sweep** — it breaks at `n_hub = 16` (W5, distance 3,
`g = 3`; *Step G36*(ii)). The measurement itself is not deleted, only
its scope: on the swept stratum it still stands.

**CFLANK item (v), the odd-pair flip (`--flip`, half 2).** The binding
circuits with no even branch (profiles `(1,3,3)` and `(1,1,5)`) have
**no live instances at `n ≤ 4`**: 316 shapes of that pool carry such a
circuit, but 0 admissible colourings violate one. At `n = 6` — up to 150
constructed shapes per profile (the generator's cap, disclosed), a
targeted construction, not a pool widening — 178 violated (colouring, circuit) instances occur, and the
balance-preserving **odd-pair flip** (flip an odd branch of the circuit
plus an opposite-`σ` odd partner, which always exists since
`Σ_odd σ = 0`) repairs **178/178** while preserving admissibility. Item
(v)'s mechanism therefore works where it is live; what stays open is only
its *theorem* form (privacy/disjointness hypotheses under which the
simultaneous repair is guaranteed), the exact analogue of the (GR-24)
mixed-case gap.

**Where the chain now stands.** Everything measured above is per-shape
**proof** (exact points / exact combinatorial maxima), so the target
statement is proven on every swept shape and open only in its **uniform**
(all-`n_hub`) form. Modulo that uniformity gap, the chain of the Step-0
pin applies verbatim — and never without its two riders: certificate 3
implies (GR-15) at `D = 0` **modulo (GR-4′)**, and `D > 0` is unswept.

---

### Step G33 — the falsification control, the F13 witness for the g-detector, and where a flank could still live (hand-off)

**The control (`--adv` part (i)).** 323 constructions aimed at the
analysis' own worst case — K4s carrying the whole excess budget, prisms
and `K_{3,3}`s with paired length-5 branches (the K4-minus-a-branch
binding-theta pattern stacked as densely as (GR-22) allows) — swept
exhaustively over all `2^M` bits: **every one keeps a fully-good
colouring**; the worst binding rate is 10 of 56 admissible colourings at
`prism(5,2,2,2,5,2,2,2,2)`. No flank.

**The F13 witness (`--adv` part (ii)).** *Step G28* item (vi) recorded
that the detector for "every admissible colouring leaves `max_P g(P) > 0`
at a non-circuit `P`" did not exist. It exists now, and per README §4
convention 6 it is exercised on a constructed witness it must reject:
**`θ(2,4,4)`** — found by a deterministic lexicographic search re-run on
every invocation, and provable by hand: both length-4 paths have
bit-independent cost `A(β) − 1 = 1`, so (GR-28)(i) pins
`g(θ) = 3 − 2 = 1 > 0` at **every** admissible colouring, while NC1 is
satisfiable (2 of its 6 admissible colourings pass — the corner darts can
be arranged). It is out of habitat on two counts (not tight:
`5|E| = 50 ≠ 48`; girth 6 < 7), so the miss is correct behaviour, exactly
as the all-length-2 `K4` was for the NC1 detector. **Pinned
counter-fact:** the NC1 detector — (GR-26)(i)'s criterion — PASSES
`θ(2,4,4)`, so the g-detector is strictly stronger, which is precisely
why item (i) of *What would change this (Steps G24–G28)* asked for it.
**Negative control:** `K4(3,3,3,3,3,3)` (in habitat) is accepted end to
end. The witness's binding block is re-confirmed through the exact
`subgraph_g` and by the absence of any `dim Z = 0` draw.

**Where a flank could still live — the honest residual, updated from
*Step G28*'s list.** **Superseded 2026-08-13 (direction GUNIF) — see
*Step G37* for the current hand-off; items 1–2 are corrected/resolved
below rather than deleted, per the note at each.**

1. **The uniform existence gap.** Everything is proven per swept shape;
   nothing bounds the first-good-colouring index or proves the ≤-2-flip
   repair in general. A flank would be a `D = 0` shape whose every
   admissible colouring is binding — the control says the known
   mechanisms cannot stack densely enough (~~the same (GR-21)
   constant-budget mechanism that killed the NC1 flank kills this one:
   binding needs `defect ≤ 2`, and defect units are bought with the same
   excess budget the circuits compete for~~), but that is an argument, not
   a theorem. **Correction (2026-08-13, *Step G36*'s caveat): the struck
   mechanism is WRONG AS STATED** — *Step G35*'s W5 witness has a binding
   subset with **zero excess and zero defect** (cost-0 paths are
   excess-free), so the (GR-21) budget never charges it. What binding at
   `g ≥ 2` actually costs (*Step G34*'s ledger) is **structure** — AA
   interiors with B-forced exits, a (GR-25)-shaped boundary, and a
   balance partner — not excess inside `S`; *Step G36* names the
   exact-alignment thinness observation as the successor's raw material.
   Separately, this item's own premise is now refuted at `n_hub ≥ 8`
   (*Step G35*): four `D = 0` shapes fail the swept-stratum cap, though
   every one keeps abundant fully-good colourings (*Step G36*(i)) — none
   is the existence-gap flank this item hunted for.
2. **The `k ≥ 3` cap gap** ((GR-28)(iv)): a `defect ≤ 1` configuration at
   some `k ≥ 3` would give `g = 2` and break the repair calculus; the
   dart-menu analysis above localizes where it would have to live
   (a cost-0 core circuit with ≥ 3 non-AA corners, every core node
   mono-ban-fed by a single-ℓ2 path), and the 549 172-block sweep found
   none. **RESOLVED 2026-08-13 (*Step G35*): such a configuration exists
   from `n_hub = 8` on** (outside this item's own `n_hub ≤ 6` sweep) —
   the dart-menu localization was exactly right; the missed case sits at
   the item's own edge, past where the sweep looked.
3. **`D > 0`** — unswept, unchanged (CFLANK item (iii)).
4. **`n_hub ≥ 8` at `Λ = ∅`, `|Λ| ≥ 2` at `n_hub = 6`** — compute, not
   mathematics, unchanged (CFLANK item (iv)); the `Λ ≠ ∅` side here
   reached `n ≤ 4` exhaustively plus the constructed `n = 6` item-(v)
   shapes.

---

### Verification (Steps G29–G33)

`notes/scripts/w4/gcap.py` (**new with this pass**, untracked; imports
`cflank.py` / `gridcol.py` / `grid.py` / `gridwit.py` / `closure.py` /
`kbare_common.py` read-only — `gridwit` is the canonical §1 home of
`subgraph_g` / `structured_beta` / `a_and_M`, the same import route
`packmm.py` uses). Exact ℚ throughout; rank enters only through
`gridcol.block_generic_zero` (GF(p) as a certified lower bound) with an
exact-ℚ recheck of every attaining draw through **both** the branch
system and the landed `grid.dim_Z` (README §4 convention 2). Rngs seeded
per mode, seeds printed; no `set` printed; nothing samples a placement,
so no figure is a rate over sampled placements and `repin.star_generic`
gates nothing (§(K-clos) (AC-9)).

Local devices, each named as such in its docstring: `two_ec_masks` /
`two_ec_subsets` (the (GR-27)(iii) enumeration), `tec_candidates` (the
exact colouring-independent pre-filter: a binding subset carries ≤ 2
branches of length ≥ 4), `branch_stats` / `g_formula` ((GR-28)(i)),
`contracted_view` / `gmax_exact_block` / `minimal_wits_general` (the
`Λ ≠ ∅` exact path), `witness_profile` (the classification datum),
`nc1_from_bd`, `probe_block`, `good_colouring`, `pool_specs`,
`item_v_shapes` (the 150-per-profile constructed item-(v) habitat).
Nothing existing is modified (`git status` shows only the new driver).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --probe    # ~345 s  the 45-shape reproduction (572/1144/16) + the 907-shape census probe (955 hits, 675 at Lambda = empty) + witness classification
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --law      #  136 s  (GR-27) xval 16 823 pairs; (GR-28): 549 172 blocks, g <= 1, a = 0; 35 minimal-witness profiles at k in {2,3}
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --cap      #  103 s  the target at 4920 + 884 + 972 shapes, no MISS; 68 seeded dim Z = 0 cross-checks
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --flip     #  137 s  repair distance <= 2 at 23 950/23 950 binding colourings; the odd-pair flip 178/178 at the constructed item-(v) shapes
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --adv      #    2 s  323 constructions, no flank; the F13 witness theta(2,4,4) + counter-fact + control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcap.py --validate # all five in one process -- OVER the 600 s foreground budget (~15 min): run the modes separately
```

`--validate` is the one **over-ceiling** invocation (dispatch-log F15
shape): all five modes together run to ~15 min in one process, well past
the 600 s foreground budget, while every individual mode above sits
inside it. `--probe` prints no self-timed elapsed figure (the other four
do); its ~345 s is the coordinator's own measured wall-clock for that
invocation.

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-27)(i)–(iii) | `--law` | `g_formula` asserted `==` the exact `subgraph_g` at 16 823 seeded (block, subset) pairs, 0 failures |
| the *Step G23* reproduction | `--probe` | asserted: 572 colourings, 16 hits, each `a = 0`, structured = exact max = 1, all `Λ ≠ ∅`, all minimal witnesses `k = 2` |
| the `Λ`-clause correction | `--probe` | the census hit census: 675 of 955 hits on `Λ = ∅` shapes, printed with the mechanism (the census's length-3 filter + lexicographic prefix) |
| probe soundness | `--probe` | every hit carries an explicit `g ≥ 1` witness re-checked through `subgraph_g` (a proof, not a sample); every clean block an exact-ℚ `dim Z = 0` point re-checked through `grid.dim_Z`; anomalies = 0 after 6-draw retry |
| (GR-28)(ii) `a = 0` | `--law` (+ `--probe` at every `Λ = ∅` hit) | `a_and_M` asserted `= 0` at 542 seeded blocks and at every formula-hit block |
| (GR-28)(iii)/(iv) the cap | `--law` | per block: exact `max g` computed; distribution printed; `assert max ≤ 1` over all 549 172 |
| the target statement | `--cap` | per shape over the three pools: first admissible colouring with `a = 0 ∧ max g ≤ 0` both blocks; `assert` no MISS; seeded `dim Z = 0` cross-checks |
| repair distance ≤ 2 | `--flip` | per binding colouring: 1-even / odd-pair / 2-even moves tried in order; `assert` 0 unrepaired |
| item (v) odd-pair | `--flip` | `n ≤ 4`: asserted 0 violated instances; constructed `n = 6`: 178/178 repaired, failures (none) would print by circuit profile |
| no flank in the control | `--adv` | 323 constructions: `assert adm > 0 and good > 0` per construction |
| the F13 witness | `--adv` | deterministic search re-run; `θ(2,4,4)` asserted out-of-habitat, NC1-satisfiable, 0 fully-good; counter-fact + negative control asserted |
| (GR-4′), (GR-10), (GR-15) as statements | — | **untouched and not driver-testable here**: no mode probes them |

**Determinism.** Every figure is identical under `PYTHONHASHSEED` 0 and
999; the only differing bytes across all five modes are their printed
wall-clock `[NNNs]` annotations — including `--adv`'s own (`[2s]` at seed
0 vs `[1s]` at seed 999), corrected here from the draft's overstated
claim of full byte-identity on `--adv` (the coordinator's own re-run
diffed the two outputs and found that one differing byte), the same
caveat `cflank.py`'s record carries.

**Scratch probes (README's standing rule).** Three throwaway spikes were
run during this pass (a wiring/timing spike, a witness-structure spike,
and a stratum-sweep spike) and are **not retained**; every figure any
claim above rests on is re-derived by a committed `gcap.py` mode — the
spikes' numbers (including a 28 696-pair hit count over non-minimal
subsets) are superseded by the modes' and are cited nowhere.

---

### Confidence verdict (Steps G29–G33)

| | claim | standing |
|---|---|---|
| **(GR-27)** | block additivity + exact computability of the (GR-8) maximum | **proven-informally** (proof above; 16 823-pair machine cross-validation) |
| **(GR-28)(i)** | the defect formula at `Λ = ∅` | **proven-informally** (same cross-validation) |
| **(GR-28)(ii)** | `a = 0` at every admissible colouring, `D = 0`, `Λ = ∅` | **proven-informally** (542-block corroboration) |
| **(GR-28)(iii)** | NC1 ⟹ every binding theta has `g = 1`, costs `(1,1,0)` | **proven-informally** |
| **(GR-28)(iv)** | NC1 ⟹ `max_P g(P) ≤ 1` at all `k` (`D = 0`, `Λ = ∅`) | **REFUTED at `k ≥ 3`, with an exact boundary** (Steps G34–G37, direction GUNIF, 2026-08-13): a **THEOREM at `n_hub ≤ 6`** ((GR-29)'s ledger, kills every tuple there), **FALSE from `n_hub = 8` on** ((GR-30)'s four witnesses, `g` up to 3) — the 549 172-block sweep was exhaustive over exactly the stratum that cannot exhibit the failure |
| *Step G30* | the probe reproduction and the `Λ`-clause correction | **proven** (exhaustive recomputation; the correction is a measured fact with its mechanism named) |
| the target | certificate 3's colouring-existence at `D = 0` | **proven per swept shape** (4920 + 884 + 972, each certificate exact); the **uniform** statement stays **OPEN** — this is the (GR-15) gap in its new, sharpest form |
| repair | distance ≤ 2 at `Λ = ∅`; odd-pair 178/178 at item (v) | **measured, and SWEEP-LOCAL** (no theorem claimed; per Step G36, "≤ 2" breaks at `n_hub = 16` — distance 3 at W5) |
| **(GR-15)** | | **OPEN — unchanged.** No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's and CFLANK's: everything above is about colourings of
fixed graphs and constructed σ-fixed configurations' ranks, never about
`PencilNondegFeasible G`; no σ-fixed witness is read as generic
(§(K-clos) (AC-9)).

### What would change this (Steps G29–G33)

**Items (i), (ii) and (iv) are ANSWERED — see *Steps G34–G37* (direction
GUNIF, 2026-08-13); the text below is kept as the record of what this pass
hoped for, not as a live lead.**

*(i)* **Closing (GR-28)(iv)'s `k ≥ 3` case** — a finite dart-menu
argument; would make the cap a theorem on the whole `Λ = ∅` `D = 0`
stratum at every `n_hub`, unswept sizes included. **ANSWERED
NEGATIVELY** (*Steps G34–G35*): the case analysis closed ((GR-29)) and
the cap is **REFUTED** at `k ≥ 3` — a theorem exactly at `n_hub ≤ 6`,
false from `n_hub = 8` on ((GR-30)). *(ii)* **A repair
theorem** — hypotheses under which the measured ≤-2-flip repair is
guaranteed (the (GR-24) analogue for the g-family; the binding-theta
characterization (iii) is its raw material). **ANSWERED: unprovable as
posed** (*Step G36*) — its premise dies with (i), and its measured
conclusion fails independently at `n_hub = 16` ((GR-31)). (i) + (ii) + (GR-23)/(GR-24)
would prove the certificate-3 target on the whole `Λ = ∅` `D = 0`
stratum, i.e. (GR-15) there **modulo (GR-4′)** — that composite route is
therefore **DEAD AS SPECIFIED**, while (GR-15) itself stays OPEN,
unchanged (per-shape it HOLDS at all four witnesses, (GR-31)).
*(iii)* **The `Λ ≠ ∅`
closed form** — the (GR-28) analogue with `Γ`-path merged classes
(the ear law is the natural vehicle); would extend (i)/(ii) to the full
`D = 0` stratum. *(iv)* **A `defect ≤ 1` configuration** at some
`k ≥ 3` — would break the cap and the repair calculus at one stroke;
none in 549 172 blocks. **ANSWERED: four of them exist** (*Step G35*,
(GR-30)), all outside this pass's `n_hub ≤ 6` sweep — the "none in
549 172 blocks" figure stands for the stratum it covers.
*(v)* **A `D = 0` shape with every admissible
colouring binding** — the g-flank; the detector for it now exists and is
adversarially tested (`--adv`), and the constructions say the budget is
too tight, but only per swept shape. *(vi)* **(GR-4′)** — any movement
there changes what certificate 3 buys; a habitat-block proof would make
every certificate above a rank statement outright.

---

### Step G34 — (GR-29): the dart menu and the budget ledger — the finite case analysis, machine-certified, with kills that are proofs

Answering *Step G33*'s items 1–2 and the GUNIF spec's two targets
(`notes/Pencil-fanout-archive.md` §"Eighth direction"): (a) close (GR-28)(iv)'s
`k ≥ 3` case, (b) a repair theorem. **The crux, restated from *Step
G31*.** At `defect(S) ≤ 1`, `k ≥ 3` forces a circuit of cost-0 core paths
inside the core; a 2-path circuit is dead (the `k = 2` argument), but a
`t ≥ 3` circuit's defect is its non-AA **corner** count, and corners
(degree-3-in-`S` hubs) contribute nothing to `defect_A(S)` — so NC1's own
`defect ≥ 3` requirement on the sub-circuit does not propagate into a
contradiction. This is a genuine degree of freedom, not a gap in the
argument: the dart-menu below finds where it is realized.

**The load-bearing colouring model** (verified against
`closure.alternation_classes`, the canonical generator). Colours
alternate along every branch, one free bit per branch. Hence at
`Λ = ∅` (all `ℓ ≥ 2`, and `ℓ ≤ 5` by (SD-6)):

| `ℓ` | `A(β)` | darts (the two end-edge colours) | cost `A(β) − 1` |
|---|---|---|---|
| 2 | 1 always | one A, one B, always | 0 |
| 3 | 2 or 1 (bit) | AA or BB | 1 or 0 |
| 4 | 2 always | one A, one B | 1 |
| 5 | 3 or 2 (bit) | AA or BB | 2 or 1 |

> **(GR-29)** *(proven; the menu machine-certified exhaustively over all
> paths of ≤ 5 branches, lengths 2–5, all bits, `--menu`; the ledger's
> case list machine-enumerated with every kill named, `--ledger`)* Let
> `S` be a connected 2-edge-connected branch subset of a `D = 0`,
> `Λ = ∅` class shape, `k = b − q + 1 ≥ 3`, with `defect_A(S) ≤ 1` at an
> admissible colouring, decomposed into its `3(k−1)` **core paths**
> between its `2(k−1)` **corners** (degree-3-in-`S` hubs).
>
> **(i) The cost-0 menu.** Every cost-0 core path is exactly one of
> - **[ℓ2]** a single length-2 branch, darts `(A, B)` — the only cost-0
>   path presenting an A-dart;
> - **[ℓ3]** a single length-3 branch at its B-majority bit, darts
>   `(B, B)`;
> - **[ℓ22]** two length-2 branches with an **AA interior hub**, darts
>   `(B, B)` outward — and the interior hub's third `G°`-dart is
>   **forced B** by the mono-hub ban.
>
> No cost-0 path has ≥ 3 branches; path costs are never negative.
>
> **(ii) The cost-1 menu** is finite: 15 canonical types, each of ≤ 4
> branches (an ℓ2 middle branch must be adjacent to the unique non-AA
> interior) and excess ≤ 3, enumerated with their dart/parity/balance
> attributes by `--menu` — including the three types the refutation
> lives on: the single **ℓ3 A-majority** (darts `(A, A)`, the only
> 1-branch path presenting two A-darts), the **(2,2) path with a non-AA
> interior** (whose interior's third dart is **free**, not B-forced),
> and **(2,3A,2)** (an A-majority ℓ3 carried inside a both-ends-B
> path).
>
> **(iii) Corners eat A-darts.** Every corner needs at least one A-dart
> (mono-hub ban) and at most two; only [ℓ2] heads and A-ended cost-1
> paths supply them. With `x = #[ℓ2]`, `a = #AAB` corners, `h` the
> cost-1 path's A-ends: `x = 2(k−1) + a − h`.
>
> **(iv) The core is simple at defect 0.** A 2-circuit of two cost-0
> paths has `defect_A ≤ 2 < 3` at every dart orientation — an NC1
> violation outright (`--menu` enumerates all pairs).
>
> **(v) The ledger.** Write `W_S` for the hub set of `S`, `z = #[ℓ22]`,
> `w3 = #[ℓ3]`; free darts of `W_S` exist only at path interiors
> (`F = z + n_int(P*)`); a **chord** (a `G°`-branch joining two AA
> interiors) is B-forced at both ends, hence **odd** (alternation) with
> excess ∈ {1, 3} ((SD-6)) and **B-majority**; a chord may be even only
> at the ≤ 1 free interior. The following are all necessary, so each
> kill below is a proof:
> 1. **(K-bal)** every forced-B-majority odd branch ([ℓ3]s, AA-chords,
>    B-odd cost-1 parts) needs a distinct A-majority odd partner in
>    `G°`, each costing ≥ 1 excess; inside `S` at most one A-majority
>    odd exists (inside the cost-1 path).
> 2. **(K-cut)** (GR-25) at `W_S`: `∂ = 0` proper and `∂ = 1` are dead
>    (`exc ≤ 6 < 7`; both bridge sides need ≥ 5 excess vs a budget of
>    6); proper `W_S` needs `2∂ + exc(E(W_S)) ≥ 7`, and the complement
>    the same with the shared budget `Σ exc = 6` (GR-21).
> 3. **(K-cut-inner)** (GR-25) applied **inside** `S`, at
>    corners ∪ [ℓ22]-interiors — i.e. with a multi-branch cost-1 path's
>    interiors dropped (removing one edge of the 2-edge-connected core
>    keeps it connected, so this `W′` is always legal and proper). *This
>    clause was found the honest way: the first ledger draft's would-be
>    `n_hub = 8` candidate (`P* = (2,3A,2)`, K4 core) FAILED the habitat
>    gate on exactly this cut; it is kept as a control in `--wit`.*
> 4. **(K-improper)** if `W_S` spans all hubs, all 6 units of excess
>    live on `E(W_S)`, but (K-bal) + (SD-6) cap it at ≤ 4 — **the
>    improper case is dead at every `k`.**
> 5. **(K-mono/K-bal at a singleton outside)** a single outside hub
>    receives 3 boundary branches whose W_S-side darts are B-forced
>    except at ≤ 1 free interior; a finite dart/parity enumeration
>    (`--ledger`'s `singleton_outside_lives`) decides each such tuple.
>
> **Corollary (the theorem half — the exact-boundary upgrade of
> (GR-28)(iv)).** Enumerating every parameter tuple
> `(k ≤ 6, defect, P*-type, a, w3, z, chords, dispositions)` — `k ≥ 7`
> forces `n_hub ≥ 13` — **every tuple with `n_hub ≤ 6` is killed by a
> named clause** (histogram printed by `--ledger`: 1385 improper-excess,
> 1244 bridge, 486 budget, 341 + 288 cut, 310 improper-balance, 33
> inner-cut, 18 balance-pool, 3 singleton-enumeration). Hence **NC1 ⟹
> `max_P g(P) ≤ 1` is a THEOREM on the whole `n_hub ≤ 6` stratum** — the
> 549 172-block sweep was exhaustive over exactly the stratum where the
> cap is provable. The first surviving tuples sit at `n_hub = 8`, all in
> the `k = 3` singleton-outside family.

*Proof notes.* (i)+(ii) are the alternation table plus a finite
enumeration (`--menu` runs it to 5-branch paths and finds nothing past
4). The A-dart scarcity (iii) is the mono-hub ban read through the menu:
[ℓ3]/[ℓ22]/chords present only B. (iv) is (GR-28)(i) on the 2-circuit:
`defect = cost + cost + (≤ 2 corner indicators) ≤ 2`. (v)-1: an odd
branch is A- or B-majority by its bit; every structurally-forced one
above is forced to B, and balance is a zero-sum. (v)-3: dropping the
`P*` interiors changes `∂` by `2 − n_int(P*)` per the end-darts and
removes `exc(P*)`, which is strictly tightening for `n_int ≥ 2`. (v)-4:
with everything internal, the only A-majority-odd candidates are inside
the cost-1 path (≤ 1 of them, always with excess 1), so
`w3 + #chords ≤ 1` and `exc(E(W_S)) ≤ 1 + 3 = 4 < 6`. ∎

---

### Step G35 — (GR-30): the refutation. Four explicit habitat witnesses, `k = 3, 3, 4, 5`, `g` up to 3, minimal at `n_hub = 8`

> **(GR-30)** *(proven by explicit construction through the canonical
> gates, `--wit`; every gate asserted)* (GR-28)(iv) is **FALSE**, with
> the exact boundary of (GR-29)'s corollary:
>
> | witness | `n_hub` | `k` | `defect_A(S)` | exact `g(S)` | generic `dim Z` | binding circuits | NC1 |
> |---|---|---|---|---|---|---|---|
> | **W3M** (minimal) | **8** | 3 | 1 | **2** | 2 | **0 — NC1 vacuous** | passes |
> | W3 | 10 | 3 | 1 | 2 | 2 | 0 — NC1 vacuous | passes |
> | W4 | 12 | 4 | 1 | 2 | 2 | 2 | passes |
> | W5 | 16 | 5 | 0 | **3** | 3 | 1 | passes |
>
> Each is a tight (`5|E| = 6(|V|−1)`), `def = 0`, `hnoRigid`, girth-7,
> `Λ = ∅`, `D = 0` class shape (the proven (GR-25) cut criterion over
> all `2^{n}` subsets, cross-validated against `gridcol.class_shape`),
> with an explicitly constructed admissible colouring (balanced, both
> classes forests, no mono hub) passing NC1 at every binding circuit, at
> which the named branch subset `S` has the stated **exact**
> `subgraph_g` (cross-checked against the (GR-28)(i) formula), no
> `dim Z = 0` draw exists in 6 attempts, and 3 exact rational seeded
> draws give `dim Z = g` through **both** matrices (`dim_W_branch` and
> the landed `grid.dim_Z`) — so generic `dim Z = g(S)` exactly. `g = 3`
> at W5 is the largest value `g` takes on any connected subset checked:
> at `k ≥ 5` the cap fails maximally.

**The minimal witness W3M (`n_hub = 8`, 26 vertices), in full.** Core
K4 on `v1..v4`: `P* = v1v2` a **single ℓ3 A-majority** (both darts A —
it feeds both its own corners and carries the A-majority balance
partner *inside* `S`); [ℓ2] heads at `v3` (from `v1v3`) and `v4` (from
`v2v4`); [ℓ22]s on `v1v4`, `v2v3`, `v3v4` (interiors `m14, m23, m34`,
all AA, third darts B-forced). All three boundary branches run to a
**single outside hub `o`**, lengths `(5, 4, 2)`: the ℓ5 is B-majority
(both ends B, balancing `P*`), the even ones arrive at `o` as A — darts
at `o` are `(B, A, A)`. Excess `1 + 3 + 2 = 6` exactly. The shape has
**no binding circuit whatsoever** (every circuit has
`Σ_β(ℓ_β − 1) ≥ 5`), so NC1 is vacuous — the cap fails with room to
spare. `S` = the 9 core branches: `k = 3`,
`defect_A(S) = (A(P*) − 1) = 1`, `g = 2`.

W3 (`n = 10`) replaces `P*` by a `(2,2)` cost-1 path whose non-AA
interior has a **free** third dart (played A inward so the boundary
arrives B at the outside — the trick that defuses the mono-hub crash at
small outsides), with a 3-hub outside triangle `(5,4,2)`. W4 (`n = 12`)
is a prism core at `k = 4` with two binding circuits that NC1 passes at
exactly `runs = 3` each. W5 (`n = 16`, defect 0) is the structural
heart: an all-[ℓ2] 8-cycle of corners, cyclically A-oriented, plus an
[ℓ22] perfect matching through four AA interiors — `S` has **zero
excess and zero defect**, `g = 3` — with an ℓ5 B-majority chord between
two interiors, two boundary ℓ2s, and a `K4 − e` outside carrying the
(GR-25)-forced excess-3 and the ℓ3 A-majority balance partner. The
construction visibly scales with `k` (a `2(k−1)`-cycle plus matching);
only `k ≤ 5` is machine-realized, and nothing below rests on larger
`k`.

**Why 549 172 blocks and the 907-shape census never saw it.** *Step
G28* item 3 (CFLANK item (iv)) had already recorded that the sweep
"stops at `n_hub = 6` because `gridcol.multigraphs` is exponential in
the pair count" — the ledger's corollary explains *why* that boundary
is not just a compute limit but the exact edge of where the cap holds:
no counter-configuration fits at `n_hub ≤ 6`. The evidence for (iv) was
exhaustive over exactly the maximal stratum on which the cap is a
theorem — the same epistemic shape as *Step G30*'s `Λ`-clause
correction (a generator-boundary artifact read as a law), one level up,
and this time caught by a proof direction rather than a wider sweep.

**Two controls (`--wit`, both asserted).** The (SD-6) control: W5 with
its chord lengthened to 7 is REJECTED by the habitat gate. The
(K-cut-inner) control: the first ledger draft's would-be `n = 8`
candidate (`P* = (2,3A,2)`, which needs `n_int = 2` interiors) is
REJECTED — the inner cut at corners + [ℓ22]-interiors has
`2∂ + exc = 6 < 7`.

---

### Step G36 — (GR-31): what survives. Per-shape (GR-15) at every witness; the repair distance grows with `g`; both halves of the old route die as posed

> **(GR-31)** *(measured with rank-grade certificates, `--repair`)*
> At every witness shape:
>
> **(i) Per-shape (GR-15) HOLDS.** A fully-good admissible colouring —
> certified by an exact rational `dim Z = 0` point in **both** blocks
> through **both** matrices, which by (GR-8)'s proven `≥` direction is a
> proof of `a = 0 ∧ max_P g(P) ≤ 0` with no subset scan — exists at
> random draw 52 / 97 / 329 / 188 (seeded). **The refutation kills the
> route to uniform (GR-15), not (GR-15).**
>
> **(ii) The flip distance from the witness colouring to a
> rank-certified fully-good one** is 2 at W3M, W3, W4 (`g = 2`) and
> **3 at W5** (`g = 3`) — so *Step G32*'s measured "≤ 2 balance-
> preserving flips" law is **also false beyond the sweep**, failing at
> the first `g = 3` block. (Measured distance equals `g` at all four
> witnesses; a suggestive pattern, not a claim.)

**Both targets of the GUNIF spec, adjudicated.** Target (a) is closed:
(GR-28)(iv) is refuted, with the exact boundary `n_hub ≤ 6` as the
salvage theorem. Target (b) — the (GR-24)-analogue repair theorem — is
**unprovable as posed**: its premise (the cap, hence the binding-theta
`(1,1,0)` witness structure of (GR-28)(iii) as the only binding mode)
is false from `n = 8` on, and its intended conclusion (distance ≤ 2) is
false at W5. What survives for a successor: repair distance was never
observed to exceed `g`, and every witness shape keeps an abundant
supply of fully-good colourings.

**The true mechanism behind binding at `g ≥ 2`** (correcting *Step
G33* item 1's mechanism in place, since that item claimed defect units
are "bought with excess" — wrong as stated: W5's binding subset has
zero excess and zero defect; cost-0 paths are excess-free). What
binding at `g ≥ 2` actually costs is *structure* — AA interiors with
B-forced exits, a (GR-25)-shaped boundary, and a balance partner — not
excess inside `S`. Any future uniform-existence argument must charge
*that*, e.g. by the exact-alignment observation: a defect-≤1
configuration pins every [ℓ2] head and every interior dart, so binding
colourings occupy an exponentially thin slice of the admissible cube
(measured, not proven: at every witness a fully-good colouring appears
within a few hundred random draws).

---

### Step G37 — where this leaves the (GR-15) line (hand-off)

- **(GR-15) itself: OPEN, unchanged in both directions.** Every swept
  or constructed shape — including all four witnesses — has a per-shape
  proof. No flank; no gap-map *status* moves; (GR-4′)/(GR-10)
  untouched.
- **The certificate-3 route to uniform (GR-15) at `Λ = ∅` `D = 0` (cap
  + repair theorem, *Steps G32–G33*) is DEAD as posed** — both
  ingredients refuted above. Surviving route material: (GR-27)'s exact
  computability (untouched), the (GR-29) ledger (a new, proven
  structural tool: it says exactly where and how binding-at-`g ≥ 2`
  configurations live), the distance-≤-`g` repair observation, and the
  exact-alignment thinness observation.
- **The `g ≤ 1` cap survives as a theorem exactly on `n_hub ≤ 6`**
  ((GR-29) corollary) — which is what the repair calculus of
  (GR-22)–(GR-24) actually consumes on the swept pools, so nothing
  landed in Steps G24–G33 is invalidated on its own stratum; only the
  extrapolation dies.
- The (K-res)/(GR-15) quantification question stays a coordinator
  hand-off note, untouched here (spec caution).
- **The line's positive-termination path is DEAD AS SPECIFIED**: "cap
  + `Λ ≠ ∅` flip + `D > 0` lift + (GR-4′) = (GR-15) proven" named the
  cap as its first ingredient, and the cap is false in general. This is
  a refutation of the *named route*, not a failure of the TERMINATION
  test itself (a cap **was** proven and new mechanisms **were** named —
  the test's literal trigger does not fire) — see `notes/Phase39.md`
  *Hand-off* for the coordinator's resulting phase-shape escalation.

---

### Verification (Steps G34–G37)

`notes/scripts/w4/gunif.py` (**new with this pass**, untracked; imports
`gcap.py` — the tracked GCAP driver, whose `branch_stats` / `g_formula`
/ `subset_eidx` are reused rather than rebuilt — plus `cflank.py` /
`gridcol.py` / `grid.py` / `gridwit.py` / `closure.py` read-only). Exact
throughout (integers; rank only through
`gridcol.block_generic_zero`'s GF(p) lower bound, with every attaining
draw re-checked in exact ℚ through **both** the branch system and the
landed `grid.dim_Z` — README §4 convention 2). Rngs seeded per mode,
seeds printed; no `set` printed; nothing samples a placement, so
`repin.star_generic` gates nothing (§(K-clos) (AC-9)).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --menu     #  <1 s  the (GR-29) menu: cost-0 EXACTLY {[l2],[l3],[l22]}; cost-1 = 15 types, <= 4 branches; the 2-circuit kill
PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --ledger   #  <1 s  every n_hub <= 6 tuple killed by a named clause (histogram); first survivors at n = 8, k = 3 singleton family
PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --wit      #  ~1 s  the four witnesses through the canonical gates + the (SD-6) and (K-cut-inner) controls
PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --repair   #  ~1 s  per-shape (GR-15) at every witness; flip distances 2/2/2/3
PYTHONHASHSEED=0 python3 notes/scripts/w4/gunif.py --validate #  ~2 s  all four in one process (inside the 600 s budget; no F15 shape needed)
```

**Which driver mode tests which sentence (F11 — doubly binding here,
since the direction's claims are exhaustiveness claims).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-29)(i) cost-0 menu complete | `--menu` | exhaustive enumeration over all ≤ 5-branch paths, lengths 2–5, all bits; asserted equal to the 3-element canonical set |
| (GR-29)(ii) cost-1 menu, ≤ 4 branches, exc ≤ 3 | `--menu` | same enumeration; the 15 canonical types printed with dart/parity/balance attributes; asserted bounds |
| (GR-29)(iv) 2-circuit kill | `--menu` | all cost-0 pairs × dart orientations: `defect_A ≤ 2` asserted |
| (GR-29) corollary: no counter-tuple at `n_hub ≤ 6` | `--ledger` | full parameter enumeration (`k ≤ 6` suffices, printed); `assert` no survivor at `n ≤ 6`; kill histogram printed |
| the singleton-outside case | `--ledger` | the finite dart/parity enumeration (`singleton_outside_lives`), the one non-arithmetic clause |
| first survivors at `n = 8`, `k = 3` | `--ledger` | `assert nmin == 8` and all `n ≤ 8` survivors in the `('singleton', 3)` family |
| (GR-30) each witness is habitat | `--wit` | `cubic_habitat` (the proven (GR-25) criterion, `2^n` subsets) + tightness `5\|E\| = 6(\|V\|−1)` asserted per witness |
| (GR-30) each witness colouring admissible + NC1-passing | `--wit` | `cflank.admissible` and `cflank.nc1_violations == []` asserted (binding-circuit counts printed; W3M/W3 have zero) |
| (GR-30) exact `g(S)` = 2/2/2/3 | `--wit` | exact `gridwit.subgraph_g` asserted equal to the (GR-28)(i) formula and to the expected value |
| (GR-30) generic `dim Z = g` | `--wit` | no `dim Z = 0` draw in 6; three exact ℚ draws asserted equal through both matrices |
| the (SD-6) and (K-cut-inner) controls | `--wit` | the ℓ7-chord variant and the `(2,3A,2)` `n = 8` candidate asserted REJECTED by the habitat gate |
| (GR-31)(i) per-shape (GR-15) at the witnesses | `--repair` | seeded random search; fully-good = exact ℚ `dim Z = 0` point in both blocks through both matrices, asserted |
| (GR-31)(ii) flip distances 2/2/2/3 | `--repair` | balance-preserving moves in increasing size (evens + odd pairs); first rank-certified success reported |
| (GR-15), (GR-4′), (GR-10) as statements | — | **untouched and not driver-testable here**: no mode probes them |

**Determinism.** `--validate`'s combined output (which runs `--menu`,
`--ledger`, `--wit` and `--repair` in one process) diffs byte-identical
across `PYTHONHASHSEED` 0 and 999, and `--wit` was independently
rechecked standalone at both seeds with the same result — at these
runtimes even the wall-clock `[Ns]` annotations printed identically
(the usual inherently-nondeterministic caveat, per the `cflank`/`gcap`
precedent, simply did not bite here).

**Scratch probes (README's standing rule).** Three throwaway debug
spikes were run and are **not retained**: a violating-cut finder (its
finding became the (K-cut-inner) clause and the `--wit` control), a
ledger-survivor dump (superseded by `--ledger`'s survivor printout),
and a standalone first-pass of the `n = 8` witness (superseded by W3M
in `--wit`). Every figure above is re-derived by a committed driver
mode.

---

### Confidence verdict (Steps G34–G37)

| | claim | standing |
|---|---|---|
| **(GR-29)** | the cost-0/cost-1 menu, the ledger clauses, and the case-list enumeration | **proven-informally** (proofs above; menu and case list machine-certified exhaustively, `--menu`/`--ledger`) |
| **(GR-29) corollary** | NC1 ⟹ `max_P g(P) ≤ 1` is a **theorem at `n_hub ≤ 6`** (`Λ = ∅`, `D = 0`) | **proven-informally** (every counter-tuple killed by a named necessary clause) |
| **(GR-30)** | **(GR-28)(iv) REFUTED**: witnesses at `n_hub = 8, 10, 12, 16` (`k = 3, 3, 4, 5`, `g = 2, 2, 2, 3`); `n_hub = 8` minimal | **proven** (explicit constructions; every gate canonical and asserted; the boundary exact by (GR-29) + W3M) |
| **(GR-31)(i)** | per-shape (GR-15) at all four witness shapes | **proven per shape** (exact ℚ `dim Z = 0` points, both blocks, both matrices) |
| **(GR-31)(ii)** | repair distance 2/2/2/3; *Step G32*'s ≤ 2 law false beyond the sweep; distance ≤ `g` | **measured** (rank-certified endpoints; the `≤ g` pattern is an observation, not a claim) |
| target (b) | the (GR-24)-analogue repair theorem | **unprovable as posed** (premise refuted by (GR-30); conclusion refuted at W5) |
| **(GR-15)** | | **OPEN — unchanged in both directions.** Not closed, not refuted; the certificate-3 uniformity *route* is dead as posed; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's, CFLANK's and GCAP's: everything above is about
colourings of fixed graphs and constructed configurations' exact ranks,
never about `PencilNondegFeasible G`; no σ-fixed witness is read as
generic (§(K-clos) (AC-9)).

### What would change this (Steps G34–G37)

*(i)* **A `Λ ≠ ∅` or `D > 0` analogue of the ledger and witnesses** —
both strata stay unswept; the witness mechanism (AA interiors + a
balance partner) has no obvious dependence on either restriction, so
the refutation plausibly extends, but nothing here shows it. *(ii)*
**A repair theorem in the post-refutation form** — e.g. "distance ≤ g",
or a proof that fully-good colourings always exist via the
exact-alignment thinness of binding colourings; either would re-open a
route to uniform (GR-15) at `Λ = ∅` `D = 0` **modulo (GR-4′)**. *(iii)*
**A `D = 0` shape whose every admissible colouring is binding** — the
g-flank, now with a sharper hunting ground: the ledger says exactly
what structure it must contain; none is known, and every witness shape
here fails to be one (abundant good colourings). *(iv)* **(GR-4′)** —
unchanged: any movement there changes what a fully-good colouring
buys. *(v)* **A realization at `k ≥ 6`** of the scaling family — would close
the cosmetic gap between "witnesses at `k ≤ 5`" and "false at every
`k ≥ 3`": the refutation as stated is per-`k` at `k ∈ {3, 4, 5}` plus
the exact `n_hub` boundary; the `2(k−1)`-cycle + matching pattern is
expected to realize every larger `k` but is machine-checked only to
`k = 5`.

### Steps G38–G42 (2026-08-13, direction GEXIST) — the target is reduced to a **minority-dart orientation problem** with one unit of structural slack at every proper chunk: a **capacity theorem** makes the whole graph exactly critical and every proper chunk strictly slack, a **weakness lemma** makes binding an alignment of ≥ 2 scarce per-hub weaknesses, the **first-moment/union-bound route is REFUTED by a constructed witness**, an **uncrossing lemma** (defect is submodular) organizes the binding family, and a correlated **rung-minority rule** closes the whole ladder family by explicit rank-certified colourings — but the uniform existence statement, and with it (GR-15), stays **OPEN**

Answering `notes/Pencil-fanout-archive.md` §"Ninth direction — GEXIST": the
uniform fully-good existence target at `Λ = ∅`, `D = 0` — *every tight
class shape there admits an admissible colouring with
`a = 0 ∧ max_P g(P) ≤ 0` in both blocks* — attacked through the (GR-29)
ledger, in the (existence direct) mechanism form, with the (repair form)
advanced as a by-product.  Read against *Steps G19–G23*
((GR-16)/(GR-17)), *Steps G24–G28* ((GR-21)–(GR-26)), *Steps G29–G33*
((GR-27)/(GR-28)), *Steps G34–G37* ((GR-29)–(GR-31)), §(K-clos)
(AC-4)/(AC-7)/(AC-9), and the *Shared dictionary*'s (R3)/(R4)/(SD-6).

**Step 0 pin (mandatory, discharged before any derivation).**
**(GR-29)**: the cost-0 menu is exactly `{[ℓ2], [ℓ3], [ℓ22]}`, the
cost-1 menu is 15 canonical types of ≤ 4 branches, the ledger clauses
are (K-bal)/(K-cut)/(K-cut-inner)/(K-improper)/the singleton-outside
enumeration, and the corollary's boundary is exact — NC1 ⟹
`max_P g(P) ≤ 1` is a theorem at `n_hub ≤ 6`, first survivors at
`n = 8`, `k = 3`, singleton-outside family.  **(GR-30)**: W3M/W3/W4/W5
as constructions, with W5 the structural heart (all-[ℓ2] corner cycle +
[ℓ22] matching, binding with zero excess and zero defect inside `S`).
***Step G36*'s corrected mechanism**: binding at `g ≥ 2` costs
**structure**, not excess; the exact-alignment observation is measured,
not proven.  **(GR-4′)'s proven-case boundary** (≤ 3 classes total or
all-singleton classes) covers no habitat block, so the (GR-4′) rider
below is genuinely load-bearing and never dissolves silently.  W5 is
priced FIRST below (*Step G40*, *Step G41*): its binding subset is the
capacity-tight case of (GR-32) and the constant-probability witness of
(GR-34).

**The closure chain, with both riders, stated before anything is
claimed.**  The target implies (GR-15) at `Λ = ∅` `D = 0` **modulo
(GR-4′)** (certificate 3 of (GR-20)); (GR-15) there + (GR-1)/§(K-clos)
(AC-4) + (GR-5) + (AC-7) would discharge `hK` on the tight `D = 0`
stratum over every infinite characteristic-0 field; the **`Λ ≠ ∅`
closed-form analogue stays unswept** and the **`D > 0` lift stays
unswept**.  Nothing here closes (GR-15), and nothing below claims to.

**Headline, stated before the mathematics.**

- **(GR-32), the capacity theorem (proven).**  For every chunk (=
  connected 2-edge-connected branch subset) `S`,
  `defect_A(S) + defect_B(S) = 2z(S) + exc(S) − z_mono(S)`, and the
  habitat forces the **capacity** `cap(S) := 2z(S) + exc(S)` to be
  **≥ 7 at every chunk except the whole graph**, where it is exactly 6
  and balance makes `defect_A = defect_B = 3` **identically**.  So the
  whole graph is exactly critical, every proper chunk carries one unit
  of slack, and a *pointwise* g-flank mechanism (a chunk binding at
  every colouring because its capacity is under 6) is **impossible in
  habitat** — `θ(2,4,4)`, GCAP's F13 witness, has `cap = 4`, which is
  exactly *why* it is one out of habitat.  Machine-certified at all
  **220 038 chunks of all 4920 pool shapes**.
- **(GR-33), the weakness lemma (proven).**  At an admissible colouring
  every hub has a 2-1 dart pattern: a majority colour, a unique
  **minority dart**.  `defect_A(S) = N(S) − save_A(S)` with
  `N = z + w₃ + w₄ + 2w₅ ≥ 4` at every proper chunk, and `save_A`
  counts the **weak-A interiors** (exit dart = minority dart, majority
  A) plus the B-majority odd branches of `S`.  Binding in A ⟺
  `save_A ≥ N − 2 ≥ 2`: every binding chunk is an **alignment of at
  least two weaknesses**, and each hub can spoil, per block, only the
  chunks that exit at its one minority dart.  All-even sub-case: the
  colouring **is an orientation** of the hub multigraph with in-degrees
  in {1, 2}, and the target becomes a pure orientation problem.
- **(GR-34), the route adjudication.**  The **first-moment/union-bound
  route is REFUTED by a constructed witness**: on the circular ladder
  `CL10` (habitat, the CFLANK `--tight` recipe) the interval-chunk
  family alone has measured `E[#binding] = 3.23 > 1` (growing 0.20 →
  1.55 → 3.23 along CL6/CL8/CL10), and the binding probability of a
  fixed chunk is a **constant in its size** (W5's 16-branch subset is
  binding at 43/200 seeded admissible colourings — two aligned
  interiors out of four suffice), so no per-event-decay (LLL-shaped)
  scheme closes either.  This is the spec's named union-bound risk,
  **confirmed fatal** for the uncorrelated version of mechanism form 1.
  What survives is the **correlated route**: the **rung-minority rule**
  (every hub's minority dart on its rung — a branch no interval or
  square chunk ever exits through) produces an explicit colouring at
  CL6/CL8/CL10 that is admissible, has `save ≡ 0` on the whole interval
  family, and is **rank-certified fully good** (exact rational
  `dim Z = 0`, both blocks, both matrices — a per-shape proof).
- **(GR-35), the uncrossing lemma (proven).**  The defect formula is
  **submodular**: `defect_A(S) + defect_A(S′) ≥ defect_A(S ∪ S′) +
  defect_A(S ∩ S′)` for any two branch sets with all degrees in {2, 3}
  — the intersection needs no structure.  Crossing binding chunks
  therefore either **merge into a binding union** or **intersect in a
  defect-≤ 1 set** — exactly the object the (GR-29) ledger classifies
  (absent at `n_hub ≤ 6` under NC1).  Asserted at 1526 hub-sharing
  chunk pairs.  The **weakness-guided repair** realizes every recorded
  distance: 2/2/2/3 at the four GUNIF witnesses using only flips at
  weak interiors of the named subset, and *Step G32*'s ≤ 2 law at
  120/120 sampled pool binding colourings with the same guided set.
- **The named sticking configuration** (the honest-MISS deliverable): a
  hub **all three of whose darts are exits of capacity-tight chunks** —
  the Hall-type obstruction to choosing minority darts.  The hot-dart
  census finds **none** on the swept stratum (199 pool shapes: 2 hubs
  with two hot darts, 0 with three), so the minority-orientation CSP is
  loose exactly where everything is proven, and the configuration must
  be hunted at `n_hub ≥ 8` — the pruned target for the conditional
  tenth-direction enumerator.
- **What does NOT move.**  The target stays **OPEN** in its uniform
  form — proven per shape everywhere swept or constructed (nothing
  new: (GR-26)(iii)/(GR-31)(i) already said so), refuted nowhere, **no
  g-flank found**.  (GR-15) stays OPEN, unchanged in both directions;
  (GR-4′)/(GR-10) untouched; **no gap-map status moves**.

**Notation (on top of *Steps G19–G37*).**  `Λ = ∅`, `D = 0` throughout:
`G°` cubic, lengths `ℓ_β ∈ [2, 5]` ((SD-6)), `Σ_β(ℓ_β − 2) = 6`
((GR-21)).  A **chunk** is a connected 2-edge-connected branch subset
`S`; `W_S` its hub set; `z(S)` = #degree-2-in-`S` hubs (its
**interiors** — chunk-relative, unlike *Step G34*'s path-interiors);
`w₃/w₄/w₅` its length-3/4/5 branch counts, `exc(S) = w₃ + 2w₄ + 3w₅`;
`N(S) := z + w₃ + w₄ + 2w₅`.  A degree-2-in-`S` hub's **S-pair** is its
two `S`-darts; `z_mono(S)` = # monochromatic S-pairs.  An **exit** is
an interior's third dart leaving `W_S`; a **chord** is a branch off `S`
joining two interiors.  Binding in A ⟺ `defect_A(S) ≤ 2` ((GR-28)(i):
`g = 3 − defect ≥ 1`); **fully good** = no binding chunk in either
block, which by (GR-27) block-additivity and (GR-28)(ii) (`a = 0` free)
is exactly the target's `a = 0 ∧ max_P g(P) ≤ 0` in both blocks.
Everything dualizes with `A ↔ B`.

---

### Step G38 — (GR-32): the capacity theorem — the whole graph is exactly critical, every proper chunk has one unit of slack, and the pointwise flank mechanism is impossible

> **(GR-32)** *(proven; the trichotomy machine-certified at 220 038
> chunks of all 4920 pool shapes, the identity chain at 72 120
> (colouring, chunk) pairs, `--exh`)*  Let `G` be a habitat shape and
> `S` a chunk.
>
> **(i) The pair identity.**  At every admissible colouring,
> > `defect_A(S) + defect_B(S) = 2z(S) + exc(S) − z_mono(S)`.
>
> **(ii) The capacity trichotomy.**  With `cap(S) := 2z(S) + exc(S)`:
> - `W_S` proper ⟹ `cap(S) ≥ 7`;
> - `W_S` improper (spanning): `z` is even; `z = 0` forces
>   `S = E(G°)` with `cap = 6`; `z = 2` forces `cap ≥ 7`; `z ≥ 4`
>   gives `cap ≥ 8`.
>
> **(iii) Whole-graph criticality.**  At every *balanced* colouring,
> `defect_A(E(G°)) = defect_B(E(G°)) = 3` **identically** — the whole
> graph is never binding and never slack (`g(E(G°)) = 0` is tightness
> restated).
>
> **(iv) The anti-flank floor.**  A chunk with `cap(S) ≤ 5` is binding
> in some block at **every** colouring (by (i), since `z_mono ≥ 0`);
> hence in habitat the *pointwise* flank mechanism is impossible, and
> a g-flank — if one exists — must be a **covering** phenomenon
> (different chunks binding at different colourings), never a single
> chunk's arithmetic.
>
> **(v) `N ≥ 4`.**  `2N(S) = cap(S) + w_odd(S)`, so every chunk except
> `E(G°)` has `N ≥ 4`; at `E(G°)`, `N = 3 + w_odd/2 ≥ 3`.

*Proof.*  (i): per branch, `(A(β) − 1) + (B(β) − 1) = ℓ_β − 2`; per
interior, `[pair not AA] + [pair not BB] = 2 − [pair mono]`; sum.
(ii): each interior has exactly one free dart, so exits and chords
account for all of them and `∂(W_S) = z − 2·ch`; `E(W_S) = S ⊔ chords`
(a degree-3-in-`S` hub has no free dart), so proper `W_S` gives, by the
proven cut criterion (GR-25),
`7 ≤ 2∂(W_S) + exc(E(W_S)) = 2z − 4ch + exc(S) + exc(chords)`, i.e.
`cap(S) ≥ 7 + Σ_{chords}(4 − exc) ≥ 7 + ch` since `exc(chord) ≤ 3` by
(SD-6).  (`W_S` qualifies for (GR-25): it induces a connected subgraph
⊇ `S` and `|W_S| ≥ 2` because loops do not exist in habitat.)  If
`z = 0` and `W_S` were proper, `∂(W_S) = 0` would disconnect `G°`; so
`z = 0` forces improper, and then every branch of `G°` is in `S`
(a missing branch would put free darts at its ends), i.e.
`S = E(G°)`, `cap = exc(E(G°)) = 6` by (GR-21).  Improper with `z > 0`:
free darts pair up into chords (`z = 2ch`, even); at `z = 2` the single
chord carries `≤ 3` excess, leaving `exc(S) = 6 − exc(chord) ≥ 3`, so
`cap ≥ 4 + 3 = 7`; at `z ≥ 4`, `cap ≥ 2z ≥ 8`.  (iii): `z(E(G°)) = 0`,
so `defect_A(E(G°)) = Σ_β(A(β) − 1) = |E_A| − M = 3c − M`; at `D = 0`,
`M = 3n/2` and `c = n/2 + 1`, so `3c − M = 3`.  (iv) and (v) are
arithmetic on (i)–(ii).  ∎

**Why this is the load-bearing step.**  *Step G36* said binding at
`g ≥ 2` costs structure, not excess, and left "charge that" as the
successor's task.  (GR-32) is the charge, run at the `g ≥ 1` threshold
the *target* needs: the structural quantity a chunk must expose —
interiors at 2 units each, excess at face value — is bounded **below**
by the cut criterion at exactly `7 = 6 + 1`: one unit above the
threshold `6` under which no colouring can save both blocks.  The
capacity-tight chunks (`cap = 7`; 4344 on the pool, all three GUNIF
witness subsets — `cap(S_{W3M}) = 7` exactly, `cap(S_{W5}) = 8` with
its cut value `2∂ + exc(E(W_S)) = 7` exactly) are the whole hunt: they
are where a colouring is one aligned weakness away from binding.
`θ(2,4,4)` (`cap = 4 < 6`) is the (GR-32) reading of GCAP's F13
witness: out of habitat the floor fails and binding is unavoidable —
the g-detector's miss there is now a two-line corollary rather than a
computation.

---

### Step G39 — (GR-33): the weakness lemma — binding is an alignment of scarce per-hub weaknesses, and the all-even case is an orientation problem

> **(GR-33)** *(proven; the 2-1 pattern lemma certified exhaustively
> over all 6 non-mono patterns × 3 exits; the identity
> `defect = N − save` asserted against the direct (GR-28) sum,
> `gcap.g_formula` and exact `subgraph_g` at 72 120 pairs, `--exh`;
> the binding consequences at 509 binding instances, `--charge`)*
> At an admissible colouring:
>
> **(i) The minority dart.**  Every hub's three darts form a 2-1
> pattern (the mono-hub ban): a **majority colour** `maj(v)` and a
> unique **minority dart** `m(v)`.  For a chunk `S` with interior `v`,
> the S-pair at `v` is monochromatic **iff the exit dart at `v` is
> `m(v)`**, and then its colour is `maj(v)`.
>
> **(ii) The save form.**  `defect_A(S) = N(S) − save_A(S)`, where
> > `save_A(S) = #{interiors v : exit(v, S) = m(v), maj(v) = A}
> >             + #{odd β ∈ S : β B-majority}`.
>
> **(iii) Binding needs two aligned weaknesses.**  `S` binding in A ⟺
> `save_A(S) ≥ N(S) − 2`; with (GR-32)(v) this forces `save_A ≥ 2`.
> A hub contributes to `save_A` only for chunks exiting at its one
> minority dart, and only in its one majority colour: **weakness is a
> scarce, directed resource** — per hub, one dart, one block.
>
> **(iv) The orientation form.**  When every branch of `S`-relevant
> support is even, dart colours are exactly an **orientation** of the
> hub multigraph (A-end = head): admissible ⟺ every in-degree is 1 or
> 2 (balance is automatic — even branches contribute `ℓ/2` to each
> block; the class forests are automatic at `Λ = ∅`), a hub's minority
> dart is its out-dart (in-degree 2, weak-A) or its in-dart (in-degree
> 1, weak-B).  The target is then: *orient `G°` with in-degrees in
> {1, 2} so that no chunk collects `N − 2` weaknesses in one block* —
> a pure orientation problem with the odd branches (at most 6, an even
> number, each costing ≥ 1 excess) entering as a bounded decoration
> plus one global balance bit-choice.

*Proof.*  (i) is the pattern enumeration.  (ii): split (GR-28)(i)'s two
sums by (i): `Σ(A(β) − 1) = w₃ + w₄ + 2w₅ − #{B-majority odds in S}`
(the alternation table of *Step G34*), and
`#{non-AA interiors} = z − #{AA S-pairs}`.  (iii) is (ii) plus
(GR-32)(v).  (iv): an even branch's two end darts always differ
(alternation), so the dart data is exactly a choice of A-end per
branch; the in-degree window is the mono-hub ban.  ∎

**What the lemma buys.**  Every question below becomes bookkeeping over
(hub, minority-dart, majority-colour) triples.  The exact-alignment
observation of *Step G36* is now a formula: a defect-0 configuration is
`save = N`, i.e. *every* interior's minority dart pointed out of `S`
with one majority colour — W5's witness colouring is measured at
exactly `save_A = 4 = N` (`--adv`).  And the *g-flank question*
becomes: can the habitat force every in-degree-{1,2} orientation (plus
odd decoration) to align `N − 2` weaknesses on some chunk?  **Corrected
by GORIENT (*Step G43*):** the capacity slack of (GR-32) bounds a
binding chunk's *defect*, not its *capacity* — `cap` carries no upper
bound at a binding chunk (W5's own binding subset has `cap = 8`), so
"capacity-tight or one off" strictly under-describes the obstruction
family; the honest family is the **binding-capable** chunks defined
there.  The census below (upgraded to the exhaustive stratum in *Step
G46*) still finds the habitat at `n ≤ 6` nowhere near the required exit
density on that corrected family.

---

### Step G40 — (GR-34): the route adjudication — the union-bound is refuted by a constructed witness; the correlated rung-minority rule closes the ladder family

**(i) The first-moment/union-bound route, REFUTED as a route.**  The
spec named the union bound as the (existence direct) form's open risk:
an argument that charges each binding configuration's thinness and sums
must have `Σ_S P(S binding) < 1`.  That is **false in habitat**, by
construction:

> **(GR-34)** *(the refutation witness constructed and measured,
> `--charge`; the constant-probability witness measured at W5,
> `--adv`)*  On the circular ladders `CL_m` (hub graph
> `cflank.ladder`, excess `2+2+2` on three adjacent rungs — the CFLANK
> `--tight` recipe, habitat-certified by the proven (GR-25) criterion
> at `n = 2m ≤ 20`), the **interval chunks** (consecutive square
> blocks; `z = 4`, exits the four boundary rims; `Θ(m²)` of them)
> already give, over seeded admissible colourings,
> > `E[#binding among intervals + circuits] = 0.23 (CL6), 1.68 (CL8),
> > 3.23 (CL10)`,
>
> exceeding 1 and growing — while **every member keeps a fully-good
> colouring, proven per shape** (below).  Moreover the binding
> probability of a *fixed* chunk does not decay with its size: W5's
> 16-branch, `z = 4` subset is binding at **43/200** seeded admissible
> colourings (two aligned interiors of four suffice at `N = 4`), so
> event probabilities are bounded below by a constant while the
> events' supports overlap without bound — no Lovász-local-lemma-shaped
> per-event scheme applies either.  **Any proof of the target must
> correlate the per-hub minority choices; no uncorrelated charging can
> close it.**

**(ii) The correlated route, opened: the rung-minority rule.**  On
`CL_m` with even `m`, give every top hub the rim darts `c_i` (alternating
`c_{i+1} = ¬c_i`) and the rung dart `¬c_i`, dually on the bottom ring.
Then **every hub's minority dart is its rung** — and no interval or
square chunk ever exits through a rung, so `save ≡ 0` on the entire
family, `defect ≥ 3` everywhere on it, and NC1 holds with `h_≠ = 4` at
every square.  Machine-certified at CL6/CL8/CL10 (`--charge`): the rule
colouring is admissible, its minority darts are all rungs, `save = 0`
at all 24/48/80 intervals, and — the complete certificate, no chunk
enumeration needed — an **exact rational `dim Z = 0` point in both
blocks through both matrices**, which by (GR-8)'s proven `≥` direction
is a per-shape **proof** of fully-goodness.  Two honest limits,
recorded: the pure rule needs **even `m`** (rim alternation is a parity
condition; odd `m` needs one deviating hub, absorbable at an excess
rung — observed, not developed), and the rule is proven **per tested
shape**, not for all `m` (the all-`m` statement would need the ladder's
chunk classification, which nothing here requires).

**Why this adjudication is the direction's pivot.**  Mechanism form 1
as literally specified — charge thinness against the budget, per
configuration — is dead, and not because the budget fails (it holds:
(GR-32)) but because *summing* per-event bounds is the wrong shape.
The surviving problem is a **constraint satisfaction over minority
darts** in which the ladder family — the densest interval-chunk habitat
family the excess law allows — is solved by pointing every weakness at
a branch no tight chunk uses as an exit.  That is the exact shape of
the general question (*Step G42*).

---

### Step G41 — (GR-35): the uncrossing lemma, the guided repair, and the hot-dart census

> **(GR-35)** *(the lemma proven; asserted at 1526 hub-sharing
> low-defect chunk pairs with formula-level union/intersection,
> `--charge`; the guided distances rank-certified at all four GUNIF
> witnesses and 120/120 pool binding colourings, `--repair`; the census
> originally at 199 pool shapes, `--adv` — upgraded to all 4920 pool
> shapes by GORIENT *Step G46*, `--hot`)*
>
> **(i) Submodularity.**  For branch sets `S, S′` with every `S`- and
> `S′`-degree in {2, 3},
> > `defect_A(S) + defect_A(S′) ≥ defect_A(S ∪ S′) + defect_A(S ∩ S′)`,
>
> the right side read as the (GR-28)(i) **formula** (no connectivity or
> 2ec-ness needed on `∪` or `∩`; the formula is a sum of nonnegative
> terms on any edge set).
>
> **(ii) Uncrossing.**  Two binding-in-A chunks sharing a hub have a
> chunk union (2ec sets sharing a hub union to a 2ec connected set) with
> `defect_A(S ∪ S′) ≤ 4 − defect_A(S ∩ S′)`: crossing binding chunks
> either **merge into a binding union** (when the intersection carries
> formula-defect ≥ 2) or **intersect in a defect-≤ 1 set** — the
> structure the (GR-29) ledger prices, and whose chunk form is absent
> at `n_hub ≤ 6` under NC1 ((GR-29) corollary; at `k ≤ 2` absent at
> every `n` by (GR-17)(c)/(GR-28)(iii)).
>
> **(iii) The guided repair (measured).**  At every GUNIF witness the
> recorded flip distance — 2/2/2/3 — is realized by flips of
> majority-side even branches **at the weak interiors of the named
> binding subset only** (candidate sets of size 6/4/4/8), endpoint
> rank-certified in both blocks through both matrices; on the swept
> stratum the same guided move set realizes *Step G32*'s law at
> 120/120 sampled binding NC1-passing colourings (112 at distance 1,
> 8 at distance 2, 0 beyond).
>
> **(iv) The hot-dart census (measured; upgraded to exhaustive by
> GORIENT *Step G46*).**  Call a dart **hot** when it is an exit of some
> capacity-tight (`cap = 7`) proper chunk.  Originally measured over 199
> pool shapes (**2** hubs with two hot darts, **0** with three); over
> **all 4920** pool shapes, exhaustively: **32** hubs with two hot
> darts, **0** with three — same verdict.  **This census undercounts
> the true obstruction family** (*Step G43*'s correction): it sees only
> `cap = 7` exits, missing binding-capable chunks of higher capacity
> (W5's own binding subset, `cap = 8`).

*Proof of (i).*  The branch sums are modular.  Per hub `v`, write
`ψ_T(v) = [deg_T(v) = 2]·[the T-pair at v is not AA]`; it suffices that
`ψ_S + ψ_{S′} ≥ ψ_∪ + ψ_∩` at every `v`.  If `v` lies in one set only,
both sides equal its one contribution.  Otherwise `deg_S(v), deg_{S′}(v)
∈ {2, 3}` in a cubic host, so the dart sets share ≥ 1 dart, and the
cases are: both degree 3 (all four terms 0); degree 3 and degree 2
(`∪` has degree 3 ⟹ `ψ_∪ = 0`; `∩`-pair = the degree-2 pair ⟹
`ψ_∩ = ψ` of that side; equality); both degree 2 with the same pair
(all four pairs equal; equality); both degree 2 sharing one dart (`∪`
degree 3 and `∩` degree 1 ⟹ RHS = 0, and the two pairs cannot both be
AA — three darts with two AA-pairs through a shared dart would be a
monochromatic hub — so LHS ≥ 1 when either side could have mattered,
and ≥ 0 always).  ∎

*Proof of (ii).*  Union of two bridgeless connected edge sets sharing a
hub is bridgeless and connected; degrees stay in {2, 3} (subsets of a
cubic star).  Apply (i) with `defect_A(S), defect_A(S′) ≤ 2`.  ∎

**What (ii) is for.**  It is the privacy-style hypothesis of (GR-24)'s
template, manufactured rather than assumed: on any stratum where
defect-≤ 1 sets are excluded (e.g. `n_hub ≤ 6` under NC1 — with the
honest caveat that the exclusion is proven for *chunks*, and the
intersection is a priori only a formula object whose 2ec core the
ledger covers), **maximal binding chunks are closed under crossing
union**, so the maximal binding family is pairwise non-crossing and a
simultaneous guided repair has disjoint targets.  Turning that into the
(repair form) theorem — "distance ≤ g", the post-refutation form
(GR-31) suggested — needs exactly two more pieces: the defect-≤ 1
**intersection kill** (extend the ledger's clauses from chunks to
formula-level sets), and a **no-collateral clause** for the guided flip
(a flip at a weak interior moves one dart at one other hub; (iii)'s
120/120 + 2/2/2/3 measurements say collateral is absorbed in practice).
Neither is closed here; both are named, dispatchable, and bounded.

**The sticking configuration, named.**  The correlated route (G40(ii))
generalizes to: *choose minority darts so that no capacity-tight chunk
collects `N − 2` of them as exits, in either colour*.  The obstruction
shape is a **hub all three of whose darts are hot** — then every
pattern at that hub is weak *for* some tight chunk, and a Hall-type
condition over the tight-chunk hypergraph decides feasibility.  (iv)
says the swept stratum has **no such hub** (and near-zero density of
even two-hot hubs): the CSP is loose at `n ≤ 6`, exactly matching the
abundance measurements ((GR-26)(iii), (GR-31)(i), and `--adv`'s 35/60
fully-good rate at W5).  A g-flank, if one exists, must realize a
saturated tight-chunk hypergraph — no known construction comes close,
and the (GR-29)-ledger structure any tight chunk must carry makes
saturation expensive.  **This is the sharpest g-flank specification the
arc has**: the `n_hub = 8` enumerator (the conditional tenth direction)
should enumerate habitat shapes with a maximally hot hub and test the
orientation CSP, instead of sweeping blind.

**Correction, GORIENT *Step G43*.** The capacity-tight sub-hypergraph
above is a strict *under-proxy* of the true Hall-relevant family — the
**binding-capable** chunks (*Step G43*) are far larger (2721 vs 252
exit darts measured on a subsample) and DO carry fully-hot hubs (761,
vs 0 here); this paragraph's "no such hub" verdict holds only for the
narrower capacity-tight family.  The corrected census, on both the
binding-capable and the exact realized-binding families, is *Steps
G45–G46*.

---

### Step G42 — where this leaves the target and the (GR-15) line (hand-off)

- **The target — uniform fully-good existence at `Λ = ∅` `D = 0` —
  stays OPEN**: not proven (the orientation CSP's general feasibility
  is the one missing theorem), not refuted (no g-flank; the pointwise
  mechanism is impossible by (GR-32)(iv), and the covering mechanism
  needs a saturated hot hub that no habitat shape exhibits).  Riders
  carried verbatim: the statement lives at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)**; the `Λ ≠ ∅` closed-form analogue stays
  **unswept**; the `D > 0` lift stays **unswept**; and none of this
  closes (GR-15) — at best the target would close (GR-15) on this
  stratum modulo (GR-4′), and the target itself is open.
- **What is newly PROVEN**: (GR-32) (capacity theorem, pair identity,
  whole-graph criticality, anti-flank floor), (GR-33) (weakness lemma,
  orientation form), (GR-35)(i)–(ii) (submodularity, uncrossing).
  **What is newly REFUTED**: the uncorrelated (first-moment /
  per-event-decay) version of the (existence direct) mechanism —
  constructed witness CL10, constant-probability witness W5's subset.
  **What is measured**: the guided-repair distances (= the recorded
  2/2/2/3 and ≤ 2 laws, now localized to weak sites), the hot-dart
  census, W5's abundance (35/60) and binding (43/200) fractions.
- **The surviving route, in one sentence**: prove that every habitat
  shape admits an in-degree-{1,2} orientation (plus balanced odd
  decoration) in which no capacity-tight chunk collects `N − 2`
  same-colour weaknesses — the uncrossing lemma organizes the tight
  chunks, the hot-dart scarcity says the constraint hypergraph is
  sparse, and the ladder rule is the worked example.  Its two
  dispatchable sub-lemmas: the defect-≤ 1 intersection kill (a ledger
  extension), and the no-collateral clause for guided flips (the
  (repair form) closure at `n ≤ 6`).  **Superseded by *Step G47*:** the
  "capacity-tight chunk" framing here is corrected to the
  binding-capable family, and the route is re-anchored on a
  bounded-deviation selection principle instead.
- **For the route ledger** (`notes/Pencil-fanout-archive.md` §"Ninth
  direction"): entry 1 (this direction) lands as
  **open-with-named-dispatchable-attacks** (the orientation theorem;
  the two sub-lemmas; the pruned hot-hub enumeration at `n = 8`) — a
  MISS with a named sticking configuration in the spec's sense, plus
  three proven structural theorems.  E1 does not fire (no flank), E2
  does not fire (the ledger keeps dispatchable entries), E3 does not
  fire (the target is not proven).
- The (K-res)/(GR-15) quantification question stays a coordinator
  hand-off note, untouched here (spec caution).  Class uniformity of
  `hK` is untouched; **no gap-map status moves**.

---

### Verification (Steps G38–G42)

`notes/scripts/w4/gexist.py` (**new with this pass**, untracked;
imports `gunif.py` — the witness constructions `WITNESSES` /
`wit_colouring` / `spec_to_hm_index` — plus `gcap.py` (`branch_stats`,
`g_formula`, `pool_specs`, `subset_eidx`, `two_ec_masks`/`_subsets`),
`cflank.py` (`admissible`, `cubic_habitat`, `hub_model`,
`nc1_violations`, `flip_branch`), `gridcol.py`, `grid.py`, `gridwit.py`,
`closure.py`, all read-only).  Exact throughout (integers; rank only
through `gridcol.block_generic_zero`'s GF(p) lower bound, every
attaining draw re-checked in exact ℚ through **both** the branch system
and the landed `grid.dim_Z` — README §4 convention 2).  Rngs seeded per
mode, seeds printed; no `set` printed; nothing samples a placement, so
`repin.star_generic` gates nothing (§(K-clos) (AC-9)).  No pool is new:
the 4920-shape stratum is regenerated by the same `gcap.pool_specs`
enumeration and **asserted equal to the recorded 4920**; ladders are
targeted constructions on the CFLANK `--tight` recipe, habitat-gated by
the proven (GR-25) criterion per instance.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --exh      # ~12 s  (GR-32): trichotomy at 220 038 chunks; identity chain; pattern lemma; F13 pair
PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --charge   #  ~9 s  (GR-33)/(GR-34): binding needs >= 2 weak items; uncrossing at 1526 pairs; CL6/8/10
PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --repair   #  ~3 s  (GR-35)(iii): guided distances 2/2/2/3 at the witnesses; 120/120 pool law
PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --adv      #  ~5 s  W5 priced (cap 8 / cut 7, save_A = N); 43/200 binding, 35/60 fully good; hot-dart census
PYTHONHASHSEED=0 python3 notes/scripts/w4/gexist.py --validate # ~30 s  all four in one process (inside the 600 s budget; no F15 shape needed)
```

**Which driver mode tests which sentence (F11 — doubly binding: the
direction's claims are case-list / exhaustiveness claims).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-32)(i) pair identity + (GR-33)(ii) save form | `--exh` | `defect = N − save` asserted against the direct (GR-28) sum, `gcap.g_formula`, and exact `subgraph_g` (72 120 pairs, seeded ~2% deep sample for the third) |
| (GR-32)(ii) trichotomy | `--exh` | every 2ec chunk of every pool shape classified and asserted (`proper/improper ≥ 7`, whole graph `= 6`, improper `z` even), 220 038 chunks; pool count asserted `== 4920` |
| (GR-32)(iii) criticality | `--exh` | `defect_A = defect_B = 3` at `E(G°)` asserted at every sampled admissible colouring |
| (GR-32)(iv) floor / F13 pair | `--exh` | `θ(2,4,4)`: habitat gate asserted REJECTING, `cap` asserted `= 4 < 6` (pinned counter-fact: NC1 satisfiable there, *Step G33*); negative control `K4(3⁶)` asserted in habitat with every chunk `≥ 6/7` |
| (GR-33)(i) pattern lemma | `--exh` | exhaustive: 6 non-mono patterns × 3 exits (unique minority; mono ⟺ exit = minority) |
| (GR-33)(iii) binding ⟹ ≥ 2 weak items | `--charge` | 509 binding (chunk, block) instances, `save ≥ N − 2` and `≥ 2` asserted at each |
| (GR-34)(i) union-bound refutation | `--charge` | CL6/8/10 habitat-asserted; `E[#binding]` over 60 seeded admissible colourings printed; asserted `> 1` and growing at CL10 |
| (GR-34)(i) constant event probability | `--adv` | W5's subset binding fraction measured (43/200), asserted below 1/2; fully-good fraction (35/60) asserted abundant |
| (GR-34)(ii) rung-minority rule | `--charge` | rule colouring asserted admissible, minority-=-rung at every hub, `save = 0` at every interval, NC1 clear, and exact-ℚ `dim Z = 0` in both blocks through both matrices |
| (GR-35)(i) submodularity | `--charge` | asserted at 1526 hub-sharing low-defect chunk pairs, formula-level `∪`/`∩` (an assert wired to fire on any counterexample) |
| (GR-35)(iii) guided distances | `--repair` | witness distances asserted `≤` recorded 2/2/2/3 with candidates restricted to weak sites; 120/120 pool binding colourings repaired at `≤ 2` guided flips, endpoint = full chunk re-scan |
| (GR-35)(iv) hot-dart census | `--adv` | per-shape tight-chunk enumeration; hubs with 2 and 3 hot darts counted (0 fully-hot reported, not asserted — it is a census, not a theorem) |
| the target, (GR-15), (GR-4′) as statements | — | **untouched and not driver-testable**: no mode probes them |

**Determinism.**  `--validate` (all four modes, one process) is
**hash-seed invariant across `PYTHONHASHSEED` 0 and 999**: every
substantive figure is identical, and the *only* diff is the printed
wall-clock `[Ns]` annotation (`[5s]` vs `[6s]`) — unlike the `gunif`
precedent, timing noise did bite here, so this run is not literally
byte-identical.

**Scratch probes (README's standing rule).**  None retained: every
figure above is produced by a committed driver mode.  (Two transient
debugging iterations of `--charge` during development — an
interval-indexing mismatch against `hub_model`'s branch order, fixed by
routing through `spec_to_hm_index`, and a wording-only correction of
the `--adv` abundance sentence — changed no mathematics; the final
driver re-derives everything.)

---

### Confidence verdict (Steps G38–G42)

| | claim | standing |
|---|---|---|
| **(GR-32)** | pair identity, capacity trichotomy, whole-graph criticality, anti-flank floor, `N ≥ 4` | **proven-informally** (proofs above; machine-certified at 220 038 chunks / 4920 shapes) |
| **(GR-33)** | minority-dart lemma, `defect = N − save`, binding ⟹ ≥ 2 aligned weaknesses, the orientation form | **proven-informally** (pattern lemma exhaustive; identity asserted against three independent computations) |
| **(GR-34)(i)** | the uncorrelated (first-moment / per-event-decay) existence mechanism | **refuted** (constructed witness CL10: `E[#binding] = 3.23 > 1` with fully-good proven per shape; constant-probability witness at W5) |
| **(GR-34)(ii)** | the rung-minority rule closes CL6/CL8/CL10 | **proven per shape** (exact-ℚ `dim Z = 0`, both blocks, both matrices); the all-even-`m` form is a stated pattern, not a claim |
| **(GR-35)(i)–(ii)** | submodularity of the defect formula; the uncrossing dichotomy | **proven-informally** (per-hub case analysis; asserted at 1526 pairs) |
| **(GR-35)(iii)** | guided repair realizes 2/2/2/3 and the ≤ 2 pool law from weak sites only | **measured** (rank-certified endpoints; a theorem form needs the two named sub-lemmas) |
| **(GR-35)(iv)** | hot-dart scarcity (0 fully-hot hubs at `n ≤ 6`) | **measured, now exhaustive** (all 4920 pool shapes, GORIENT *Step G46*; originally a 199-shape sample, same verdict) — undercounts the true (binding-capable) family, corrected in *Steps G43/G45–G46* |
| **the GEXIST target** | uniform fully-good existence at `Λ = ∅` `D = 0` | **OPEN** — proven per swept/constructed shape (as before), reduced to the minority-orientation CSP, with the named sticking configuration (the saturated hot hub) and three dispatchable attacks; **not** proven uniformly, **not** refuted, and never read without the riders |
| **(GR-15)** | | **OPEN — unchanged in both directions.**  No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**What would change this.**  *(i)* **The orientation theorem** — every
habitat shape admits an in-degree-{1,2} orientation plus balanced odd
decoration with `save ≤ N − 3` on every chunk in both blocks: that is
the target, hence (GR-15) at `Λ = ∅` `D = 0` **modulo (GR-4′)**; the
uncrossing lemma, the hot-dart sparsity, and the ladder rule are its
raw material, and a Hall/discharging argument over the capacity-tight
chunk hypergraph is the natural shape.  *(ii)* **Either named
sub-lemma** — the defect-≤ 1 intersection kill, or the no-collateral
clause — would upgrade the guided repair to a (GR-24)-analogue theorem
on the `n ≤ 6` stratum and re-open the (repair form) route in
(GR-31)'s "distance ≤ g" shape.  *(iii)* **A habitat shape with a
fully-hot hub** (all three darts exits of capacity-tight chunks) —
the g-flank's necessary seed and the pruned target for the `n_hub = 8`
enumerator (the conditional tenth direction): enumerate at the hot hub,
not blind.  *(iv)* **(GR-4′)** — unchanged; any movement changes what a
fully-good colouring buys.  *(v)* The **`Λ ≠ ∅` / `D > 0` analogues**
of (GR-32)/(GR-33) — both strata stay unswept; the capacity proof uses
(GR-25) at `D = 0` and (SD-6) only, so a `D > 0` analogue with
`2D + 6` budget is plausible but nothing here shows it.

### Steps G43–G47 (2026-08-13, direction GORIENT) — the orientation target is re-anchored on a **selection principle** (perfect-matching minority + bounded deviation) whose parity obstruction is exactly the cut space, a **structural charge** bounds every chunk's defect from below by its interior-adjacency count, the **intersection kill lands vacuously-strong on the whole `n_hub ≤ 6` stratum** (crossing same-block binding pairs do not exist there at all), the **hot-dart census family is corrected and the census upgraded to the exhaustive stratum**, and **no fully-hot hub exists anywhere searched** — but the orientation theorem, and with it the target and (GR-15), stays **OPEN**, with the sticking instance named at W3

Answering `notes/Pencil-fanout-archive.md` §"Tenth direction — GORIENT": the
orientation theorem — *every habitat shape (cubic `G°`, `ℓ_β ∈ [2,5]`
((SD-6)), `Σ(ℓ_β − 2) = 6` ((GR-21)), the proven (GR-25) cut criterion;
`Λ = ∅`, `D = 0`) admits an admissible colouring with `save_X(S) ≤ N(S) − 3`
at every proper chunk in both blocks* — the merged attacks (a)+(b), with (d)
folded in as a targeted-construction falsification control. Read against
*Steps G38–G42* ((GR-32)–(GR-35)), *Steps G34–G37* ((GR-29)–(GR-31)),
*Steps G24–G28* ((GR-21)–(GR-26)), and the *Shared dictionary*'s (SD-6).

**Step 0 pin (mandatory, discharged before any derivation).** **(GR-32)**
from the statement: the pair identity
`defect_A + defect_B = 2z + exc − z_mono`, the trichotomy (proper ⟹
`cap ≥ 7`; improper `z` even, `z = 0` forces `S = E(G°)` at `cap = 6` with
`defect_A = defect_B = 3` identically), `N ≥ 4` at proper chunks.
**(GR-33)**: the minority-dart lemma, `defect = N − save`, binding ⟺
`save ≥ N − 2 ≥ 2`, and the orientation form with both caveats (odd branches
as bounded decoration — at most 6, an even number — plus the global balance
bit; class forests automatic only at `Λ = ∅`). **(GR-35)(i)–(ii)**:
submodularity's exact scope (formula-level sets, degrees in {2,3}, no
connectivity on `∪`/`∩`) and the dichotomy's honest caveat — the
intersection-kill job description. **(GR-34)(i)**: no uncorrelated charging
closes the target (CL10, W5's subset); **(GR-34)(ii)**: the rung-minority
rule verbatim with its two limits (even-`m` parity; proven per tested
shape). **(GR-29)**'s ledger + exact boundary; **(GR-30)** with W5 the
structural heart — W5 is priced FIRST below (*Step G43* and `--adv`).
**(GR-4′)'s proven-case boundary** (≤ 3 classes or all-singleton classes)
covers no habitat block, so the rider below is genuinely load-bearing.
**The hot-dart census's evidence grade**: measured, 199 pool shapes,
`n ≤ 6` — a census, not a theorem (it is upgraded, and its family
corrected, in *Step G46*).

**The closure chain, with the riders, stated before anything is claimed.**
The target implies (GR-15) at `Λ = ∅` `D = 0` **modulo (GR-4′)**
(certificate 3 of (GR-20)); (GR-15) there + (GR-1)/§(K-clos) (AC-4) +
(GR-5) + (AC-7) would discharge `hK` on the tight `D = 0` stratum. The
**`Λ ≠ ∅` closed-form analogue stays unswept**, the **`D > 0` lift stays
unswept**, and **nothing here closes (GR-15)** — nothing below claims to.

**Two spec premises corrected against source, stated up front** (the
fan-out spec asks for this plainly):

1. **The "capacity-tight chunk hypergraph" is a strict under-proxy of the
   Hall constraint family.** *Step G39*'s gloss — "each such chunk must be
   capacity-tight or one off" — is **false as a statement about binding
   chunks**: binding bounds `defect`, and the pair identity puts no *upper*
   bound on `cap` at a binding chunk. W5's own named subset is the landed
   counter-instance — `cap = 8`, binding at 43/200 (both figures *Step
   G41*/`gexist --adv`) — so its exits are **invisible to (GR-35)(iv)'s
   census**, which counted only `cap = 7` exits. The corrected obstruction
   family is the **binding-capable** chunks (*Step G43*), and the corrected
   seed census is run in *Steps G45–G46*. The `2(k−1)`-cycle scaling family
   realizes binding-capable chunks of capacity `2k − 2` (machine-realized
   to `k = 5`), so the under-coverage grows with `k`.
2. **(GR-35)(iv)'s "199 pool shapes" was a subsample census.** It is
   upgraded here (`--hot`) to the **exhaustive** 4920-shape stratum: still
   0 fully-hot hubs, 32 hubs with ≥ 2 hot darts. The correction changes no
   verdict; it changes the statement's evidence grade at `n ≤ 6` from
   census to **exhaustive fact**.

**Headline, stated before the mathematics.**

- **(GR-36), the structural charge (proven).** `defect_A(S) = w45(S) +
  #{A-majority odd branches in S} + #{non-AA interiors}` — and an S-branch
  joining two AA interiors is forced **odd A-majority**, so on the
  interior-adjacency graph `J(S)` (a **path forest** for `k ≥ 2`),
  `defect_X(S) ≥ w45(S) + Σ_paths ⌈m_i/2⌉` in **both** blocks. A binding
  chunk therefore has `m_J ≤ 4 − 2·w45`: binding costs *interior
  adjacency*, the proven form of *Step G36*'s "structure, not excess".
  Asserted at 338 364 (colouring, chunk) pairs; 10 190 AA-adjacent pairs,
  every joining branch odd A-majority.
- **(GR-37), the selection reduction (proven), and the ladder parity
  explained.** Admissible colourings **are** pairs (majority colour,
  minority dart) subject to one GF(2) equation per branch plus balance.
  For any **perfect matching** `M` of `G°` (exists: cubic bridgeless,
  Petersen), the all-`M`-minority prescription's obstruction vector is
  **exactly the even-branch indicator** — solvable iff that vector lies in
  the cut space of `G°`; on the all-even stratum, iff `G°` is bipartite.
  The rung-minority rule is the instance `M = rungs`, and `CL_m` is
  bipartite iff `m` is even — **(GR-34)(ii)'s parity limit is the cut-space
  criterion**, not a ladder accident. Deviations reach every obstruction
  class (the shift vectors span modulo cuts, since star cuts have odd
  weight), so consistency is always repairable; asserted at 5409
  (matching, branch) pairs and by construction on the pool.
- **(GR-38), the intersection kill — settled at `n ≤ 6`, vacuously
  strong.** The submodularity sharpens to an **exact identity**
  `defect_A(S) + defect_A(S′) = defect_A(∪) + defect_A(∩) + slack`, with
  the slack supported on shared different-pair degree-2 hubs and ≥ 1 per
  such hub; the **attachment lemma** classifies every crossing. On the
  **complete** `n_hub ≤ 6` stratum (all 4920 shapes, all 284 512 admissible
  colourings — the same exhaustiveness grade as (GR-26)), **crossing
  same-block binding pairs sharing a hub do not exist at all** (0 pairs
  among 53 740 binding instances): the maximal binding family is
  **laminar outright**, and the kill holds with nothing to kill. The
  identity and the lemma are certified non-vacuously at 58 495 crossing
  low-defect pairs.
- **(GR-39), the hot-hub adjudication: NOT FOUND, with partial
  impossibility.** Structure theorem: a capacity-tight chunk is chordless
  with `(z, exc) ∈ {(2,3), (3,1)}` and **short exits** (`z = 2`: both
  exits of length ≤ 3). Kills, each a proof: **K4-saturation** (three
  tight triangles at a hub force `G° = K4` with `A = 3 < 6` — no length
  assignment survives, 4096 enumerated), the **digon kill**, and the
  **corner-set kill**, which together close the (triangle, triangle, ⋆)
  cell. Census: **0 fully-hot hubs** on the exhaustive `n ≤ 6` stratum, at
  all four GUNIF witnesses, at CL6/CL8/CL10 (ladders have **no tight
  chunks at all**), at the Q3/V8 targets, and across a 10 984-completion
  targeted digon-frame hunt (caps disclosed). In the **corrected**
  (realized-binding) family — exact at `n ≤ 6` — 506 hubs carry ≥ 2
  realized-hot darts and **0 carry three**.
- **The sticking instance, named (the honest MISS).** The selection
  principle *"some perfect matching plus ≤ 2 deviations is fully good"*
  holds at **120/120** subsampled pool shapes (deviation histogram
  7/52/61) and at W3M, W4, W5 (rank-certified) — and **fails at W3**: the
  ≤ 2-deviation neighbourhoods of all 8 perfect matchings of W3's hub
  graph contain **no** admissible colouring that even passes the screen
  (named subset non-binding + NC1), while W3's actual fully-good minority
  maps sit at matching-distance **3, 5, 6** (sampled). The uniform
  question is now: *is there a bound `d` such that every habitat shape
  has a fully-good colouring within `d` deviations of some perfect
  matching?* — measured `d ≤ 2` on the swept stratum and at 3 of 4
  witnesses, `d = 3` sufficient at W3, no bound proven.
- **What does NOT move.** The orientation theorem stays **OPEN** — proven
  per shape everywhere swept or constructed (nothing new), refuted
  nowhere, **no g-flank found**, no fully-hot seed found. (GR-15) stays
  OPEN, unchanged in both directions; (GR-4′)/(GR-10) untouched; **no
  gap-map status moves**.

**Notation (on top of *Steps G38–G42*).** `w45(S) := w4 + w5`. For an
admissible colouring, an interior of `S` is **AA** when both its S-darts
are A (equivalently weak-A: exit = minority, majority A, (GR-33)(i)).
`J(S)` = the **interior-adjacency graph**: vertices the interiors of `S`,
one edge per S-branch joining two interiors; `m_J` its edge count. A pair
of chunks **crosses** when they share a hub and neither contains the
other. `M` always denotes a perfect matching of the hub multigraph `G°`
(branch level: parallel branches count separately). A **deviation** from
`M` at `v` re-points `m(v)` off `v`'s matching dart.

---

### Step G43 — (GR-36): the structural charge — binding costs interior adjacency, in both blocks

> **(GR-36)** *(proven; the bound and the path-forest clause asserted at
> 338 364 (colouring, chunk) pairs of a 120-shape seeded pool subsample,
> with the evaluator cross-checked against the landed `defect_direct` at
> 3324 pairs, `--hall`)* Let `S` be a chunk of a habitat shape at an
> admissible colouring.
>
> **(i) The charge form of (GR-28)(i).**
> > `defect_A(S) = w45(S) + #{A-majority odd branches in S}
> >               + #{non-AA interiors of S}`,
>
> and dually for B. In particular `defect_A ≥ w45` always.
>
> **(ii) AA-independence.** An S-branch joining two AA interiors has an
> A-dart at both ends, hence is **odd and A-majority** (an even branch's
> end darts differ; a B-majority odd branch's end darts are both B). So
> AA interiors are independent across even and B-majority-odd branches.
>
> **(iii) The J-bound.** For `k ≥ 2`, `J(S)` is a **path forest** (an
> interior has ≤ 2 J-neighbours; a J-cycle's hubs have both S-darts on
> the cycle, so the cycle is a component of `S`, forcing `S` = that
> circuit, `k = 1`). Per J-path with `m_i` edges, the non-AA gaps and
> the A-majority-odd edges together number ≥ `⌈m_i/2⌉`, whence
> > `defect_X(S) ≥ w45(S) + Σ_paths ⌈m_i/2⌉`, `X ∈ {A, B}`.
>
> A binding chunk therefore has `m_J(S) ≤ 4 − 2·w45(S)`. (For `k = 1`,
> `J` is one cycle and the same count gives `defect_X ≥ ⌈z/2⌉` — NC1
> subsumes it at `z ≥ 6`.)
>
> **(iv) Exit-sharing exclusion.** Two interiors of `S` whose exits are
> the two ends of a single **even** non-S branch cannot both be AA (nor
> both BB): both S-pairs mono in one colour forces the shared exit
> branch's end darts equal, impossible for an even branch. (Proven; the
> configuration has **0 instances** on the swept subsample — recorded so
> the clause is not re-derived, not as evidence of impossibility.)

*Proof.* (i): regroup (GR-28)(i) — `ℓ4` costs 1, `ℓ5` costs `1 +
[A-maj]`, `ℓ3` costs `[A-maj]`, `ℓ2` costs 0; the interior term is
unchanged. (ii): darts of an even branch differ (alternation); darts of
an odd branch both carry its majority. (iii): path-forest as stated. On
a J-path, let `a` of its `j` vertices be AA in `b` blocks (maximal runs):
AA-AA adjacencies ≥ `a − b` — each an A-majority odd branch by (ii) —
and non-AA vertices on the path ≥ `b − 1`; with `b ≤ ⌈j/2⌉` the two
charges sum to ≥ `(a − b) + (j − a) = j − b ≥ ⌈(j−1)/2⌉ = ⌈m_i/2⌉`.
Summing paths and adding `w45` gives (iii); the B-block bound is the
mirror. (iv) is the alternation argument stated. ∎

**Why this is the load-bearing step.** *Step G36* corrected the old
mechanism to "binding at `g ≥ 2` costs structure, not excess" and left
charging that structure to a successor. (GR-36) is the charge in its
provable half: every unit of interior adjacency inside a chunk costs half
a defect unit in **both** blocks simultaneously, colouring-free. The
honest boundary is equally sharp: **W5's subset has `m_J = 0` and
`w45 = 0`** — its interiors are pairwise corner-separated — so the bound
charges it **nothing** (`--adv` asserts exactly this). What the W5 family
costs is **corner A-darts** ((GR-29)(iii): corners eat A-darts, and
cost-0 paths present them only at [ℓ2] heads); a corner-side analogue of
(iii) is the one missing charge, named in *Step G47*.

**The corrected obstruction family.** Call a chunk **binding-capable**
when `w45 + Σ⌈m_i/2⌉ ≤ 2` — the necessary condition (iii) leaves open.
This family is the honest Hall hypergraph, and it **strictly contains**
the capacity-tight family (spec correction 1 above): on a 184-shape pool
subsample, 2721 binding-capable exit darts vs 252 cap-7 exit darts, with
**761 fully-capable-hot hubs vs 0** fully-cap-7-hot (`--adv`). The
necessary condition is loose — the **realized** family (chunks that
actually bind at some admissible colouring, exactly computable at
`n ≤ 6`) has **0 fully-hot hubs** (*Step G45*) — but it is the right
*shape* for a future Hall argument: local, colouring-free, and closed
under the structures the ledger prices.

---

### Step G44 — (GR-37): the selection reduction — matchings anchor the minority map, and the parity obstruction is the cut space

> **(GR-37)** *(proven; (i) round-tripped at 230 colourings, (ii)
> asserted at 5409 (matching, branch) pairs over 120 shapes and at
> CL5–CL8, (iii) exercised constructively on the whole subsample,
> `--hall`)*
>
> **(i) The (c, m) model.** Admissible colourings of a habitat shape
> correspond exactly to pairs (`c : hubs → {A, B}` majority colours,
> `m : hubs → incident darts` minority darts) satisfying, per branch
> `β = (u, w)`,
> > `c(u) ⊕ c(w) = [ℓ_β even] ⊕ [m(u) on β] ⊕ [m(w) on β]`,
>
> plus odd-branch balance (`#A-majority = #B-majority`); the mono-hub
> ban is automatic, and the correspondence is the (GR-33)(i) pattern
> read backwards.
>
> **(ii) The matching rule and its obstruction.** For a perfect matching
> `M` of `G°` (one exists: `G°` is cubic and bridgeless), the all-`M`
> prescription (`m(v)` = the matching dart, all `v`) makes the two
> minority indicators **cancel on every branch** — matching branches
> carry both, non-matching branches neither — so the system's
> right-hand side is the even-branch indicator `[ℓ even]` for **every**
> `M`. Hence the rule extends to an admissible colouring iff `[ℓ even]`
> lies in the **cut space** of `G°` (then exactly two extensions, a
> global A↔B swap apart, before balance). All-even stratum: iff `G°` is
> **bipartite**. Ladders: `CL_m` is bipartite iff `m` is even, and at
> even `m` the two extensions of the rung matching **are** the
> (GR-34)(ii) rung-minority colouring and its swap — the rule's parity
> limit is the cut-space criterion.
>
> **(iii) Deviations reach everything.** A deviation at `v` (re-point
> `m(v)` to a non-matching dart `d`) shifts the right-hand side by
> `e_{M(v)} + e_{β(d)}`. These pair-shifts generate the even-weight
> subspace of `GF(2)^M`, which maps **onto** `GF(2)^M`/cuts (a star cut
> has odd weight 3), so every obstruction class — parity and the balance
> rider alike — is reachable by finitely many deviations. *Caveat,
> recorded:* the constructive searches below always succeeded within 2
> deviations on the pool; a proven uniform bound on the deviation count
> is exactly what *Step G47* leaves open (W3 needs 3).
>
> *Second caveat — STATEMENT-BEYOND-PROOF, scoped to the balance
> clause only (GADM, Step G53):* the words "and the balance rider
> alike" are NOT delivered by the proof below.  The span argument
> manipulates only classes in `GF(2)^{E(G°)}/Cut(G°)` — the parity
> obstruction — and balance is not a class function: at a fixed
> parity-consistent `m` the two `c`-solutions swap the odd-branch
> majority counts, so balance is decided by `m` alone, which the
> class-level argument never touches.  The parity half stands as
> proven; per-shape admissibility is the fanout route ledger's
> **entry 5**, a separate open statement.

*Proof.* (i): given an admissible colouring, every hub is 2-1
((GR-33)(i)); conversely (c, m) determines every dart (`c(v)` off
`m(v)`, flipped on it), the branch equation is alternation, and no hub
is mono by construction. (ii): `[m(u) on β] ⊕ [m(w) on β] =
[β ∈ M] ⊕ [β ∈ M] = 0`. Solvability of `c(u) ⊕ c(w) = t(β)` over a
connected graph ⟺ `t` orthogonal to cycles ⟺ `t` ∈ cut space; all-ones
∈ cut space ⟺ bipartite, and at all-even `[ℓ even]` = all-ones. (iii):
the pair-shift graph (branches as nodes, `M(v)`-to-`β(d)` pairs as
edges) is connected because `G°` is, so telescoping sums give every
`e_x + e_y`; evens + cuts = everything since cuts ⊄ evens. ∎

**The good-PM measurement (the Hall question, sharp form).** Define a
**good selection** = (perfect matching `M`, ≤ `d` deviations, a
`c`-solution) whose colouring is admissible and **fully good**. Measured
(`--hall`, exact full-chunk scan, no rank): at `d = 2`, **120/120**
subsampled pool shapes have one, histogram `d = 0/1/2 : 7/52/61`. At the
witnesses (`--adv`, rank-certified endpoints, both blocks, both
matrices): W3M, W4, W5 **have** a good selection at `d = 2` (their
matching counts: 7/10/30); the ladders at `d = 0` (the rung matching);
**W3 does not at `d ≤ 2`** — over all 8 of its matchings, the
≤ 2-deviation neighbourhoods contain **no** screened admissible
colouring at all — while its sampled fully-good minority maps sit at
matching-distance 3/5/6. So the sharpened conjecture is: *every habitat
shape has a fully-good colouring within a bounded number of deviations
of some perfect matching* — true at `d = 2` everywhere measured except
W3, true at `d = 3` at W3 by the distance witness, **unproven** in
general. This is the direction's surviving positive route: it replaces
the ladder-specific rung rule by a shape-free anchor whose parity
obstruction is understood exactly.

---

### Step G45 — (GR-38): the intersection kill — the exact slack identity, the attachment lemma, and the vacuously-strong answer on the whole `n ≤ 6` stratum

> **(GR-38)** *(the identity and lemma proven; certified at 58 495
> crossing hub-sharing low-defect pairs; the stratum statement
> EXHAUSTIVE over all 4920 shapes × all 284 512 admissible colourings,
> `--kill`)*
>
> **(i) The exact slack identity.** For branch sets `S, S′` with all
> degrees in {2, 3},
> > `defect_A(S) + defect_A(S′) = defect_A(S ∪ S′) + defect_A(S ∩ S′)
> >   + slack(S, S′)`,
>
> where `slack = Σ_v (ψ_S(v) + ψ_{S′}(v))` over the shared hubs of
> degree 2 in both with **different** pairs, and `slack ≥ #{such hubs}`
> (both pairs AA at one hub would be a mono hub). This sharpens
> (GR-35)(i) from an inequality to an identity with named support.
>
> **(ii) The attachment lemma.** Let `S, S′` be crossing chunks. Then
> `S ∩ S′ ≠ ∅` (two chunks sharing a hub share a branch: 2 + 2 > 3
> darts), and every component of `S′ ∖ S` attaches through **≥ 2 darts**
> (2-edge-connectivity of `S′`), each landing at an **interior** of `S`
> via its unique free dart (corners of `S` have no free dart, so at most
> one attachment per interior); each attachment hub is an **X-hub**
> (degree 2 in both, different pairs — a slack support point) or a
> **(2,3)-hub** (interior of `S`, corner of `S′`, degree 2 in `S ∩ S′`
> with pair = its S-pair). Dually for `S ∖ S′`.
>
> **(iii) The kill, and the stratum answer.** Two same-block binding
> chunks that cross have a binding union unless
> `slack + defect(S ∩ S′) ≤ 1`, which forces the **AA-glue**
> configuration: no X-hub, every attachment an AA (2,3)/(3,2)-hub, the
> intersection defect-free. On the complete `n_hub ≤ 6` stratum the
> question closes **above** the dichotomy: among 53 740 binding
> (chunk, block) instances over all admissible colourings of all 4920
> shapes, **not one pair of same-block binding chunks crosses** (0
> pairs; nested or hub-disjoint always) — the maximal binding family is
> **laminar outright**, per block, at every admissible colouring of the
> stratum, and the kill is a theorem there with nothing left to kill.
> The AA-glue configuration has **0 instances**; whether it is realizable
> at `n ≥ 8` is the named open case.

*Proof of (i).* Branch terms are modular. Per hub, the four cases of the
(GR-35)(i) proof are equalities except (2,2)-different-pairs, where
`ψ_∪ = ψ_∩ = 0` exactly (degree 3 in the union, 1 in the intersection)
and the left side contributes `ψ_S + ψ_{S′} ≥ 1` by the mono-hub ban. ∎

*Proof of (ii).* Sharing a hub with 2 + 2, 2 + 3 or 3 + 3 darts among 3
forces a shared dart. A component of `S′ ∖ S` with ≤ 1 attachment dart
would hang on a bridge of `S′` (its hubs off `S` have all their
`S′`-darts inside the component). An attachment dart at a corner of `S`
is impossible — all three darts of a corner lie in `S` while the
attachment branch does not. The classification is the degree count of
the attachment hub in `S′`. ∎

**What this buys, and what it does not.** The uncrossing organization
(GR-35)(ii) hoped for is, on the swept stratum, **free**: maximal binding
chunks never cross, so a simultaneous guided repair has laminar targets
there without any intersection hypothesis. What the exhaustive answer
does *not* give is the `n ≥ 8` form — W5-family chunks coexist and could
in principle cross; the identity (i) and lemma (ii) are proven at every
`n` and are the tools a successor applies there. The certification is
non-vacuous: the identity and lemma are asserted at 58 495 crossing
low-defect (≤ 4) pairs (attachment types: 76 498 X, 72 676 (2,3)-type)
— the binding-binding family is what turns out to be empty, not the
crossing phenomenon.

**The realized-hot census (exact at `n ≤ 6`).** As a by-product of the
exhaustive scan, the exits of every chunk that **actually binds** at some
admissible colouring are collected exactly: **506 hubs carry ≥ 2
realized-hot darts, 0 carry three**. This is the corrected-family form
of the (GR-35)(iv) sticking-configuration census (spec correction 1),
and at `n ≤ 6` it is an exhaustive fact, not a sample.

---

### Step G46 — (GR-39): the hot-hub adjudication — structure theorem, three kills, the exhaustive census, and no seed found

> **(GR-39)** *(structure theorem proven, asserted at all 2400 proper
> capacity-tight chunks of the pool; the kills proven with the K4 case
> machine-enumerated (4096 tuples); the census exhaustive at `n ≤ 6` and
> exact at the named large shapes, `--hot`)*
>
> **(i) Structure theorem.** A capacity-tight (`cap = 7`) proper chunk
> `S` is **chordless** (so `S = E(W_S)` — the (GR-32) proof's
> `cap ≥ 7 + ch`), has `(z, exc) ∈ {(2,3), (3,1)}` (`z = ∂(W_S)`;
> `z = 1` is a bridge, dead by (GR-25); `2z + exc = 7` with `exc ≤ 6`),
> and its exits are **short**: `f(W^c) ≤ 0` forces
> `Σ_exits (6 − ℓ) ≥ 7`, so at `z = 2` both exits have `ℓ ≤ 3`.
> Its capacity-tight **circuits** are exactly the `(2,2,3)` triangles
> (`z = 3`) and the `Σℓ = 7` digons (`z = 2`).
>
> **(ii) Three kills.** (a) **K4-saturation**: three tight triangles at
> one hub `v` pairwise share the `v`-star and force `G° = K4` (cubic
> saturation), where the three tightness equations sum to
> `2A + C = 21` (`A` = the `v`-star's total length, `C` = the opposite
> triangle's) while (GR-21) tightness forces `A + C = 18`; then
> `A = 3 < 6`, impossible. Enumeration over all 4⁶ length tuples
> confirms: **no** assignment satisfies all four constraints.
> (b) **Digon kill**: a digon costs `Σℓ ≥ 7` (girth), i.e. excess ≥ 3,
> so no `exc = 1` tight chunk contains one. (c) **Corner-set kill**: in
> an `exc = 1` tight chunk whose forced interiors are the hub `v` and
> the two ends of its in-chunk branches, the corner set attaches
> through only 2 darts, and (GR-25) at the corner set reads
> `2·2 + 1 < 7` — dead. Together: **a fully-hot hub with two
> triangle-type tight chunks is impossible** (the third chunk's
> interiors are forced, and (b)+(c) kill every non-triangle completion
> while (a) kills the triangle one).
>
> **(iii) The census (measured; exhaustive where stated).** Fully-hot
> hubs (all three darts exits of capacity-tight proper chunks): **0**
> on the exhaustive `n ≤ 6` stratum (all 4920 shapes — upgrading the
> 199-shape (GR-35)(iv) sample; 32 hubs at ≥ 2 hot darts); **0** at
> W3M/W3/W4/W5 (1/2/3/3 tight chunks each, no hub with even 2 hot
> darts); **0** at CL6/CL8/CL10, which carry **no capacity-tight chunk
> at all**; **0** at the Q3(2+2+2) and V8(two-spokes) CFLANK targets
> (also 0 tight chunks); **0** across a targeted digon-frame completion
> hunt — 10 984 completions on 4/6/8 hubs (caps disclosed: 60 000
> completions, 3000 matchings per frame, deterministic prefixes), 210
> in habitat.

**Adjudication.** No fully-hot hub is found anywhere reached, and the
all-circuit local types are **impossible by proof**. The adjudication
does **not** close the general impossibility: the k ≥ 2-bearing local
types (a tight chunk with corners, W3M-style, as one of the three) pass
the local arithmetic, and the hunt's habitat-gated family is small (210
shapes past the pool). The honest state: *impossible at the all-circuit
cells; open, unwitnessed, and arithmetically constrained elsewhere* —
together with the family correction (*Step G43*), the sharper successor
target is a **realized-binding** fully-hot hub, whose `n ≤ 6`
non-existence is now exhaustive (*Step G45*). A constructed seed would
still not be a flank (the spec's E1 clarification): every witness shape
carrying near-saturated hubs keeps abundant fully-good colourings.

---

### Step G47 — where this leaves the target and the (GR-15) line (hand-off)

- **The target — the orientation theorem at `Λ = ∅` `D = 0` — stays
  OPEN**: not proven (the selection principle lacks a uniform deviation
  bound and a corner-side charge for the W5 family), not refuted (no
  g-flank, no fully-hot seed; the laminarity of the binding family on
  the whole swept stratum is *positive* structure). Riders verbatim:
  the statement lives at **`Λ = ∅`**, **`D = 0`**, **modulo (GR-4′)**;
  the `Λ ≠ ∅` closed-form analogue stays **unswept**; the `D > 0` lift
  stays **unswept**; **none of this closes (GR-15)** — at best the
  target would close (GR-15) on this stratum modulo (GR-4′), and the
  target itself is open.
- **What is newly PROVEN**: (GR-36) (the structural charge: charge form,
  AA-independence, J path-forest, the two-block J-bound, exit-sharing
  exclusion), (GR-37) (the (c,m) model, the matching rule's exact
  cut-space obstruction — explaining (GR-34)(ii)'s parity limit — and
  deviation reachability), (GR-38)(i)–(ii) (the exact slack identity;
  the attachment lemma), (GR-39)(i)–(ii) (the tight-chunk structure
  theorem; the K4-saturation, digon, and corner-set kills). **What is
  newly SETTLED BY EXHAUSTION at `n ≤ 6`**: crossing same-block binding
  pairs do not exist (the kill vacuously-strong; binding laminarity);
  0 realized-binding fully-hot hubs; 0 capacity-tight fully-hot hubs
  (census upgraded from the 199-shape sample). **What is measured**: the
  good-PM selection at `d ≤ 2` (120/120 pool, W3M/W4/W5, ladders at
  `d = 0`), its **failure at W3** (`d ≤ 2` empty over all 8 matchings;
  fully-good minority maps at matching-distance 3/5/6), and the
  capable-vs-cap-7 family gap (2721 vs 252 exit darts; 761 vs 0
  fully-hot on the necessary-condition family).
- **The surviving route, in one sentence**: prove that every habitat
  shape has a fully-good colouring within a bounded number of deviations
  of some perfect matching — the parity/balance obstruction is exactly
  understood ((GR-37)), the constraint family is the binding-capable
  chunks with the (GR-36) charge bounding their reach, laminarity
  organizes the maximal binding family on the proven stratum, and W3 is
  the first shape any such proof must price (then the W5 family, whose
  charge — corner A-dart scarcity — is the one missing bound).
  Subsumed and still open underneath: uniform NC1-satisfiability itself
  ((GR-24)'s mixed-case universality, *Step G28* item 3) — the `k = 1`
  stratum of the same Hall problem.
- **For the route ledger** (`notes/Pencil-fanout-archive.md` §"Tenth
  direction"): entry 1 (the orientation theorem) lands as
  **open-with-named-dispatchable-attacks** — (a) the bounded-deviation
  selection theorem (anchor proven, bound open, W3 the named test), (b)
  the corner-side charge for corner-separated (W5-type) chunks, (c) the
  `n ≥ 8` AA-glue realizability question (the kill's only surviving
  general-`n` case), (d) the realized-binding fully-hot seed hunt at
  `n ≥ 8`. The intersection kill leaves the attack list (settled at
  `n ≤ 6`, vacuously strong); the hot-hub control is adjudicated
  NOT-FOUND with partial impossibility. Entries 2–4 (GR-4′; `Λ ≠ ∅`;
  `D > 0`) unchanged. **E1 does not fire** (no flank — nothing here even
  approaches one), **E2 does not fire** (entry 1 keeps four named
  dispatchable attacks), **E3 does not fire** (the target is not
  proven).
- The (K-res)/(GR-15) quantification question stays a coordinator
  hand-off note, untouched here (spec caution). Class uniformity of
  `hK` is untouched; **no gap-map status moves**.

---

### Verification (Steps G43–G47)

`notes/scripts/w4/gorient.py` (**new with this pass**, untracked;
imports `gexist.py` — `incidence` / `chunk_shape` / `defect_direct` /
`fully_good_rank` / `hub_minority` / `ladder_specs` /
`ladder_rule_first` — plus `gunif.py` (`WITNESSES`, `wit_colouring`,
`spec_to_hm_index`), `gcap.py` (`branch_stats`, `pool_specs`,
`two_ec_subsets`), `cflank.py` (`admissible`, `cubic_habitat`,
`hub_model`, `nc1_violations`), `gridcol.py` (`subdivide`), `closure.py`
(`colourings`), `kbare_common.verts_of`, all read-only; rank enters only
through `gexist.fully_good_rank`, i.e. `gridcol.block_generic_zero`'s
GF(p) lower bound with the exact-ℚ recheck through **both** matrices —
README §4 convention 2). Exact integers throughout; rngs seeded per
mode, seeds printed; no `set` printed; nothing samples a placement, so
`repin.star_generic` gates nothing (§(K-clos) (AC-9)). No pool is new:
the 4920-shape stratum is regenerated by `gcap.pool_specs` and asserted
`== 4920`; ladders and Q3/V8 are the CFLANK `--tight` recipes,
habitat-gated by the proven (GR-25) criterion per instance; the hunt is
a targeted, capped, disclosed completion family — no enumerator, no
blind sweep.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hall     #  ~4 s  (GR-36)/(GR-37): the charge at 338 364 pairs; t = [l even] at every PM; good-PM 120/120
PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --kill     # ~42 s  (GR-38): exhaustive n <= 6 -- 0 crossing binding pairs; identity at 58 495 pairs; realized-hot census
PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --hot      # ~17 s  (GR-39): structure theorem at 2400 tight chunks; kills; exhaustive + named-shape census; the hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --adv      #  ~3 s  W5 priced first; the family correction; good-PM at the witnesses; the W3 stick + distances
PYTHONHASHSEED=0 python3 notes/scripts/w4/gorient.py --validate # ~66 s  all four in one process (inside the 600 s budget; no F15 shape needed)
```

**Which driver mode tests which sentence (F11 — doubly binding: the
direction's claims are case-list / exhaustiveness claims).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-36)(i)/(iii) charge + J-bound | `--hall` | `defect_X ≥ w45 + Σ⌈m_i/2⌉` asserted at 338 364 (colouring, chunk) pairs, both blocks; evaluator vs `defect_direct` at 3324 |
| (GR-36)(ii) AA-independence | `--hall` | at 10 190 AA-adjacent interior pairs the joining branch asserted odd A-majority |
| (GR-36)(iii) path forest | `--hall` | per `k ≥ 2` chunk: every J-component asserted `edges = vertices − 1` |
| (GR-36)(iv) exit-sharing | `--hall` | asserted at every precomputed even shared-exit pair (0 occurrences on the subsample, disclosed) |
| (GR-37)(i) the (c,m) model | `--hall` | round trip colouring → (c,m) → colouring asserted equal at 230 colourings |
| (GR-37)(ii) t = [ℓ even] at every PM | `--hall` | the vector identity asserted branch-by-branch at 5409 (matching, branch) pairs; solvability = even-vector solvability at every matching |
| (GR-37)(ii) ladder corollary | `--hall` | CL5–CL8: rung-matching system solvable iff `m` even; at even `m` the two solutions asserted = the (GR-34)(ii) colouring and its swap |
| (GR-37)(iii) deviation reach + good-PM | `--hall` | constructive search: 120/120 subsampled shapes fully good (exact full-chunk scan) within ≤ 2 deviations, histogram 7/52/61 |
| (GR-38)(i) slack identity | `--kill` | asserted exactly at 58 495 crossing low-defect pairs (and at every binding pair — none exist) |
| (GR-38)(ii) attachment lemma | `--kill` | per crossing pair: every attachment at an interior, ≥ 2 per component, classification exhaustive (76 498 X + 72 676 (2,3)) |
| (GR-38)(iii) the stratum kill | `--kill` | EXHAUSTIVE: all 4920 shapes (asserted `== 4920`) × all 284 512 admissible colourings; 0 crossing same-block binding pairs among 53 740 binding instances; prefilter certified by full-scan cross-check at 566 colourings |
| realized-hot census | `--kill` | exits of every actually-binding chunk collected per shape; 506 hubs ≥ 2, **0** fully hot (exact at `n ≤ 6`) |
| (GR-39)(i) structure theorem | `--hot` | asserted at all 2400 proper cap-7 chunks of the pool (z, exc, chordless, exit weights, short exits at z = 2) |
| (GR-39)(ii) K4-saturation kill | `--hot` | all 4096 length tuples enumerated; 0 satisfy the three tightness equations + the excess law |
| (GR-39)(iii) census | `--hot` | exhaustive `n ≤ 6` (0 fully-hot, 32 at ≥ 2); named large shapes by `2^{n_hub}` boundary enumeration (cap-7 chunks are chordless, so `S = E(W)`); the hunt's caps printed |
| W5 priced first | `--adv` | `m_J = 0`, `w45 = 0`, bound = 0, `cap = 8` asserted — the charge's boundary and the census invisibility, in one place |
| the family correction | `--adv` | capable vs cap-7 exit darts (2721 vs 252), fully-hot (761 vs 0) on a 184-shape subsample |
| good-PM at the witnesses / the W3 stick | `--adv` | exhaustive over (matching, ≤ 2 deviations, both c-solutions) with screen; rank-certified successes at W3M/W4/W5 and CL6/CL8; W3: 0 candidates pass the screen; distance diagnostic 3/5/6 (W3) |
| the target, (GR-15), (GR-4′) as statements | — | **untouched and not driver-testable**: no mode probes them |

**Determinism.** `--validate` (all four modes, one process, ~66 s) is
**byte-identical across `PYTHONHASHSEED` 0 and 999**, including — as with
the `gunif` precedent — the wall-clock `[Ns]` annotations, which agreed
at these runtimes; a re-runner should still treat those lines as
inherently non-deterministic.

**Scratch probes (README's standing rule).** None retained: every figure
above is produced by a committed driver mode. (Three transient
debugging iterations during development — a vacuous first version of the
`--kill` identity certification, re-aimed at the low-defect family when
the binding-binding family measured empty; a first `--adv` witness search
that tested only the first admissible colouring per deviation set,
replaced by the exhaustive-with-screen form; and a 400-draw first cut of
the W5 distance diagnostic that under-sampled the ~0.5 % admissible rate,
re-run at 1200 draws — changed no mathematics; the final driver
re-derives everything.)

---

### Confidence verdict (Steps G43–G47)

| | claim | standing |
|---|---|---|
| **(GR-36)** | the structural charge: charge form, AA-independence, J path-forest, `defect_X ≥ w45 + Σ⌈m_i/2⌉` both blocks, exit-sharing exclusion | **proven-informally** (proofs above; asserted at 338 364 pairs) |
| **(GR-37)(i)–(ii)** | the (c,m) model; the matching rule's obstruction = the even-branch class in the cut space; the ladder-parity explanation | **proven-informally** (proofs above; the vector identity machine-asserted at every matching; CL5–CL8 corollary asserted) |
| **(GR-37)(iii)** | deviations reach every parity/balance class | **parity half proven-informally** (span argument); the "balance rider alike" clause is **statement-beyond-proof** (GADM *Step G53*: the argument moves only `GF(2)^E/Cut` classes, and balance is not a class function) — per-shape admissibility is fanout ledger **entry 5**, a separate open statement; the uniform *count* stays **open** — measured ≤ 2 on the pool, = 3 at W3 *(since GPSA Step G58: the parity half is FULLY proven — (GR-44) discharges the Hall/SDR accounting, with `d_par(M) = w_M` exact; the balance clause STAYS statement-beyond-proof)* |
| **(GR-38)(i)–(ii)** | the exact slack identity; the attachment lemma | **proven-informally** (per-hub cases; certified at 58 495 crossing pairs) |
| **(GR-38)(iii)** | crossing same-block binding pairs at `n ≤ 6` | **settled by exhaustion — they do not exist** (0 over the complete stratum); binding laminarity holds at every admissible colouring there; the AA-glue case at `n ≥ 8` **open** |
| **(GR-39)(i)** | the capacity-tight structure theorem | **proven-informally** (asserted at all 2400 pool instances) |
| **(GR-39)(ii)** | the K4-saturation / digon / corner-set kills; the (triangle, triangle, ⋆) cell closed | **proven-informally** (arithmetic; the K4 case machine-enumerated) |
| **(GR-39)(iii)** | fully-hot hubs: none | **exhaustive at `n ≤ 6`** (cap-7 and realized families both); **measured 0** at every named large shape and the capped hunt; general impossibility **open** past the killed cells |
| the good-PM selection | some PM + ≤ d deviations is fully good | **measured** (`d ≤ 2`: 120/120 pool, W3M/W4/W5, ladders `d = 0`; **fails at W3 for `d ≤ 2`**, `d = 3` sufficient there by a distance witness); no theorem claimed |
| **the GORIENT target** | the orientation theorem (uniform fully-good existence at `Λ = ∅` `D = 0`) | **OPEN** — not proven, not refuted; re-anchored on the selection principle with W3 the named test shape and the corner-side charge the named missing bound; never read without the riders |
| **(GR-15)** | | **OPEN — unchanged in both directions.** No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's, CFLANK's, GCAP's, GUNIF's and GEXIST's: everything above
is about colourings of fixed graphs and constructed configurations'
exact ranks, never about `PencilNondegFeasible G`; no σ-fixed witness is
read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G43–G47)

*(i)* **A uniform deviation bound** — a proof that every habitat shape
has a fully-good colouring within `d` deviations of some perfect
matching, for a shape-free `d`: that is the target in the (GR-37)
anchor, hence (GR-15) at `Λ = ∅` `D = 0` **modulo (GR-4′)**; W3 says
`d ≥ 3`, and the proof must price the corner-separated (W5) family,
whose charge (corner A-dart scarcity, (GR-29)(iii)) is the one bound
(GR-36) does not deliver. *(ii)* **The corner-side charge** — a
(GR-36)-style two-block lower bound on `defect` in terms of corner
count/A-dart supply for `m_J = 0` chunks: it would make the
binding-capable family finite per shape in a useful sense and is the
natural next theorem. *(iii)* **The AA-glue configuration at
`n ≥ 8`** — realizable, and the kill (hence binding laminarity) fails
beyond the swept stratum; unrealizable, and laminarity extends toward a
general uncrossing theorem. *(iv)* **A realized-binding fully-hot hub**
at `n ≥ 8` — the corrected seed; still not a flank by itself (E1's
clarification). *(v)* **(GR-4′)** — unchanged; any movement changes
what a fully-good colouring buys. *(vi)* The **`Λ ≠ ∅` / `D > 0`
analogues** — both strata stay unswept; (GR-37)'s algebra is
length-parity-only and should transfer, but nothing here shows it.

### Steps G48–G52 (2026-08-15, direction GDEV) — the bounded-deviation selection theorem is **REFUTED AS POSED** by an explicit habitat family with an unbounded **parity floor** (a proven, colouring-free lower bound on the deviation count of *every* admissible colouring from *every* perfect matching), the **corner-side charge lands** as the (GR-36)-analogue theorem for corner-separated chunks — tight at W3M, where (GR-36) prices 0 — the W3 stick is located in the **odd-branch balance layer** (not parity, not fully-goodness — *corrected by GADM Step G56: the stick SPLITS, one shift-metric unit + one balance unit*), and the deviation cost **measures as entirely an admissibility phenomenon** (`d_fg = d_adm` at every shape measured) — (GR-15) stays **OPEN**, per-shape (GR-15) gains rank-certified members up to `n_hub = 50`, and **no gap-map status moves**

Answering `notes/Pencil-fanout-archive.md` §"Eleventh direction — GDEV": the
bounded-deviation selection theorem — *every habitat shape (cubic `G°`,
`ℓ_β ∈ [2,5]` ((SD-6)), `Σ(ℓ_β − 2) = 6` ((GR-21)), the proven (GR-25)
cut criterion; `Λ = ∅`, `D = 0`) has a fully-good colouring within a
**shape-free** number `d` of deviations of some perfect matching of
`G°`* — the merged attacks (a)+(b), with (d) folded in as the
(b)-conditional control.  Read against *Steps G43–G47*
((GR-36)–(GR-39)), *Steps G38–G42* ((GR-32)–(GR-35)), *Steps G34–G37*
((GR-29)–(GR-31)), *Steps G24–G28* ((GR-21)–(GR-26)), and the *Shared
dictionary*'s (SD-6).

**Step 0 pin (mandatory, discharged before any derivation).**
**(GR-37)** in full — the (c, m) model, the matching rule's exact
cut-space obstruction (all-even reading: bipartite), and deviation
reachability *with its recorded caveat* (reachability is an
∃-finitely-many statement; the uniform count is the open half — W3
needs 3).  **(GR-36)** — the charge form
`defect_A = w45 + #{A-maj odd} + #{non-AA interiors}`, AA-independence,
the J path-forest bound `defect_X ≥ w45 + Σ⌈m_i/2⌉` in both blocks,
exit-sharing exclusion, and its honest boundary: the W5 family
(`m_J = w45 = 0`) is charged **nothing**; the binding-capable family
strictly contains the capacity-tight one.  **(GR-29)(iii)** — corners
eat A-darts; only [ℓ2] heads and A-ended cost-1 paths supply them — the
raw material of the charge below.  **(GR-38)'s exact scope** —
laminarity proven at `n_hub ≤ 6` ONLY.  **(GR-39)'s family-qualified
census** — 0 fully-hot on the **capacity-tight** and **realized**
families (exhaustive at `n ≤ 6`); the **binding-capable** family *does*
carry them (761 on GORIENT's 184-shape subsample); no unqualified zero
is quoted anywhere below.  **(GR-30)/(GR-34)** — W5 the structural
heart, CL10 the uncorrelated-mechanism killer; W3 priced FIRST below,
then the W5 family, then the ladders.  **(GR-4′)'s proven-case
boundary** — covers no habitat block; the riders below are genuinely
load-bearing.

**The closure chain, with the riders, stated before anything is
claimed.**  A proof of the target would have implied (GR-15) at
`Λ = ∅` `D = 0` **modulo (GR-4′)**; the target is refuted below *as
posed*, which moves **nothing** on that chain: (GR-15) is untouched in
both directions (the refuting family satisfies per-shape (GR-15),
certified), the **`Λ ≠ ∅` closed-form analogue stays unswept**, the
**`D > 0` lift stays unswept**, and **nothing here closes (GR-15)** —
nothing below claims to.

**Headline, stated before the mathematics.**

- **(GR-40), the corner charge (proven) — sub-deliverable (b) LANDS.**
  For every chunk, in **both** blocks,
  `defect_X(S) ≥ w45(S) + ⌈(z + odd_cc − m_J − (k−1))/2⌉`, where
  `odd_cc` counts the odd corner-corner S-branches.  Colouring-free
  consequence: a chunk binding in some block satisfies
  `z + odd_cc − m_J ≤ (k−1) + 4 − 2·w45` (**the corner condition**) —
  the corner-separated (`m_J = 0`) analogue of (GR-36)(iii)'s
  `m_J ≤ 4 − 2w45`.  **Tight at W3M** (bound 1 = its exact defect,
  where the (GR-36) bound is 0); the W5 scaling family sits at the
  bound's exact zero (`z = k−1`, `odd_cc = m_J = 0`) — charged nothing,
  *correctly*, since it binds; what the charge caps is how far above
  `z = k−1` a corner-separated binding chunk can climb.  Asserted at
  333 282 (colouring, chunk) pairs; it strictly beats (GR-36) at
  81 446 of them.  The naive **sum** of the two charges is **false**
  (816 violations measured) — `max` is the theorem.
- **(GR-41), the parity floor (proven).**  Let `τ = [ℓ even]` and
  `Φ = τ + Cut(G°)`.  Every admissible colouring's minority map has
  `μ(m) := Σ_v e_{m(v)} ∈ Φ` with `wt(μ) ≡ n_hub (mod 2)`, and — since
  `μ(M) = 0` for every perfect matching — its deviation distance from
  **every** perfect matching is `≥ wt(μ)/2 ≥ φ*/2`, where
  `φ* := min{wt(x) : x ∈ Φ, wt(x) ≡ n mod 2}` is a computable,
  colouring-free shape invariant.  Two lines from (GR-37).  The
  deviation count of the selection principle is thus bounded **below**,
  not only reachable.
- **(GR-42), the refutation (proven + machine-certified).**  The
  pentagon-necklace family `NK(m)` (m even): m pentagons ringed by
  links and chords, all lengths **even** (`ℓ ∈ {2,4}`, excess 6).
  (i) **Habitat**, by a new sufficiency lemma: cubic + 3-edge-connected
  + cyclically 4-edge-connected + star excess ≤ 5 ⟹ (GR-25)(i) —
  every clause polynomial-time per member, so membership certifies at
  any size.  (ii) `φ(NK(m)) ≥ m` — the m pentagons are edge-disjoint
  odd cycles, and at all-even lengths `Φ` is exactly the set of
  internal-edge indicators of bipartitions; `φ = φ* = m` **exactly**
  at `m ≡ 2 (mod 4)` (explicit weight-m witness).  (iii) Fully-good
  colourings **exist at every member** (rank-certified, both blocks,
  both matrices — per-shape (GR-15) at `n_hub` up to **50**, the
  largest instances certified in the arc), so **nothing here is a
  flank**.  By (GR-41): `d(NK(6)) ≥ 3`, `d(NK(8)) ≥ 4`,
  `d(NK(10)) ≥ 5`, unbounded along the family — **there is no
  shape-free deviation bound.  The bounded-deviation selection theorem
  is REFUTED as posed** (a FORM-refutation, exactly the eleventh
  spec's E1 clause (iii); per-shape existence is untouched and
  positively certified).
- **The W3 stick, located (measured).**  `φ*(W3) = 2`, floor 1 — so
  parity does **not** explain W3.  Re-derived exhaustively at the
  admissible level (all 8 matchings × ≤ 2 deviations, 1608 minority
  maps): **12 are parity-consistent, and every one of their
  c-solutions fails the odd-branch BALANCE rider**; 0 admissible.  The
  W3 stick lives in the **balance layer**.  A fully-good colouring
  exists at `d = 3` (rank-certified), so `d_adm(W3) = d_fg(W3) = 3`.
  *(Corrected by GADM, Step G56: `d_par(W3) = 2` exactly, so the stick
  **splits** — one shift-metric unit above the floor plus one balance
  unit above `d_par`; "lives in the balance layer" overstated the
  balance share.)*
- **The layer decomposition of the deviation cost (measured).**  On a
  131-shape seeded pool subsample, with `d_par ≤ d_adm ≤ d_fg` the
  least deviation counts at which some (matching, deviations) map is
  parity-consistent / extends to an admissible colouring / to a
  fully-good one (exact full-chunk scan): `d_par − ⌈φ*/2⌉ ∈ {0: 89,
  1: 42}`, `d_adm − d_par ∈ {0: 130, 2: 1}`, and
  **`d_fg − d_adm = 0 at 131 of 131`** — with W3 (`= 3 = d_adm`) and
  NK(2) (`= 2 = d_adm`) agreeing.  Everywhere measured, **the
  deviation cost of the selection is entirely about reaching
  admissibility — the fully-good layer is free.**  Measured, not
  proven; recorded as the sharpest successor target.
- **What does NOT move.**  (GR-15) stays OPEN, unchanged in both
  directions; no g-flank (the refutation family's members all carry
  certified fully-good colourings); no fully-hot seed found by the
  (b)-armed hunt; (GR-4′)/(GR-10) untouched; **no gap-map status
  moves**.  The uniform fully-good **existence** target (GEXIST's
  form) also stays open — only its bounded-deviation *strengthening*
  dies.

**Notation (on top of *Steps G43–G47*).**  For a chunk `S`:
**corners** = its degree-3-in-S hubs (there are exactly `2(k−1)` of
them, `k = |S| − |W_S| + 1`); a branch of `S` is **cc / ci / ii** as
its ends lie at two corners / a corner and an interior / two interiors
(`#ii = m_J`, `#ci = 2z − 2m_J`, `#cc = 3(k−1) − z + m_J`);
`odd_cc(S)` = the number of odd cc branches.  `τ = [ℓ even]`,
`μ(m)_β = #{ends of β carrying a minority dart} mod 2`,
`Φ = τ + Cut(G°)`, `φ* = min` parity-matched coset weight.  A
**deviation** and dist(m, M) as in *Steps G43–G47*.

---

### Step G48 — (GR-40): the corner charge — binding costs interiors-in-excess-of-corners, in both blocks

> **(GR-40)** *(proven; asserted in both blocks at 333 282 (colouring,
> chunk) pairs over every admissible colouring of a 123-shape seeded
> pool subsample, on top of the (GR-36) bound, with the supply case
> list certified exhaustively and the two counting identities asserted
> per chunk, `--charge`)*  Let `S` be a connected branch subset with
> all S-degrees in {2, 3} of a habitat shape, at an admissible
> colouring.  Then, in **both** blocks,
> > `defect_X(S) ≥ w45(S) + ⌈(z(S) + odd_cc(S) − m_J(S) − (k−1))/2⌉`.
>
> In particular a chunk **binding** in some block satisfies the
> colouring-free **corner condition**
> > `z + odd_cc − m_J ≤ (k−1) + 4 − 2·w45(S)`,
>
> the corner-separated analogue of (GR-36)(iii)'s `m_J ≤ 4 − 2w45`;
> at `m_J = 0` it reads `z + odd_cc ≤ k + 3 − 2w45`.

*Proof.*  Count the A-darts of `S` at corners, `α_A`.  **Demand:** a
corner has all three of its `G°`-darts in `S`, so the mono-hub ban
gives it at least one A-dart: `α_A ≥ 2(k−1)`.  **Supply**, by the
alternation table (the case list `--charge` certifies: an even
branch's end darts differ, an odd branch's end darts both carry its
majority): an even cc branch contributes exactly 1; an odd cc branch
contributes `2·[A-majority]`; an even ci branch contributes 1 exactly
when its interior end is B — i.e. only non-AA interiors supply,
at most `n_AB + 2n_BB` in total; an odd ci branch contributes
`[A-majority]`; ii branches contribute 0.  With
`#cc = 3(k−1) − z + m_J` and `a_odd` = the A-majority odd branches of
`S`,
`2(k−1) ≤ (3(k−1) − z + m_J − odd_cc) + 2a_odd + n_AB + 2n_BB`, so
`z + odd_cc − m_J − (k−1) ≤ 2a_odd + n_AB + 2n_BB
≤ 2(a_odd + n_AB + n_BB) = 2(defect_A(S) − w45(S))` by (GR-36)(i).
Integrality gives the ceiling; the B-block bound is the mirror.  The
corner count `2(k−1)` and the cc count are the degree identities
`2|S| = 3·#corners + 2z`, `#ci = 2z − 2m_J`.  (At `k = 1` the bound
degenerates to `defect ≥ w45`, true by (GR-36)(i).)  ∎

**Why this is the charge (b) asked for, and its exact boundary.**
*Step G47*(ii) asked for a (GR-36)-style two-block lower bound on
`defect` in terms of corner count / A-dart supply for `m_J = 0`
chunks.  (GR-40) is that bound, run through (GR-29)(iii)'s mechanism
(corners eat A-darts; AA interiors starve the corner supply through
even branches, and every odd or non-AA supplier is already a (GR-36)
defect unit).  It is **tight at W3M**: `S_{W3M}` has `z = 3, k = 3,
m_J = 0, odd_cc = 1, w45 = 0`, corner bound `1 = defect_A` exactly,
where the (GR-36) bound is 0 — the pinned counter-fact.  Its honest
boundary is the same as (GR-36)'s, now *explained*: the W5 scaling
family has `z = k − 1` and `odd_cc = m_J = 0`, the exact zero of the
bound — it binds, so no correct charge can price it; what (GR-40)
proves is that a corner-separated binding-capable chunk can have at
most **4 more interiors than the W5 family's `z = k−1`** (per unit of
`w45`, two fewer).  On the pool the charge strictly beats (GR-36) at
81 446 of 333 282 pairs and is attained with equality at 1102.  The
naive **sum** of the two charges is refuted (816 measured violations):
the two bounds double-count the non-AA interiors, and `max` is the
theorem.

**The family recount (what (b) buys the hunt).**  On a fresh 182-shape
seeded pool subsample (`--charge`; a different subsample from
GORIENT's 184-shape one, same families): binding-capable exit darts
under (GR-36) alone 2855, under (GR-36) ∧ the corner condition
**2530**; hubs with ≥ 2 capable-hot darts 978 → 897; **fully
capable-hot hubs 815 → 573** (all figures on the necessary-condition
**binding-capable** family; the realized and capacity-tight zeros of
(GR-38)/(GR-39) are a different, smaller family and stay as recorded).
The corner condition prunes ≈ 30 % of the fully-capable-hot hubs a
Hall argument would have to feed.

---

### Step G49 — (GR-41): the parity floor — the deviation count is bounded below by a coset weight, and the W3 stick is the balance layer's *(corrected by GADM Step G56: the stick splits 1 shift-metric + 1 balance unit)*

> **(GR-41)** *(proven; certified per colouring at 373 admissible
> colourings of the pool subsample — coset membership through a
> fundamental-cycle basis, weight parity, `φ*` minimality — and the
> distance bound at 1924 (colouring, matching) pairs, `--bound`)*
> Let `τ = [ℓ even] ∈ GF(2)^{E(G°)}` and `Φ = τ + Cut(G°)`.
>
> **(i)**  For every admissible colouring with minority map `m`,
> `μ(m) ∈ Φ`, and `wt(μ(m)) ≡ n_hub (mod 2)`.
>
> **(ii)**  For every perfect matching `M`, `μ(M) = 0`, hence
> > `dist(m, M) ≥ wt(μ(m))/2 ≥ φ*/2`,
>
> with `φ* = min{wt(x) : x ∈ Φ, wt ≡ n mod 2}`.
>
> **(iii)**  Hence **no admissible — a fortiori no fully-good —
> colouring exists within `⌈φ*/2⌉ − 1` deviations of any perfect
> matching.**  `φ*` is colouring-free and computable (`2^{n_hub}`
> coset enumeration).

*Proof.*  (i): admissibility means the (GR-37)(i) system is solvable
for `c`, i.e. `t(m) = τ + μ(m) ∈ Cut(G°)`; the weight parity is
`Σ_β μ_β ≡ Σ_v 1 = n`.  (ii): a matching branch receives both its
ends' minority darts and a non-matching branch neither ((GR-37)(ii)'s
cancellation), so `μ(M) = 0`; `μ(m) = Σ_{deviating v}(e_{m(v)} +
e_{M(v)})` has weight `≤ 2·dist`.  (iii) is (i) + (ii).  ∎

**W3, priced FIRST — and the honest surprise.**  `φ(W3) = φ*(W3) =
2`: **the parity floor does NOT explain the W3 stick** (it predicts
only `d ≥ 1`).  The stick is re-derived and *layered* exhaustively
(`--bound`): of the 1608 minority maps within 2 deviations of W3's 8
perfect matchings, **12 are parity-consistent — and all of their
c-solutions fail the odd-branch balance rider**; none reaches an
admissible colouring.  So the balance rider is what kills every
parity-consistent map at `d ≤ 2`.  A fully-good colouring is exhibited
at `d = 3` (rank-certified, both blocks, both matrices; 1 rank test),
so `d_par(W3) ≤ 2 < d_adm(W3) = d_fg(W3) = 3`.  *(Corrected by GADM,
Step G56: `d_par(W3) = 2` **exactly** — no parity-consistent map
exists at `d = 1` — so the stick **splits**: one shift-metric unit
above the floor (`d_par − ⌈φ*/2⌉ = 1`) plus one balance unit
(`d_adm − d_par = 1`).  "The stick is the balance layer's" and "W3
costs 2 in the balance layer" were both wrong readings of the same
data — GDEV's own recorded `d_par ≤ 2 < d_adm = 3` already forced a
balance share ≤ 1.)*  Witness consistency:
`φ* = 2` at W3M/W4/W5 (floor 1 ≤ the measured `d = 2`); ladders:
`φ(CL_m) = 0` at even `m` (bipartite — the rung rule's freeness) and
`2` at odd `m` (the parity floor restates (GR-37)(ii)'s parity limit
as a *quantified* obstruction: one deviation deep at least).

**The pool layer split (measured — the growth-law data).**  On a
131-shape seeded subsample, exact over all matchings and deviations
≤ 3 (full-chunk fully-good scan):

| layer gap | histogram |
|---|---|
| `⌈φ*/2⌉` (the floor) | `0: 16`, `1: 115` |
| `d_par − ⌈φ*/2⌉` (shift-metric looseness) | `0: 89`, `1: 42` |
| `d_adm − d_par` (balance) | `0: 130`, `2: 1` |
| `d_fg − d_adm` (fully-goodness) | **`0: 131`** |

Three separate findings, all measured: the floor's Hamming relaxation
is loose by ≤ 1 on the pool (the exact parity layer is a *shift
metric*: adjacent-pair moves, one per hub — NK(2) below shows the gap
is real, `d_par = 2` against floor 1); the balance layer costs 0 or 2
on this subsample (the `2` is a pool-resident W3-precursor; W3 itself
costs **1** there — `d_par(W3) = 2`, `d_adm = 3`, corrected by GADM
*Step G56*, so the balance gaps measured across everything probed are
`{0, 1, 2}`);
and **fully-goodness never costs a deviation beyond admissibility —
anywhere measured** (131 pool shapes + W3 + NK(2)).  The deviation
question is, empirically, an admissibility question about `(G°, ℓ)`
alone — parity + shift metric + balance — with the binding-chunk layer
free.  Measured, not proven; the sharpest successor target below.

---

### Step G50 — (GR-42): the refutation — a habitat family with unbounded parity floor; no shape-free deviation bound exists

> **(GR-42)** *(the lemma and the packing bound proven; every clause
> machine-certified per member, `--adv`)*  For even `m ≥ 2` let
> `NK(m)` be the **pentagon necklace**: pentagons `P_0..P_{m−1}` on
> hubs `v_{i,0..4}` (edges `(v_{i,j}, v_{i,j+1 mod 5})`), links
> `v_{i,0}–v_{i+1,2}` and `v_{i,1}–v_{i+1,3}` (indices mod m), chords
> `v_{i,4}–v_{i+m/2,4}` (`i < m/2`); all lengths 2 except three
> length-4 branches (on three chords for `m ≥ 6`; chord + two links at
> `m = 2`) — all lengths **even**, excess 6.  Then:
>
> **(i) Habitat.**  *Lemma:* a cubic loop-free multigraph with
> `ℓ ∈ [2,5]`, `Σ(ℓ−2) = 6`, every hub star of excess ≤ 5,
> 3-edge-connected and **cyclically 4-edge-connected** satisfies
> (GR-25)(i).  *(Proof: a legal `W′` with `∂ ≥ 4` is free; 3-edge-
> connectivity forces `∂ ≥ 3` and makes the complement connected — its
> components' boundaries partition ≤ 3 darts with ≥ 3 each; at
> `∂ = 3`, both sides of size ≥ 2 have `(3q−3)/2` induced branches,
> forcing `q` odd, `q ≥ 3`, and a cycle on each side — dead by cyclic
> 4-edge-connectivity; the one survivor is the complement of a
> singleton, where `exc(E(W′)) = 6 − exc(star) ≥ 1` gives
> `2·3 + 1 = 7`.)*  Every hypothesis is polynomial-time per member,
> and each `NK(m)` (m = 2, 6, 8, 10 run) passes all of them.
>
> **(ii) The floor grows.**  At all-even lengths, `Φ` is exactly the
> set of internal-edge indicators of bipartitions of `G°`, and every
> element hits every odd cycle; the `m` pentagons are edge-disjoint
> odd cycles, so `φ(NK(m)) ≥ m`.  At `m ≡ 2 (mod 4)` the set
> `F = {(v_{i,3}, v_{i,4})}` is itself a `Φ`-element of weight `m`
> (deleting it leaves the necklace bipartite with `F` internal), so
> `φ = φ* = m` **exactly**.
>
> **(iii) Not a flank.**  Every member run carries a rank-certified
> fully-good colouring (exact rational `dim Z = 0`, both blocks, both
> matrices — per-shape (GR-15), at `n_hub = 10, 30, 40, 50`),
> constructed through explicit `μ(m) = χ_F` pointer/pairing
> realizations of the coset element.
>
> **Corollary (the refutation).**  By (GR-41),
> `d(NK(m)) ≥ m/2`: `d(NK(6)) ≥ 3`, `d(NK(8)) ≥ 4` *(the constructed
> `d ≥ 4` witness the spec's MISS deliverable (2) names)*,
> `d(NK(10)) ≥ 5`, unbounded along the family.  **The
> bounded-deviation selection theorem is FALSE as posed: there is no
> shape-free `d`.**  This is a FORM-refutation (E1 clause (iii)) —
> fully-good existence per shape holds at every member, certified.

**Certification (each clause a machine check, `--adv`).**  The lemma
checker carries an **F13 adversarial witness**: the all-ℓ2 triangular
prism with matching excess is REJECTED for exactly its cyclic 3-cut,
having passed cubic + 3-edge-connectivity + star-excess (the pinned
counter-fact isolating the load-bearing clause), and the exhaustive
(GR-25) oracle agrees; a sufficiency control on the pool finds 27/27
lemma-true shapes confirmed habitat by `cflank.cubic_habitat` with 0
disagreements, and NK(2) is confirmed by the exhaustive `2^{10}`
oracle directly.  The pentagon packing (edge-disjointness, 5-cycles)
and the `F`-bipartization (2-colouring found, every `F`-edge internal)
are asserted per member; `φ = φ* = m` is additionally confirmed by
exact `2^n` coset enumeration at `n ≤ 20` (NK(2): `φ = 2`).  NK(2) is
priced exactly: all-M inconsistent at **every** one of its 8 perfect
matchings (`d = 0` empty, as the floor demands), and
`d_par = d_adm = d_fg = 2` against floor 1 — the floor is a floor, not
the whole parity layer.  At `m ≡ 0 (mod 4)` (NK(8)) the exact `φ` is
open inside `[m, m + m/2]` (the coset upper bound `F ∪ chords`); the
refutation only consumes `φ ≥ m`.

**What the refutation does and does not kill.**  Dead: attack (a) as
posed — any anchor-plus-shape-free-deviation selection over perfect
matchings, and with it the specific sharpened conjecture of *Step
G44*.  Alive and explicitly untouched: uniform fully-good
**existence** (GEXIST's target — `NK(m)` members all satisfy it);
per-shape (GR-15); the (GR-37) anchor itself, whose obstruction
analysis is exactly what powers the floor; and the **repaired
quantitative form** the data suggests — bound the deviation count by
the shape's own parity/balance invariants,
`d(shape) ≤ d_adm(shape)` with `d_adm − ⌈φ*/2⌉ ≤ 3` everywhere
measured — the growth-law question of *Step G52*.

---

### Step G51 — the (b)-armed control: the corner-condition-guided seed hunt finds nothing

With (GR-40) landed, the spec's re-arm condition holds, and ONE
targeted, capped, ledger-guided construction hunt was run (`--hunt`;
GUNIF's idiom, no enumerator, no blind sweep): central-hub frames on
8–10 hubs (hub `0` with three darts into randomized habitat
completions, 40 000 frames tried — cap disclosed and reached — 3526
in habitat by the exhaustive (GR-25) oracle), **armed** exactly when
all three central darts are exits of chunks passing **both** charges
((GR-36) J-bound ≤ 2 ∧ the (GR-40) corner condition; 600 armed
candidates scanned, cap disclosed), then scanned **exactly** over
every admissible colouring for a realized-binding fully-hot hub.
**NOT FOUND**: no armed candidate realizes binding chunks at all three
central darts at any admissible colouring — consistent with (GR-38)'s
exhaustive `n ≤ 6` zero and (GR-39)'s kills, now with the (b)-pruned
family (≈ 30 % smaller, *Step G48*) locating where a successor hunts.
A found seed would have been a SEED, not a flank (E1 clause (i)).

---

### Step G52 — where this leaves the target and the (GR-15) line (hand-off)

- **The target — the bounded-deviation selection theorem — is REFUTED
  AS POSED** ((GR-42)): no shape-free `d` exists.  The refutation is a
  **form**-refutation with a successor named (below), never a flank:
  every refuting member carries a certified fully-good colouring.
  Riders verbatim: everything lives at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**, and none of it moves
  (GR-15) in either direction.
- **What is newly PROVEN**: (GR-40) (the corner charge and the corner
  condition — sub-deliverable (b), a standalone (GR-36)-analogue
  theorem, tight at W3M); (GR-41) (the parity floor — deviations are
  bounded below by the coset invariant `φ*`); (GR-42)'s lemma (cyclic
  4-edge-connectivity ⟹ (GR-25)(i)) and packing bound
  (`φ(NK(m)) ≥ m`), hence the refutation.  **What is newly MEASURED**:
  the three-layer split of the deviation cost (parity / balance /
  fully-good) with **`d_fg = d_adm` at every one of 133 shapes
  measured** — the fully-good layer is free, everywhere probed; the W3
  stick located above the parity floor (12 parity-consistent maps at
  `d ≤ 2`, all balance-killed; GADM *Step G56* later splits it exactly:
  1 shift-metric + 1 balance unit); the (b)-recount of the
  binding-capable family (fully-capable-hot hubs 815 → 573 on a fresh
  182-shape subsample).
- **The surviving route, in one sentence**: the deviation question
  decouples from the binding-chunk question — everywhere measured, a
  fully-good colouring exists at the *admissibility*-minimal deviation
  count, so the repaired target is a **growth law**
  `d_fg(shape) = d_adm(shape) ≤ ⌈φ*/2⌉ + c_shift + c_balance` with the
  parity term proven exact-from-below and the two measured layers
  bounded (≤ 1 and ≤ 2 on everything probed) — prove the
  `d_fg = d_adm` half (fully-goodness free once admissible) and the
  existence target of GEXIST follows from per-shape admissibility,
  with the deviation language stripped of its false uniformity.
- **For the route ledger** (`notes/Pencil-fanout-archive.md` §"Eleventh
  direction"): entry 1 (the orientation theorem in its re-anchored
  bounded-deviation form) — the bounded-deviation FORM is **refuted**
  ((GR-42)); the entry re-anchors as
  **open-with-named-dispatchable-attacks**: (a′) the `d_fg = d_adm`
  law (fully-goodness free at the admissibility optimum — the sharpest
  measured regularity, 133/133); (b′) the balance-layer bound (prove
  `d_adm − d_par ≤ 2`, or characterize the W3-type balance sticks);
  (c) AA-glue realizability at `n_hub ≥ 8` (unchanged); (d′) the
  corner-armed seed hunt beyond the 600-candidate cap (Step G51's
  family).  Entries 2–4 ((GR-4′); `Λ ≠ ∅`; `D > 0`) unchanged.
  **E1 does not fire** (no flank; a deviation blowup is E1(iii)'s
  named non-event, and the members are certified fully-good).  **E2
  does not fire**: the theorem is refuted-as-posed **with successors
  named** — the growth-law re-anchoring above — which is E2's explicit
  carve-out.  **E3 does not fire** (nothing is proven that closes the
  target).  Per the spec's otherwise-clause, a constructed `d ≥ 4`
  witness routes the twelfth to **the growth-law question at the
  necklace family**.
- The (K-res)/(GR-15) quantification question stays a coordinator
  hand-off note, untouched here (spec caution).  Class uniformity of
  `hK` is untouched; **no gap-map status moves**.

---

### Verification (Steps G48–G52)

`notes/scripts/w4/gdev.py` (**new with this pass**, untracked; imports
`gorient.py` — `jdata` / `chunk_fast` / `fast_defects` / `darts_at` /
`cm_solve` / `cm_colouring` / `odd_balance` / `perfect_matchings` /
`m_of_matching` / `prep_shape` / `fully_good_scan` — plus `gexist.py`
(`incidence`, `chunk_shape`, `fully_good_rank`, `hub_minority`,
`ladder_specs`), `gunif.py` (`WITNESSES`, `spec_to_hm_index`,
`wit_colouring`), `gcap.py` (`branch_stats`, `pool_specs`),
`cflank.py` (`admissible`, `cubic_habitat`, `hub_model`), `gridcol.py`
(`branch_decomp`, `subdivide`), `closure.colourings`,
`kbare_common.verts_of`, all read-only; rank enters only through
`gexist.fully_good_rank`, i.e. `gridcol.block_generic_zero`'s GF(p)
lower bound with the exact-ℚ recheck through **both** matrices —
README §4 convention 2).  Exact integers throughout; rngs seeded per
mode, seeds printed; no `set` printed; nothing samples a placement, so
`repin.star_generic` gates nothing (§(K-clos) (AC-9)).  No pool is
new: the pool legs subsample `gcap.pool_specs` behind the
`cflank.cubic_habitat` gate; NK and the hunt frames are targeted,
capped, disclosed constructions (no enumerator, no blind sweep).  One
local device replaces a hot import: `light_hm` builds the
(hubs/branches/ends/lens) sub-dict of `cflank.hub_model` without its
simple-cycle enumeration, which is exponential in the cyclomatic
number and prohibitive at NK(8)+ (`hub_model` itself is unchanged and
still used everywhere it terminates).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --charge   #  ~6 s  (GR-40): case list; 333 282 pair-asserts; W3M/W5 pins; the family recount
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --bound    #  ~3 s  (GR-41): W3 layered; witnesses + ladders; the pool layer split; per-colouring certification
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --adv      #  ~5 s  (GR-42): the F13 prism; the lemma control; NK(2)/NK(6)/NK(8)/NK(10) certified; the refutation
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --hunt     # ~24 s  the (b)-armed hunt: 40 000 frames, 3526 gated, 600 armed + scanned, none fully-hot
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdev.py --validate # ~40 s  all four in one process (inside the 600 s budget; no F15 shape needed)
```

**Which driver mode tests which sentence (F11 — doubly binding: the
direction's claims are case-list / exhaustiveness claims).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-40) supply case list | `--charge` | all 8 (length, bit) branch cases enumerated: even ⟹ end darts differ (one A-end), odd ⟹ equal = majority |
| (GR-40) counting identities | `--charge` | `#corners = 2(k−1)` and `#cc = 3(k−1) − z + m_J` asserted at every chunk of the subsample (and at every chunk `--hunt` arms) |
| (GR-40) the bound, both blocks | `--charge` | `defect_X ≥` corner bound asserted at 333 282 (colouring, chunk) pairs over every admissible colouring of 123 pool shapes |
| (GR-40) beats (GR-36) / equality / sum-form | `--charge` | strictly-greater count 81 446; equality count 1102; sum-form violations 816 (measured, printed, NOT claimed) |
| (GR-40) tight at W3M; W5 at the zero | `--charge` | W3M: corner bound 1 = witness `defect_A`, (GR-36) bound 0 asserted; W5: `z = k−1`, both bounds 0 asserted |
| the (b) recount | `--charge` | 182-shape fresh subsample: capable exits 2855 → 2530, fully-capable-hot 815 → 573 (binding-capable family, qualified) |
| (GR-41)(i) coset membership + parity | `--bound` | asserted at 373 admissible colourings via a fundamental-cycle basis; `wt ≡ n (mod 2)`; `wt ≥ φ*` |
| (GR-41)(ii) the distance bound | `--bound` | `2·dist ≥ wt(μ)` asserted at 1924 (colouring, matching) pairs, every matching of each sampled shape |
| the W3 stick, layered | `--bound` | exhaustive: 8 matchings × ≤ 2 deviations = 1608 maps; 12 parity-consistent, 0 balance-passing, 0 admissible (asserted 0) |
| W3 at `d = 3` | `--bound` | fully-good rank certificate (both blocks, both matrices) at an explicit 3-deviation selection; rank cap 40 disclosed |
| the pool layer split | `--bound` | exact `d_par/d_adm/d_fg` over ALL matchings × deviations ≤ 3 with full-chunk scans at 131 shapes; `d_par ≥ ⌈φ*/2⌉` asserted per shape |
| (GR-42)(i) the habitat lemma | `--adv` | per member: 3-edge-connectivity (all ≤ 2-subsets), cyclic 4-edge-connectivity (all 3-subsets), star excess, cubic, excess law — each machine-checked; F13 prism REJECTED for exactly its cyclic 3-cut; 27/27 pool sufficiency control; NK(2) confirmed by the exhaustive `2^{10}` oracle |
| (GR-42)(ii) `φ ≥ m` / `φ = m` | `--adv` | pentagons asserted edge-disjoint 5-cycles per member; `F`-bipartization 2-colouring found with every `F`-edge internal; exact coset enumeration agreement at `n ≤ 20` |
| (GR-42)(iii) not a flank | `--adv` | per member: constructed colouring asserted admissible; fully-good RANK-certified (caps disclosed: ≤ 30 realizations; 1/15/1/1 tests used) |
| NK(2) exact pricing | `--adv` | all-M inconsistent asserted at every one of 8 matchings; exact `d_par = d_adm = d_fg = 2` |
| the (b)-armed hunt | `--hunt` | 40 000 frames (cap disclosed, reached), 3526 habitat-gated, 600 armed + exactly colouring-scanned (cap disclosed); fully-hot NOT FOUND, asserted per candidate |
| the target / (GR-15) / (GR-4′) as statements | — | (GR-42) refutes the target's FORM; (GR-15)/(GR-4′) untouched and not driver-testable |

**Determinism.**  `--validate` (all four modes, one process, ~40 s) is
**byte-identical across `PYTHONHASHSEED` 0 and 999**, including — as
with the `gunif`/`gorient` precedents — the wall-clock `[Ns]`
annotations, which agreed at these runtimes; a re-runner should still
treat those lines as inherently non-deterministic.

**Scratch probes (README's standing rule).**  None retained: every
figure above is produced by a committed driver mode.  (Three transient
debugging iterations during development — an early `--bound` print
that hard-coded the *expected* "W3 = parity" reading before the
measurement said otherwise, replaced by the computed layer report; a
first NK member loop through `cflank.hub_model`, which does not
terminate at NK(8) because of its simple-cycle enumeration, replaced
by the `light_hm` device; and a first 120-candidate hunt cap, raised
to 600 — changed no mathematics; the final driver re-derives
everything.)

---

### Confidence verdict (Steps G48–G52)

| | claim | standing |
|---|---|---|
| **(GR-40)** | the corner charge, both blocks; the corner condition | **proven-informally** (proof above; asserted at 333 282 pairs; tight at W3M) |
| **(GR-41)** | the parity floor: `dist ≥ wt(μ)/2 ≥ φ*/2` against every PM | **proven-informally** (two lines from (GR-37); machine-certified per colouring and per matching) |
| **(GR-42)(i)** | the cyclic-4-ec habitat lemma; NK(m) in habitat | **proven-informally** (proof above; every clause machine-checked per member; F13 witness + exhaustive cross-checks at `n ≤ 10` and 27/27 pool control) |
| **(GR-42)(ii)** | `φ(NK(m)) ≥ m`; `= m` at `m ≡ 2 (mod 4)` | **proven-informally** (odd-cycle packing + explicit coset witness; exact at `n ≤ 20` by enumeration) |
| **(GR-42)(iii)** | fully-good existence at NK members | **certified per member run** (rank grade, `m = 2, 6, 8, 10`, i.e. `n_hub ≤ 50`); the all-`m` statement is **measured-shaped, open** (no per-member obstacle known) |
| **the refutation** | no shape-free deviation bound exists | **REFUTED as posed** — follows from (GR-41) + (GR-42)(i)(ii) alone (proven), with (iii) certifying the members are not flanks |
| the layer split | `d_fg = d_adm`; balance gap ≤ 2; shift gap ≤ 1 | **measured** (131-shape subsample + W3 + NK(2); no theorem claimed) |
| the W3 stick | lives in the balance layer | **corrected by GADM (*Step G56*)**: the 12/0/0 layer counts (all 1608 maps) stand, but `d_par(W3) = 2` exactly, so the stick SPLITS — 1 shift-metric + 1 balance unit |
| the (b) recount | fully-capable-hot 815 → 573 | **measured** (fresh 182-shape subsample; binding-capable = necessary-condition family, qualified) |
| the hunt | no realized fully-hot seed among armed candidates | **measured** (caps disclosed; not an impossibility claim) |
| **the GDEV target** | the bounded-deviation selection theorem | **REFUTED AS POSED**; successor named (the growth-law / `d_fg = d_adm` re-anchoring); never read without the riders |
| **(GR-15)** | | **OPEN — unchanged in both directions.**  No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.**  The
same side as TCOL's through GORIENT's: everything above is about
colourings of fixed graphs and constructed configurations' exact
ranks, never about `PencilNondegFeasible G`; no σ-fixed witness is
read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G48–G52)

*(i)* **The `d_fg = d_adm` law proven** — fully-goodness free at the
admissibility optimum: with it, uniform existence reduces to per-shape
admissibility (a `(G°, ℓ)`-level parity/balance statement), and the
deviation language disappears from the critical path.  *(ii)* **A
balance-layer theorem** — prove `d_adm − d_par ≤ 2`, or exhibit a
family where the balance gap grows (that would deepen the refutation
into the balance layer and re-rank the successors).  *(iii)* **A
shape with `d_fg > d_adm`** — would kill the measured law and put the
binding-chunk layer back on the critical path; none exists among the
133 shapes measured.  *(iv)* **A fully-good colouring of some `NK(m)`
within `< m/2` deviations of a perfect matching** — impossible by
(GR-41) unless its proof is wrong; exhibiting one refutes this pass.
*(v)* **A realized-binding fully-hot hub** from the corner-armed
family past this pass's caps — a SEED for the CSP test, not a flank.


---

### Steps G53–G57 (2026-08-17, direction GADM) — experiment 1 lands OUTCOME 3 with `d_par` above the floor: the **shift-metric layer is UNBOUNDED** ((GR-43), the odd-cycle-packing floor `d ≥ m` at the necklaces, proven — so the growth law's bounded-correction reading dies), while the **`d_fg = d_adm` law (a′) SURVIVES its first large-`d` test** — `d_par = d_adm = d_fg = m` **exactly**, rank-certified at the optimum, at all four NK members up to `n_hub = 50`; ledger **entry 5 settles as a SEPARATE OPEN STATEMENT** ((GR-37)(iii)'s recorded proof covers only the cut-space class — its statement's "balance rider alike" clause is undelivered); the balance layer measures `≤ 2` everywhere probed including the odd-richest stratum, with a record correction: **W3's balance gap is 1, not 2** — (GR-15) stays **OPEN**, no gap-map status moves

Answering `notes/Pencil-fanout-archive.md` §"Twelfth direction — GADM": attack
**(a′)** the `d_fg = d_adm` law (primary) and **(b′)** the balance-layer
bound (secondary), tested first at the pentagon necklaces `NK(m)` of
(GR-42) — the only known large-`d` regime, where the 133/133 figure (131
seeded pool subsample + W3 + NK(2), all at `d ≤ 3`, not exhaustive) had
never been tested.  Read against *Steps G48–G52* ((GR-40)–(GR-42)),
*Steps G43–G47* ((GR-36)–(GR-39)), and the *Shared dictionary*'s (SD-6).

**Step 0 pin (mandatory, discharged before any derivation).**  (GR-41) in
full — the coset `Φ = τ + Cut(G°)`, `τ = [ℓ even]`; `wt(μ) ≡ n_hub
(mod 2)`; `μ(M) = 0` at every perfect matching; `dist ≥ wt(μ)/2 ≥ φ*/2`;
and the two recorded loosenesses (the floor is a Hamming relaxation of a
shift metric, loose by ≤ 1 on the pool, NK(2) real at `d_par = 2` vs
floor 1).  (GR-37) in full — the (c, m) model with the odd-branch balance
rider, the cut-space obstruction, the exactly-two-solutions count at
fixed `m`, and reachability with its caveat.  (GR-42) — the family, the
cyclic-4-ec habitat lemma with its F13 prism witness, `φ(NK(m)) ≥ m` with
`φ = φ* = m` exactly at `m ≡ 2 (mod 4)` and the exact `φ` OPEN in
`[m, 3m/2]` at `m ≡ 0 (mod 4)`, per-member rank certification up to
`n_hub = 50`.  (GR-40)/(GR-36) — both charges, both blocks, `max` not
sum (816 sum violations), (GR-36)'s honest W5 boundary.  (GR-38) —
laminarity at `n_hub ≤ 6` ONLY.  The 133-shape figure's provenance as
above.  (GR-4′)'s proven-case boundary — covers no habitat block.

---

### Step G53 — ledger entry 5 settled as a reading: per-shape admissibility is NOT a (GR-37)(iii) corollary — it is a separate open statement, vacuous at all-even shapes and confined to ≤ 6 branches elsewhere

**The question the spec pins first**: does (GR-37)(iii)'s reachability
clause (*"every obstruction class — parity and the balance rider alike —
is reachable by finitely many deviations"*) already prove `d_adm < ∞` at
every habitat shape?

**Answer: NO — the clause's recorded proof does not deliver its own
statement's balance half.**  The proof as landed (*Step G44*) is: the
pair-shift graph is connected, telescoping gives every `e_x + e_y`, and
evens + cuts = everything.  Every object in that argument lives in
`GF(2)^{E(G°)}/Cut(G°)` — it moves the class of the right-hand side
`t(m) = τ + μ(m)`, i.e. it addresses exactly the **parity** obstruction.
The **balance rider** is not a function of that class: at a fixed
parity-consistent `m` the branch system has exactly two solutions
(`c`, `c̄`) ((GR-37)(ii)), the odd-branch majority counts `(a, b)` swap
under `c ↔ c̄`, and balance (`a = b`) is decided by `m` — a quantity the
class-level span argument never touches.  Reading "the balance rider is
reachable" as *proven* reduces, on inspection, to "any admissible
minority map — if one exists — is finitely many deviations from any
matching", which *consumes* existence rather than proving it.  This is a
**statement-stronger-than-its-proof flag on (GR-37)(iii) as recorded**:
the parity half is what the span argument supports; the "balance rider
alike" clause should be read as unproven prose.

*(One further bookkeeping caveat, flagged for whoever transcribes
(GR-37)(iii): even the parity half needs the ≤-one-move-per-hub
accounting done explicitly.  A cleaner route the draft verified as far
as it goes: mod `Cut`, the star relation at hub `v` gives
`e_{M(v)} + e_β ≡ e_γ` (γ = the third branch at `v`), so a deviating hub
contributes `e_x` for either non-matching branch `x` at `v`; every class
has a representative avoiding `M` (a cycle-space vector supported inside
a matching is zero), leaving a system-of-distinct-representatives step
(one end hub per representative branch) that is Hall-shaped and not
discharged here.  Measured, `d_par < ∞` at every shape ever probed.)*
*(Discharged by GPSA, Step G58: the SDR is automatic — off-matching
support forces max degree 2 — and `d_par(M) = w_M` exactly, (GR-44);
`d_par < ∞` is now PROVEN.)*

**What entry 5 reduces to.**  (i) At **all-even shapes** (no odd
branches — in particular every `NK(m)`) the balance rider is **vacuous**:
admissible = parity-consistent, so `d_adm = d_par` and entry 5 holds
there outright.  (ii) In general the excess law `Σ_β(ℓ_β − 2) = 6`
((GR-21)) forces **≤ 6 odd branches at every habitat shape** (each odd
length `ℓ ∈ {3,5}` costs `ℓ − 2 ≥ 1`), and their number is even
(`#odd ≡ Σℓ ≡ 6 + 3n ≡ n ≡ 0 (mod 2)`).  So entry 5 is exactly: *a
parity-consistent minority map with balanced majorities on a fixed set of
≤ 6 odd branches exists* — a bounded-defect condition, not a growing one.
Asserted at 72 sampled pool shapes (`--balance`).

**Consequences for the TERMINATION test**: a HIT on (a′) does **NOT**
fire E3 — entry 5 stays the named successor consuming input.  **Entry 5
status: OPEN** (measured true everywhere probed; vacuously true on the
all-even stratum; the balance half is the entire content).

---

### Step G54 — (GR-43): the odd-cycle-packing shift floor — the deviation count is bounded below by a *vertex-disjoint cycle packing*, and at the necklaces it DOUBLES the (GR-41) floor

> **(GR-43)** *(proven; the accounting audited per constructed witness
> and DP-confirmed at NK(2)/NK(6)/NK(8), `--nk`)*  Let `G°` be a habitat
> hub multigraph and `C_1, …, C_m` **vertex-disjoint cycles** of `G°`
> such that `|{β ∈ C_i : ℓ_β even}|` is **odd** for every `i`.  Then
> every parity-consistent minority map — a fortiori every admissible
> colouring — has deviation distance **≥ m** from **every** perfect
> matching of `G°`:
> > `d_par(shape) ≥ m = the packing number`.
>
> At `NK(m)` (and at any all-even-pentagon variant) the `m` pentagons
> are such a packing, so `d(NK(m)) ≥ m` — **twice** the (GR-41) floor
> `⌈φ*/2⌉ = m/2` at `m ≡ 2 (mod 4)`.

*Proof.*  (1) For `μ ∈ Φ = τ + Cut(G°)`: cuts meet cycles evenly, so
`|μ ∩ C_i| ≡ |τ ∩ C_i| ≡ 1 (mod 2)`.  (2) Anchored at a perfect matching
`M`, `μ(M) = 0` ((GR-37)(ii)'s cancellation), so
`μ(m) = Σ_{v ∈ D} (e_{M(v)} + e_{β(m(v))})` — one move per deviating
hub, both flipped branches incident to that hub.  (3) A branch of `C_i`
is incident only to `C_i`'s hubs, and the `C_i` are vertex-disjoint, so
a move at `v` flips `C_i`-branches only for the (at most one) `i` with
`v ∈ C_i`, and it flips 0, 1 or 2 of them.  Two-flips contribute 0
(mod 2) to `|μ ∩ C_i|`; hence the number of moves at `C_i`-hubs flipping
**exactly one** `C_i`-branch is `≡ |μ ∩ C_i| ≡ 1 (mod 2)`, so ≥ 1.
These move sets are disjoint across `i`, so `|D| ≥ m`.  ∎

**Why this is a shift-metric statement.**  (GR-41)'s floor `wt(μ)/2` is
the Hamming price of `μ`: each move flips ≤ 2 branches.  (GR-43) prices
the same moves **cycle-locally**: inside a packed cycle a move can pay
its 2 flips only into ONE cycle, and a cycle needing odd change cannot
be paid in 2-flip coins.  At `NK(m)` the minimum-weight coset element
has weight `m` spread one-per-pentagon, so Hamming charges `m/2` while
the packing charges `m` — the gap the pool measured as "loose by ≤ 1"
is, in the large-`d` regime, **half the whole answer**.

**What dies with it.**  *Step G52*'s growth-law form
`d_fg = d_adm ≤ ⌈φ*/2⌉ + c_shift + c_balance` **with `c_shift` bounded**
(measured ≤ 1 on the pool) is **REFUTED**: `c_shift(NK(m)) ≥ m − ⌈φ*/2⌉
≥ m/4 → ∞`.  The floor's proven-exact-from-below term `⌈φ*/2⌉` is *not*
the dominant term of `d_adm` — the shift metric is.  The (a′) law itself
is untouched (below, it *survives*); what dies is only the reading in
which the parity floor plus bounded corrections computes `d_adm`.

**Tightness at the necklaces.**  `d = m` is attained: for every member
run there is a perfect matching `M` and a size-`m` deviation set — one
moving hub per pentagon at a shared "pairing" external branch, external
flips cancelling in pairs, `μ` = one pentagon branch per pentagon, `μ`
verified in `Φ` — that is parity-consistent (`--nk`, the paired search).
DP over the cycle-syndrome space (exact per matching, dims 6/16/21)
confirms the minimum at the construction's matching is exactly `m` at
NK(2)/NK(6)/NK(8); at NK(10) (dim 26, past budget) the exact value
stands on the proven lower bound + the constructed witness.  So, balance
being vacuous at all-even shapes (Step G53):
> `d_par(NK(m)) = d_adm(NK(m)) = m` **exactly**, for `m = 2, 6, 8, 10`.

*(Whether `d_par` **equals** the maximum vertex-disjoint odd-τ-parity
cycle packing in general is deliberately left as a question, not a
claim: it is min-max-shaped, and (GR-13) is the standing caution about
Edmonds-type readings in this arc.  The lower bound is proven; equality
is measured only at the necklaces.)*

---

### Step G55 — experiment 1's verdict: OUTCOME 3 with `d_par` above the floor — and the (a′) law SURVIVES its first large-`d` test, rank-certified at the optimum at every member

The spec's three-outcome experiment, run first (`--nk`):

| member | `n_hub` | floor `⌈φ*/2⌉` | `d_par = d_adm` (exact) | `d_fg` |
|---|---|---|---|---|
| NK(2)  | 10 | 1 (exact, `2^10`) | 2 | **2** (rank; agrees with GDEV's exact 2/2/2) |
| NK(6)  | 30 | 3 (`φ* = m`, (GR-42)(ii)) | 6 | **6** (rank at the optimum) |
| NK(8)  | 40 | in [4, 6] (`φ*` OPEN in [8, 12]) | 8 | **8** (rank at the optimum, 19 tests) |
| NK(10) | 50 | 5 (`φ* = m`) | 10 | **10** (rank at the optimum, 55 tests, cap 60) |

- **Outcome 3 holds, in its `d_par`-above-the-floor branch**: the whole
  stack sits at `d = m`, strictly above the floor, excess `≥ m/4`
  growing.  `d_par` is *measured* (DP-exact at NK(2)/NK(6)/NK(8);
  bounded exactly by (GR-43) + construction at NK(10)), not inferred,
  and it equals `d_adm` because balance is vacuous — the excess is the
  **shift-metric layer**, exactly the case the spec routes to *"sharpen
  (GR-41)'s Hamming relaxation to the true shift metric"*.  (GR-43) is
  the first instalment of that sharpening.
- **The (a′) law holds at all four members**: at each, an
  admissibility-**optimal** witness (deviation count exactly `m`)
  carries a **rank-certified fully-good colouring** (both blocks, both
  matrices, README §4 convention 2; caps: 12 optimal witnesses per
  member, 60 at NK(10); rank tests used 1/1/19/55).  This is the first
  test of the 133/133 regularity outside `d ≤ 3`, at deviation counts
  up to 10, and it did not break.  E1 clause (iv)'s dichotomy: nothing
  here found `d_adm < d_fg` (finite or otherwise); every `d_fg` above
  is a certified equality, not an exhausted cap.

**The (a′) census (`--free`) — where the exchange freedom lives.**  New
measurement, not in GDEV's data: group the *optimal* admissible
solutions (all matchings × all optimal deviation sets × both
`c`-solutions) by their coset element `μ`.

- Fresh 108-shape seeded pool subsample (rate 0.02, this driver's own
  seed): **all 108 have `d_fg = d_adm`** (the law's measured support now
  spans this fresh subsample + the four NK members + W3/W5/CL5/CL6).
- At **107 of 108** shapes, **every optimal μ-class carries a fully-good
  realization**: the freedom the (a′) proof needs lives *inside the
  fiber of a fixed μ* — vary the deviation set (equivalently the
  minority-dart positions) at fixed majority classes `c`.
- At **1 pool shape** and at **W3** (27/34 optimal μ-classes fully-good
  vs 34) some optimal μ-class carries **none**: there the fixed-μ
  exchange is provably insufficient and the proof must also move μ (or
  the matching).  **This is the named sticking case**: *a fixed-μ
  fiber-exchange argument cannot prove (a′) alone; the argument needs a
  second exchange axis across optimal μ-classes.*  (Consistent with the
  spec's own caution: at fixed `m` the `c`-extension has no freedom —
  and this measurement shows even the full fixed-μ fiber is sometimes
  dead.)
- Worst fully-good fraction among optima: 4/12 (shape recorded in the
  driver output).  **Binding profile of the failing optima**: every
  binding chunk at a failing optimum has **defect exactly 2** in its
  bad block — never 0 or 1 (histogram over (min defect, #branches,
  #interiors): all keys at min defect 2).  At the admissibility optimum
  the colouring is never *deeply* bad; the (a′) repair only ever has to
  buy one defect unit.  A proof-shaped restatement: *(a′) ⟺ at some
  optimum, no chunk sits at defect ≤ 2 — and the measured failures are
  all at the boundary defect 2.*

**(a′) status: OPEN — measured true everywhere probed, now including
the large-`d` regime; not proven.**  The honest MISS statement: the two
landed charges ((GR-36)/(GR-40)) price binding from below
colouring-freely, but converting them into "some optimal deviation set
avoids all defect-≤ 2 chunks" needs a counting/exchange step over the
optimal μ-classes jointly, and the census shows single-μ exchange does
not suffice at W3-type shapes.

---

### Step G56 — (b′): the balance layer is structurally confined to ≤ 6 branches, measures ≤ 2 everywhere probed including the odd-richest stratum — and the record's "W3 costs 2" is corrected to **gap 1**

- **The odd-branch cap (proven, elementary).**  Step G53(ii): every
  habitat shape has ≤ 6 odd branches, an even number of them.  So the
  balance rider's *imbalance* is ≤ 6 (≤ 3 repair units) at any shape —
  the balance layer cannot grow through the imbalance itself; the only
  way (b′) fails is a growing **repair cost per unit**, i.e. shapes
  where re-balancing forces extra parity-consistent deviations.
- **W3, layered exactly (`--balance`, all 8 matchings, exact):**
  `d_par(W3) = 2`, `d_adm = d_fg = 3` — **the W3 balance gap is 1, not
  2**.  *Step G49*'s prose ("W3 itself costs 2 there") is corrected:
  W3's stack is floor 1 → shift +1 → balance +1.  The pool's single
  `d_adm − d_par = 2` resident stands untouched; the measured balance
  gaps are now `{0, 1, 2}` (so the gap is not parity-forced to be
  even — the pool histogram's `{0, 2}` was a small-sample artifact).
- **The odd-rich necklaces `NKo(m)`** (same graphs as NK(m), the
  excess-6 moved onto odd branches — six `ℓ3` links at `m ≥ 6`; four
  `ℓ3` links + the `ℓ4` chord at `m = 2` — pentagons kept all-even so
  (GR-43) still applies; habitat by the (GR-42) lemma, machine-checked):
  `NKo(2)`: exact `d_par = d_adm = d_fg = 2`, balance gap **0**.
  `NKo(6)` (`n_hub = 30`, 6 odd branches — the first balance
  measurement at a large member): `d_par(M) = 6` (DP-exact at one
  constructed matching; ≥ 6 proven for every matching), and the first
  sampled optimal witness is already **balanced, admissible, and
  rank-certified fully good** — balance gap 0 and `d_fg = 6` at this
  matching.
- **The odd-6 pool hunt** (the odd-richest habitat stratum, 12 sampled
  shapes, exact over all matchings at `dmax 4`): balance gap **0 at all
  12**.
- **No growing gap found anywhere** (a measured negative at the
  disclosed caps, not a proof).  **(b′) status: OPEN as a theorem;
  supported, sharpened** — the true conjecture the data now suggests is
  `d_adm − d_par ≤ 2` with the constant coming from one repair unit of
  the ≤ 6-branch global count condition, and the odd-rich stratum shows
  no sign of a growing repair cost.

---

### Step G57 — where this leaves the target and the (GR-15) line (hand-off)

- **The route ledger** (coordinator updates on landing):
  **Entry 1** (uniform fully-good existence at `Λ = ∅` `D = 0`,
  growth-law re-anchoring) — **open**; (a′) **survives its sharpest
  test** (rank-certified at the optimum up to `n_hub = 50`) and stays
  the primary dispatchable attack, now with the sticking case *named*
  (fixed-μ exchange insufficient at W3-type shapes); (b′) sharpened and
  supported; (c)/(d′) untouched.  The growth law's
  **bounded-shift-correction form is REFUTED** ((GR-43)); its surviving
  content is exactly (a′) + a shift-metric characterization of `d_adm`.
  **Entry 5** — **OPEN, settled as a separate statement** (Step G53):
  not a (GR-37)(iii) corollary; vacuous on the all-even stratum;
  a ≤ 6-branch balance condition elsewhere.  Entries 2–4 unchanged.
- **TERMINATION check** (coordinator's to run; the draft's reading):
  **E1 does not fire** — no g-flank; every member measured carries a
  rank-certified fully-good colouring at its optimum; clause (iv):
  nothing found `d_adm < d_fg`, no `∞` claim anywhere (all caps
  disclosed as caps).  **E2 does not fire** — (a′) is neither refuted
  nor unprovable-as-posed; it survived where it was most likely to die.
  **E3 does not fire** — nothing here closes entry 1 (and a future (a′)
  HIT alone would not either, per Step G53).
- **The thirteenth's natural routing** (per the spec's otherwise-clause,
  outcome 3 with `d_par` above the floor): **the shift-metric layer** —
  sharpen (GR-41) to the true shift metric.  (GR-43) is the packing
  lower bound; the open question is the matching upper structure:
  whether `d_par` equals the odd-τ-cycle packing number (min-max-shaped;
  (GR-13) caution), or at least is computed by a polynomial certificate
  the closure chain can consume.  The (a′) attack itself remains
  dispatchable with its sticking case now concrete.
- **Riders, verbatim**: everything lives at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)** — and per Step G53,
  **(a′) alone would not close the existence target while entry 5 is
  open**.  (GR-15) stays OPEN, unchanged in both directions; **no
  gap-map status moves**.

---

### Verification (Steps G53–G57)

`notes/scripts/w4/gadm.py` (**new with this pass**; imports —
all read-only — `gdev` (`nk_specs`, `habitat_by_lemma`, `light_hm`,
`phi_of`, `mu_of`, `in_coset`, `fundamental_cycles`, `min_dev`,
`even_vec`), `gorient` (`cm_solve`, `cm_colouring`, `odd_balance`,
`perfect_matchings`, `m_of_matching`, `prep_shape`, `fully_good_scan`,
`fast_defects`, `darts_at`), `gexist` (`fully_good_rank`,
`ladder_specs`), `gcap` (`branch_stats`, `pool_specs`), `cflank`
(`admissible`, `cubic_habitat`), `gunif` (`WITNESSES`), `gridcol`
(`subdivide`), `kbare_common.verts_of`; rank enters only through
`gexist.fully_good_rank` — README §4 convention 2).  Local devices, none
shadowing a §1 primitive: `cycle_masks`/`dp_pref`/`dp_walk` (the exact
per-matching deviation DP over the cycle-syndrome space — the landed
`gdev.min_dev` enumerates deviation sets and is infeasible past the
pool), `mu_in_phi` (2-colouring coset test, cross-checked against
`in_coset`), `pentagon_floor_audit` ((GR-43)'s accounting per witness,
with the `μ(M) = 0` anchor gate), `complete_matching` (explicit perfect
matchings — `perfect_matchings` is never called at `n_hub ≥ 30`),
`nk_d_eq_m_witness`/`nk_d_eq_m_random` (the `d = m` constructions),
`nko_specs`, `opt_census`.  Exact integers throughout; rngs seeded per
mode, seeds printed; no `set` printed; nothing samples a placement
(§(K-clos) (AC-9)).  No pool is new: the two pool legs subsample
`gcap.pool_specs` behind the `cflank.cubic_habitat` gate at this
driver's own seed (fresh subsamples, disclosed as such); NK/NKo members
are targeted constructions.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --nk        # ~15 s  experiment 1: (GR-43) audited; d=m witnesses; DP-exact; rank at the optimum
PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --free      #  ~4 s  the (a') census: W3/CL5/CL6/NK(2) exhaustive, W5 rank-light, 108-shape fresh pool
PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --balance   #  ~5 s  (b'): odd-branch cap; W3 layered; NKo(2)/NKo(6); the odd-6 hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --adv       #  ~1 s  six controls, each must-fire/-reject
PYTHONHASHSEED=0 python3 notes/scripts/w4/gadm.py --validate  # ~25 s  all four in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-43) accounting, per witness | `--nk` | `pentagon_floor_audit`: pentagons 5-cycles, vertex-disjoint, 2-own+1-external per hub, `μ(M) = 0` gate, per-pentagon b-move parity, `dist = m`, every b-count ≥ 1 |
| (GR-43) floor vs DP | `--nk`, `--adv` | DP exact min ≥ m asserted at NK(2)/NK(6)/NK(8) and NKo(6); DP == `min_dev`'s `d_par` at NK(2) over all 8 matchings |
| `d_par = d_adm = m` exact | `--nk` | constructed `d = m` witness parity-consistent + admissible; balance asserted vacuous (`odd_balance = (0,0)`); lower bound proven |
| (a′) at the optimum | `--nk` | fully-good RANK certificates at deviation count exactly `m`, all four members; caps printed (12/12/12/60 witnesses; 1/1/19/55 rank tests) |
| the (a′) census | `--free` | exhaustive optimal-solution enumeration at W3/CL5/CL6/NK(2) + 108 fresh pool shapes; `d_fg = d_adm` asserted per shape; per-μ availability counted |
| the sticking case | `--free` | per-μ fully-good counts: 27/34 at W3, 107/108 pool shapes all-μ-good, 1 shape with a dead optimal μ-class; failing-optima defect profile all at defect 2 |
| the odd-branch cap | `--balance` | `#odd ≤ 6` and even, asserted at 72 sampled pool shapes |
| W3 balance gap = 1 | `--balance`, `--adv` | exact `min_dev` over all 8 matchings: (2, 3, 3); the gap ≥ 1 must-fire control |
| NKo / odd-6 gaps | `--balance` | NKo(2) exact (gap 0); NKo(6) DP + walk-sampled balanced witness at +0, rank-certified; 12 odd-6 shapes exact at dmax 4, all gap 0; any gap > 2 asserts a HEADLINE failure |
| coset test correctness | `--adv` | `mu_in_phi == in_coset` at 2000 random vectors |
| anchor gate (ranking item 8) | `--adv` | a near-perfect-matching base map with `μ ≠ 0` REJECTED; a doctored non-5-cycle "pentagon" REJECTED |
| cap discipline (E1 (iv)) | `--adv` | the W3 scan at `dmax 2` returns NOT-FOUND-WITHIN-CAP, never `∞` |
| entry 5 / (GR-15) / (GR-4′) as statements | — | Step G53 is a reading of the landed proof text; not driver-testable |

**Determinism.**  `--validate` was re-run by the coordinator at
`PYTHONHASHSEED` 0 and 999 (both exit 0, ~25 s): the outputs differ in
exactly one line — a `[5s]` vs `[6s]` wall-clock annotation, the
recorded exception — and in no other byte.

**Scratch probes (README's standing rule).**  None retained: every
figure above is produced by a committed driver mode.  (Development
iterations — a first witness search returning one witness instead of a
list, a first NK(8) rank hunt with too thin a witness cap (2 tests),
an odd-6 sampling rate of 0.02 raised to 0.08 — changed no mathematics;
the final driver re-derives everything.)

---

### Confidence verdict (Steps G53–G57)

| | claim | standing |
|---|---|---|
| **Step G53** | entry 5 is not a (GR-37)(iii) corollary; (GR-37)(iii)'s balance clause is statement-beyond-proof | **proven-informally as a reading of the landed proof text** (the recorded proof manipulates only `GF(2)^E/Cut`; balance is not a class function) |
| entry 5 itself | per-shape admissibility | **OPEN**; vacuously true at all-even shapes (proven); confined to ≤ 6 branches (proven); measured true everywhere probed *(since GPSA Steps G58–G60: half 1 PROVEN ((GR-44)); half 2 true-modulo-named-gap — the descent lemma's stuck case; NOT a HIT)* |
| **(GR-43)** | the odd-cycle-packing floor `d_par ≥ m` against every PM | **proven-informally** (proof above; audited per witness; DP-confirmed at three members) |
| the necklace stack | `d_par = d_adm = d_fg = m` exactly at NK(2)/6/8/10 | lower bound **proven**; upper **constructed + rank-certified per member** (caps disclosed); `d_adm = d_par` proven (balance vacuous) |
| the growth law's bounded-shift form | `c_shift ≤ 1`-style corrections | **REFUTED** ((GR-43): `c_shift ≥ m/4 → ∞` at the necklaces) |
| **(a′)** | `d_fg = d_adm` at every habitat shape | **OPEN — measured true everywhere probed, now including `d = 10`**; sticking case named (fixed-μ exchange insufficient at W3-type shapes); no counterexample |
| **(b′)** | `d_adm − d_par ≤ 2` | **OPEN — supported**: gaps `{0, 1, 2}` measured (W3 corrected to 1); odd-richest stratum all 0; imbalance structurally ≤ 6 |
| W3's balance gap | = 1 (record correction to *Step G49*'s "costs 2") | **measured, exact** (all 8 matchings) |
| **(GR-15)** | | **OPEN — unchanged in both directions.**  No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.**  The same
side as TCOL's through GDEV's: colourings of fixed graphs and exact
ranks of constructed configurations, never `PencilNondegFeasible G`; no
σ-fixed witness is read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G53–G57)

*(i)* **A proof of (a′)** — the census says what it must contain: an
exchange step that moves *between* optimal μ-classes (fixed-μ freedom is
measured insufficient at W3-type shapes), and it only ever has to repair
defect-exactly-2 chunks (no deeper failure was ever measured at an
optimum).  *(ii)* **A shape with finite `d_adm < d_fg`** — kills the law
(E2's branch); none exists among everything measured, now including the
large-`d` regime.  *(iii)* **A `d_fg = ∞` at finite `d_adm`** — a
g-flank, E1, unconditional; nothing of the kind was seen (every cap
reported as a cap).  *(iv)* **A shift-metric upper structure** —
a certificate matching (GR-43)'s packing lower bound would make `d_adm`
computable and re-arm the growth law in exact form.  *(v)* **A balance
gap > 2** — refutes (b′); the odd-rich stratum showed none.  *(vi)* **A
proof of entry 5's balance half** — with (a′) it would close the
`Λ = ∅` `D = 0` existence target modulo (GR-4′) (and only then would an
(a′) HIT fire E3).

---

### Steps G58–G62 (2026-08-18, direction GPSA) — route-ledger entry 5 attacked in BOTH halves: the Hall/SDR step is **AUTOMATIC** and the parity layer collapses to an exact per-matching coset formula (**(GR-44)**: `d_par(M) = w_M` — **half 1 PROVEN**, (GR-37)(iii)'s parity half repaired to statement-equals-proof), while the balance rider reduces via a new cut-move calculus (**(GR-45)**) to a **descent lemma** proven in its free-T1 case and open exactly at a **named stuck case** — entry 5 holds **EXHAUSTIVELY at all 97 censused shapes** (full `3^n` per shape) yet is **NOT a HIT**; **(b′)** gap 0 at every commissioned odd-rich stress member — (GR-15) stays **OPEN**, no gap-map status moves

Answering `notes/Pencil-fanout-archive.md` §"Thirteenth direction — GPSA":
**route-ledger entry 5 — per-shape admissibility (`d_adm < ∞`) in
BOTH halves** — half 1 the Hall/SDR realizability step (*Step G53*'s
recorded, undischarged caveat), half 2 the ≤ 6-odd-branch balance
rider — with **(b′)** (`d_adm − d_par ≤ 2`) the secondary and **(a′)
deliberately NOT attempted** (the named fourteenth on a HIT).
Rank-free throughout: no mode calls `fully_good_rank`, and no `d_fg`
claim is made anywhere in this pass.  Read against *Steps G53–G57*
((GR-43), entry 5's settlement), *Steps G48–G52* ((GR-40)–(GR-42)),
and *Step G44* ((GR-37)).

**Step 0 pin (mandatory, discharged before any derivation).**
(GR-37) in full — the (c, m) model with the odd-branch balance rider,
the cut-space obstruction, the exactly-two-solutions count at fixed
`m` (with the coordinator-verified sharpening: the A↔B swap swaps the
balance counts, so balance is decided by `m` alone).  *Step G53* in
full — the statement-beyond-proof flag scoped to (GR-37)(iii)'s
balance clause; the ≤ 6-odd-branch / even-count confinement; the
Hall/SDR caveat verbatim (half 1's exact target).  (GR-41) — the
coset `Φ = τ + Cut(G°)`, `τ = [ℓ even]`, `μ(M) = 0` at every perfect
matching.  (GR-42)/(GR-43) as they bear on test families — the
habitat-membership lemma; balance vacuous at all-even shapes (NK
members are controls, not tests, for half 2).  The measured record
with provenance — the 907/907 census and the 40 742-shape sweep are
per-shape admissibility witnesses a fortiori; GADM's 72-shape
`--balance` assertion; the odd-6 pool's 12 shapes at gap 0; W3's
exact stack floor 1 → shift +1 → balance +1; the pool's single
gap-2 resident.  (GR-4′)'s proven-case boundary — covers no habitat
block.

---

### Step G58 — (GR-44): the Hall/SDR step is AUTOMATIC, and the parity layer has an exact per-matching coset formula — (GR-37)(iii)'s parity half repaired to statement-equals-proof

**The question the spec pins first** (half 1): *Step G53*'s recorded,
undischarged system-of-distinct-representatives step — one end hub per
representative branch, Hall-shaped — standing between the measured
`d_par < ∞` and a proof.

**Answer: the SDR step discharges with no additional hypothesis, and
the discharge overshoots — the deviation count to the parity layer is
not merely finite but EXACTLY a coset weight.**

> **(GR-44)** *(proven; certified at 415 (shape, matching) pairs — 72
> sampled pool habitat shapes (seeded rate 0.015) + W3M/W3/W4/W5 +
> NK(2)/NKo(2), ≤ 12 matchings each — with the equality's gap
> histogram `{0: 415}`, plus the n = 30 constructive demo at
> NK(6)/NKo(6), `--sdr`)*
>
> Let `G°` be a connected cubic loop-free hub multigraph with a
> perfect matching `M` (habitat shapes qualify: cubic and bridgeless
> — (GR-37)(ii) — so Petersen supplies `M`; loop-free since a loop's
> third dart is a bridge).  Let `τ = [ℓ even]` and
> `Φ = τ + Cut(G°)`.  Define
> > `w_M := min{ wt(x) : x ≡ τ (mod Cut(G°)), supp(x) ∩ M = ∅ }`.
>
> **(i) M-avoiding representatives exist** (so `w_M < ∞`):
> `span{e_β : β ∉ M} + Cut(G°) = GF(2)^E`.
>
> **(ii) Hall is automatic, and the SDR is constructive.**  For any
> `x` with `supp(x) ∩ M = ∅`, the branches of `supp(x)` admit a system
> of distinct representative end hubs: `supp(x)` avoids `M`, so every
> hub carries at most 2 of its branches (a cubic hub has exactly two
> non-matching branches), every subgraph of maximum degree ≤ 2 is a
> disjoint union of paths and cycles, and orienting each component and
> giving every branch its head hub is an SDR.  (Hall's condition
> `|N(S)| ≥ |S|` holds for every `S ⊆ supp(x)` by the degree sum
> `2|S| ≤ 2|N(S)|`; no marriage theorem is needed.)
>
> **(iii) The exact formula.**  For every perfect matching `M`,
> > `d_par(shape, M) = w_M`.
>
> In particular `d_par(shape) = min_M w_M < ∞` at every habitat shape:
> **(GR-37)(iii)'s parity half is now statement-equals-proof**, with
> the ≤-one-move-per-hub accounting Step G53's caveat asked for done
> by the SDR's distinctness.

*Proof.*  (i): the orthogonal complement of the left side is
`{y : supp(y) ⊆ M} ∩ Cycle(G°)` (cut and cycle spaces are GF(2)
orthogonal complements); a cycle-space vector has even degree at every
hub while a matching supports degree ≤ 1, so `y = 0`.

(ii) as stated; every component of a max-degree-2 graph is a path or a
cycle, and head-assignment along an orientation is injective into hubs
and total on branches.

(iii), `≤`: take `x` attaining `w_M` and an SDR `β ↦ v_β`.  Anchor at
the all-`M` map and, at each `v_β`, move the minority dart to the
**third** branch `t_β` (≠ `M(v_β)`, ≠ `β`; the star at `v_β` has three
distinct branch indices since `G°` is loop-free).  Exactly `wt(x)`
hubs deviate, each once.  By the star relation
`e_{M(v)} + e_{t} ≡ e_{β} (mod Cut)`,
`μ(m) = Σ_β (e_{M(v_β)} + e_{t_β}) ≡ Σ_β e_β = x ≡ τ`, so `m` is
parity-consistent and `d_par(M) ≤ wt(x) = w_M`.

`≥`: let `m` be parity-consistent at deviation set `D`, `|D| = d`.
Then `μ(m) = Σ_{v∈D} (e_{M(v)} + e_{b_v})` with `b_v` the branch of
`m(v)`; each term `≡ e_{x_v} (mod Cut)` with `x_v` the third branch at
`v`.  Every `x_v` avoids `M` globally (its end `v` is already matched
by `M(v)`), so `y := Σ_{v∈D} e_{x_v}` satisfies `y ≡ μ(m) ≡ τ`,
`supp(y) ∩ M = ∅`, `wt(y) ≤ d`.  Hence `w_M ≤ d`.  ∎

**Corollaries, and where this sits against the landed record.**

- **(GR-41)(ii)'s per-move factor-2 loss is eliminated:**
  `d_par(M) = w_M ≥ φ` (the unconstrained coset minimum), where the
  Hamming floor charged `wt(μ)/2 ≥ φ*/2` — the third-branch reduction
  prices a move at ONE branch mod Cut instead of two flips.  (Both
  old floors remain valid; `w_M` is exact.)
- **(GR-43)'s necklace lower bound re-derives in one line:** at
  `NK(m)`, `d_par(M) = w_M ≥ φ(NK(m)) ≥ m` ((GR-42)(ii)) for every
  matching — the packing argument's conclusion without the packing.
  ((GR-43)'s cycle-local accounting remains the combinatorial witness
  of the same bound and is untouched as landed; the DP-exact
  `d_par = m` values at NK(2)/6/8/10 are consistent with the formula.)
- **A shape-level closed form:** `d_par(shape) = min{ wt(x) : x ∈ Φ,`
  `G° ∖ supp(x)` has a perfect matching `}` — minimize jointly over
  the coset element and an avoiding matching.
- **Hall-tightness is real but never fatal:** cycle components of
  `supp(x)` are exactly where `|N(S)| = |S|`; measured 0/78 shapes at
  the *minimum* representative (the minimum seems to prefer forests —
  observed, not developed).

**What is deliberately NOT developed** (ranking item 3's bar and the
(GR-13) caution stand): whether `w_M` — or `min_M w_M` — has an
Edmonds-type min-max / packing characterization (e.g. equality with
the odd-τ-parity cycle packing of (GR-43)) is **not attacked**.  The
formula is reported as a finding of the half-1 proof; the shift-metric
quantitative theory stays where GADM's landing left it.  (The formula
is exponential-shaped as stated; no polynomial certificate is
claimed.)

**Certification** (`--sdr`): at all 415 (shape, matching) pairs the
minimum M-avoiding representative exists, the SDR builds with the
max-degree-2 assert live at every pair, the deviated map is
parity-consistent at exactly `wt(x)` deviations, and the DP-exact
`d_par(M)` equals `w_M` (histogram `{0: 415}` — the equality's machine
witness).  At n = 30 (NK(6)/NKo(6)) the *constructive* representative
(weight 18/12) is SDR-verified while DP gives `d_par(M) = 6` — the
constructive rep is an upper bound only; the minimum is not enumerable
at n = 30 (disclosed).  F13: a doctored SDR reusing a hub is REJECTED
by the verifier; the undoctored assignment passes (`--adv` (1)).

---

### Step G59 — (GR-45): the balance-move calculus — legal deviation moves form a cut-indexed family with an exact majority-flip formula

The machinery half 2 needs (and the fixed-μ-insufficiency census of
*Step G60* shows it must cross μ-classes).

> **(GR-45)** *(proven; machine-verified at 264 legal moves over 18
> shapes — parity preservation, the `c'`-law, the two-end-consistent
> flip formula, and both corollaries, every clause asserted per move,
> `--balance` part (a))*
>
> Let `(m, c)` be parity-consistent.  A **legal move set** is a family
> `{(v_i, x_i)}` of distinct hubs `v_i` with target branches
> `x_i ∋ v_i`, `m(v_i) ∉ x_i`, such that `Σ_i e_{x_i} ∈ Cut(G°)`,
> say `= δ(S)`.  Applying it moves each `m(v_i)` to the third branch
> at `v_i` (≠ its current branch, ≠ `x_i`).  Then:
>
> **(i)** the new map `m'` is parity-consistent, with exact change
> `Δ = μ(m') + μ(m) = δ(R △ S)`, `R = {v_i}`, and solutions
> `c' = c + χ_{R△S}` (and its complement);
>
> **(ii)** the odd-branch majority flip is exact and local: for odd
> `γ` with end `p`,
> > `flip(γ) = χ_{R△S}(p) ⊕ [m(p) moved on/off γ]`,
>
> and the two ends of `γ` always agree;
>
> **(iii) (T1, the double-swap)** at a branch `z` whose BOTH end darts
> are off `z`: hubs = the two ends, targets = `z` twice
> (`Σ = 0 ∈ Cut`); it flips exactly `{z} ∩ O` — the single-branch
> majority flip, at ≤ 2 deviations of movement;
>
> **(iv) (T2, the star move)** at a hub `u`: targets = the three
> branches of `star(u)`, each repped by `u` itself or its far end
> (reps distinct, darts off targets; `Σ = δ({u})`); it flips exactly
> `star(u) ∩ O`.
>
> All flip statements are mod the global A↔B swap (the complement
> choice in `S`), which negates the imbalance `δ = a − b` and is free.

*Proof.*  (i): per move, the exact contribution is
`e_{cur} + e_{third} = δ({v_i}) + e_{x_i}` (the star relation), so
`Δ = δ(R) + Σ e_{x_i} = δ(R △ S)` — a cut — and the (GR-37)(i)
right-hand side `t(m') = t(m) + Δ` stays solvable with
`c' = c + χ_{R△S}`.  (ii): the majority of odd `γ` at end `p` is
`c(p) ⊕ [m(p) ∈ γ]`; both change only as stated, and the two-end
agreement is the solvability of the new system.  (iii)/(iv):
instantiate (ii); at a moved hub the swap crosses each non-target
branch exactly once, cancelling the `χ` term, and the target branch
keeps its dart status, exposing it.  ∎

**The (b′)-shaped consequence.**  One T1 at a majority-side odd branch
is **one repair unit**: it reduces `|δ|` by exactly 2 at the cost of
at most 2 extra deviations from any anchor matching.  This is the
mechanism under (b′)'s measured `d_adm − d_par ∈ {0, 1, 2}` — the
constant 2 = one double-swap, a global-count repair, not a per-branch
one (the anti-triviality caution's shape: the argument does not give
`≤ 0`, because a repair unit is genuinely priced at 2 movements).

F13 for the calculus (`--adv` (2)): a move targeting the branch
currently holding the dart is REJECTED by the guard; the pinned
counter-fact is the naive single-hub deviation applied anyway, which
leaves the parity class (`cm_solve` fails: a single hub can never move
`μ` by a cut — `e_x + e_y ≡ e_z`, never `0`).

---

### Step G60 — half 2's status: entry 5 reduces to a DESCENT LEMMA whose easy case is proven, whose stuck case is named — and holds EXHAUSTIVELY at every censused shape

**The reduction (proven).**  By (GR-44) the parity space is nonempty
at every habitat shape; by *Step G53*(ii) the odd branches number
`2k ≤ 6`.  Balance therefore follows from:

> **The descent lemma (OPEN in one case).**  From every
> parity-consistent `(m, c)` with imbalance `δ ≠ 0`, some legal
> (GR-45) move strictly reduces `|δ|`.

Descent terminates at `δ = 0` (values are even, bounded by 6), i.e. at
an admissible colouring; `(GR-44) + descent ⟹ entry 5` *(marked by
GDESC (GR-46) Cor. 1, Step G63: over the FULL (GR-45) legal family
the descent lemma is EQUIVALENT to entry 5's balance half, so this
reduction is true but is not a reduction to anything smaller)*.

- **Easy case (proven):** if some majority-side odd `z` has both end
  darts off it, T1@z reduces `|δ|` by 2 ((GR-45)(iii)).
- **Stuck case (OPEN — the named blocking configuration):** every
  majority-side odd branch holds a minority dart at some end.  Escape
  routes exist in profusion *(deflated by GDESC (GR-46) Cor. 1, Step
  G63: over the full legal family that profusion is exactly the
  census's balanced configurations, not extra structure — the
  optimism this sentence reads as does not survive the equivalence)*
  — an even-branch prep T1 clears a dart off
  `z` at zero majority cost when its far-end condition
  `m(far) ∉ prep-branch` holds; T2-family moves at a dart-holding hub
  flip `star(u) ∩ O` with computable net effect — but a UNIFORM
  argument that some escape always exists needs a finite local case
  analysis over the ≤ 6 odd branches with dart obstructions, and this
  dispatch did not close it.  That case analysis is the exact residual
  gap of entry 5.

**The exhaustive censuses** (`--balance` part (b), the F11
completeness mode: ALL `3^n` minority maps per shape, enumerated over
the syndrome accumulator, every passer asserted `cm_solve`-consistent
and non-passers sample-asserted inconsistent):

- **96 shapes** (93 seeded pool habitat shapes, rate 0.02, + W3M + W3
  + NK(2)): 4 all-even (balance vacuous — controls, per the spec); on
  the 92 odd-carrying shapes, 4994 parity-consistent maps, 6452
  balanced (map, c) pairs — **entry 5 holds exhaustively at every
  censused shape**, with `cflank.admissible` ground truth verified at
  3800 balanced configs (the (GR-37)(i) round-trip, re-exercised).
  Adding NKo2v (*Step G61*): **entry 5 exhaustive at 97 shapes
  total.**
- **Lemma (L) (single-flip pattern-completeness) is REFUTED as a
  full-cube statement:** 664/3620 (pattern, flip) pairs missing — the
  achievable majority-pattern set is not the full cube in general.
  **But the proof-shaped INWARD form holds exhaustively:** 0
  unbalanced achievable patterns lack an achievable `|δ|`-reducing
  single flip.  The descent lemma is measured true at pattern level
  everywhere censused.
- **The stuck case is real and confined (measured):** *(two readings
  in this bullet are REFUTED as general readings by GDESC Step G65, at
  n = 30 — the measurements themselves stand exactly as recorded)*
  stuck configurations occur at W3M (12/200 parity maps) and W3
  (120/876) — and at NO sampled pool shape *(**"confined" refuted as a
  general reading**: GDESC's capped NKp(6) hunt finds **110** stuck
  configs at n = 30, so "stuck configurations are a small-shape
  phenomenon" is a census artifact; the 12/200 and 120/876 counts are
  unaffected)* — and **all 132 are RESCUED by a single move of the
  wider {T1, T2} family** (a strictly smaller `|δ|` one (GR-45) move
  away) *(**the rescue-universality reading refuted**: 2 of those 110,
  an all-doubly-blocked `(2,2,2,2)` swap pair, defeat EVERY {T1, T2}
  move — GDESC (GR-48)(iii)'s proven kill, realized — and are rescued
  only by the K3 pair-star extension; the 132/148 figures stay true AS
  MEASURED, and every NKp(6) figure is a CAPPED sample, not a
  census)*.  Likewise all 16 stuck configs at NKo2v.  The rescue
  census is what the stuck-case analysis should be built against.
- **The fixed-μ fiber is insufficient for balance (an (a′)-relevant
  finding, reported, not developed):** 638/1655 μ-classes carry NO
  balanced pattern — balance often requires leaving the μ-class, which
  only cross-class moves ((GR-45) with `R △ S ≠ ∅` acting on `μ`)
  provide.  Structurally parallel to GADM's (a′) sticking case
  (fixed-μ fiber exchange insufficient at W3-type shapes).
- **The imbalance spectrum (an internal measurement of this dispatch —
  it appears nowhere in the landed record and moves no recorded
  figure):** `|δ| ≤ 2` at every censused n ≤ 10 shape — but this is a
  SMALL-SHAPE ARTIFACT of the census itself, refuted at NKo2v
  (exhaustive spectrum `{0: 984, 2: 864, 4: 48}`) and at NKp(6)
  samples (`|δ| = 4` seen).  The only proven cap is the structural
  `|δ| ≤ 6` (*Step G53*(ii)); descent must handle `|δ|` up to 6.
  GADM's balance-gap `{0, 1, 2}` record is a different quantity
  (`d_adm − d_par`) and is untouched.

**Verdict, half 2: TRUE-MODULO-NAMED-GAP.**  Entry 5 = (GR-44) +
descent; descent is proven in the easy case, exhaustively true
(pattern-level and config-level) everywhere censused, and open exactly
at the stuck-case analysis.

---

### Step G61 — (b′) and the commissioned odd-rich stress hunt: no growing repair cost; gap 0 at every commissioned member

Commissioned constructions (the spec's named exception to "widening a
pool is evidence, not progress"), `--odd`:

- **NKo2v** (n = 10, the four ℓ3s moved ONTO pentagon edges + the ℓ4
  chord; habitat by the (GR-42) lemma AND the exhaustive `2^{10}`
  oracle): exhaustive census 948 parity maps / 984 balanced; exact
  layers over all 8 matchings (dmax 4): `d_par = 2`, `d_adm = 2` —
  **balance gap 0**; full cube of patterns achievable (16/16); inward
  closure holds; 16/16 stuck configs rescued.
- **NKp(6)** (n = 30, one ℓ3 per pentagon — the pentagon floor
  DISARMED, a low-floor spread-odd stress): `d_par(M) = 6` DP-exact at
  the constructed matching; balanced admissible witness at
  `d_par + 0` — gap upper bound **0** at this matching.
- **NK55(6)** (n = 30, two ℓ5 links far apart, `2k = 2`):
  `d_par(M) = 8`; balanced admissible witness at `d_par + 0` — gap
  upper bound **0**.
- **NKo(6)** (GADM's member, as the spectrum control): `d_par(M) = 6`;
  balanced witness at `+0` (gap 0 at this matching, consistent with
  GADM's gap-0-at-one-matching reading).
- δ-spectra at n = 30 (dp_walk samples, budgets `d_par..d_par+6`,
  80 walks/level, caps disclosed): `|δ| ∈ {0, 2, 4}` — no `|δ| = 6`
  observed anywhere yet (a sample, not a census).

**(b′) status: OPEN as a theorem; supported, mechanism-complete.**
Measured balance gaps remain `{0, 1, 2}` (GADM's record; nothing here
moved them), gap 0 at every commissioned stress member, no growing
repair cost found (a measured negative at the disclosed caps, not a
proof).  The proof-shaped decomposition the data now suggests:
(b′) ⟸ "at some parity-optimal map `|δ| ≤ 2`" (a global-count
statement — unmeasured at optimality, flagged for the successor) +
"one descent step available there" (one T1 = one repair unit of 2,
(GR-45)).  E1 clause (v) discipline held throughout: the one
`∞`-shaped event in the whole dispatch is the synthetic `--adv` mock,
disclosed as synthetic; every real search reports caps as caps.

---

### Step G62 — where this leaves entry 5 and the (GR-15) line (hand-off)

- **The route ledger** (coordinator updates on landing): **Entry 5** —
  **half 1 (Hall/SDR parity) PROVEN** ((GR-44), with the exact
  `d_par(M) = w_M` characterization as a bonus finding; (GR-37)(iii)'s
  parity half repaired to statement-equals-proof — the balance clause
  STAYS statement-beyond-proof, so the arc's one live
  statement-beyond-proof flag is *half*-retired, not retired);
  **half 2 (balance) TRUE-MODULO-NAMED-GAP** — reduced to the descent
  lemma, proven in the easy case, exhaustively true at 97 censused
  shapes (F11: full `3^n` per shape), open exactly at the stuck-case
  analysis (the **named blocking configuration**: every majority-side
  odd branch dart-blocked; all 148 censused instances rescued by one
  {T1, T2} move).  **Entry 5 as a whole: NOT a HIT** — the balance
  half is the entire content off the all-even stratum and its uniform
  proof is not closed.  Entry 1 untouched ((a′) not attempted, per the
  spec); entries 2–4 unchanged.
- **TERMINATION check** (coordinator's to run; the draft's reading):
  **E1 does not fire** — no g-flank; clause (v): no `d_adm = ∞` shape
  (every censused shape has balanced admissible colourings at FULL
  enumeration; every capped search disclosed as a cap); clause (iv):
  untouched — the dispatch is rank-free and makes no `d_fg` claim.
  **E2 does not fire** — entry 5 is neither refuted nor
  unprovable-as-posed; half of it is now proven and the other half has
  a named finite gap.  **E3 does not fire and is NOT armed** — an
  entry-5 HIT did not occur.
- **The fourteenth's natural routing** (per the spec's
  otherwise-clause): **"entry 5 stuck with a named blocking
  configuration → that configuration"** — the descent lemma's stuck
  case: a finite local case analysis (≤ 6 odd branches, dart
  obstructions, the T1/T2-family escape catalogue), with the 148
  rescued census configs as its test bed.  The (a′) attack stays
  dispatchable behind it (and gains the fixed-μ-insufficiency balance
  datum and the (GR-45) cross-μ move family as inputs).
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **an entry-5 HIT alone
  would not close the existence target while (a′) is open** — and
  entry 5 did not HIT.  (GR-15) stays OPEN, unchanged in both
  directions; **no gap-map status moves**.

---

### Verification (Steps G58–G62)

`notes/scripts/w4/gpsa.py` (**new with this pass**; imports — all
read-only — `gadm` (`cycle_masks`, `dp_pref`, `dp_walk`, `mu_in_phi`,
`complete_matching`, `nko_specs`), `gdev` (`nk_specs`,
`habitat_by_lemma`, `light_hm`, `mu_of`, `in_coset`,
`fundamental_cycles`, `even_vec`, `min_dev`), `gorient` (`cm_solve`,
`cm_colouring`, `odd_balance`, `perfect_matchings`, `m_of_matching`,
`darts_at`, `prep_shape`), `cflank` (`admissible`, `cubic_habitat`),
`gcap` (`pool_specs`), `gunif` (`WITNESSES`), `gridcol` (`subdivide`),
`kbare_common.verts_of`.  **Rank-free**: `gexist.fully_good_rank` is
never imported or called — the target is entry 5, and a rank call
would be a scope flag onto entry 1; `min_dev`'s fully-good slot is
never consumed).  Local devices, none shadowing a §1 primitive:
`branches_at`/`is_bridgeless` (theorem-hypothesis asserts),
`m_avoiding_rep`/`min_m_avoiding_rep` (the (GR-44) representative,
constructive / exhaustive-minimum), `sdr_build`/`sdr_verify` (the
path/cycle-orientation SDR and its adversarial verifier),
`parity_census` (the full `3^n` enumeration over a syndrome
accumulator — `μ = Σ_v e_{f(v)}` makes the syndrome per-hub
accumulable), `pattern_of`, `apply_cut_move`/`cut_side`/
`predict_flips`/`t1_move`/`all_moves` (the (GR-45) calculus and its
{T1, T2}-family neighbourhood), `nkp_specs`/`nk55_specs`/`nko2v_specs`
(the commissioned stress constructions), `balanced_witness_hunt` (the
DP-traceback upper-bound search).  Exact integers over GF(2)
throughout; rngs seeded per mode, seeds printed; no `set` printed;
nothing samples a placement (§(K-clos) (AC-9)).  No pool is new: the
census legs subsample `gcap.pool_specs` behind the
`cflank.cubic_habitat` gate at this driver's own seeds (fresh
subsamples, disclosed as such); NKo2v/NKp(6)/NK55(6) are commissioned
constructions under the spec's named exception.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --sdr       #  ~3 s  (GR-44) certified at 415 pairs; d_par(M) = w_M gap {0: 415}; n = 30 demos
PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --balance   #  ~5 s  (GR-45) at 264 moves; full-3^n censuses at 96 shapes; stuck census + rescues
PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --odd       #  ~3 s  commissioned stress: NKo2v exhaustive; NKp(6)/NK55(6)/NKo(6); delta spectra
PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --adv       #  ~1 s  five controls, each must-fire/-reject
PYTHONHASHSEED=0 python3 notes/scripts/w4/gpsa.py --validate  # ~10 s  all four in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-44)(i): M-avoiding representatives exist | `--sdr` | `min_m_avoiding_rep` asserts nonempty at every (shape, matching) pair; the constructive rep at n = 30 |
| (GR-44)(ii): Hall automatic, SDR constructive | `--sdr` | the max-degree-2 assert live per pair; `sdr_verify`: injective, end-hubs, off-M, parity-consistent at exactly `wt(x)` deviations |
| (GR-44)(iii): `d_par(M) = w_M` | `--sdr` | DP-exact `d_par(M)` vs `w_M` per pair; `≤` asserted; gap histogram `{0: 415}` is the equality's witness |
| (GR-45), all clauses | `--balance` | 264 random legal moves: parity preserved, `c' = c + χ` law, flip formula asserted at BOTH ends, T1/T2 corollaries (mod swap) |
| entry 5 per censused shape | `--balance`, `--odd` | full `3^n` parity census; ≥ 1 balanced asserted per shape; `admissible()` ground truth at 3800 balanced configs |
| the descent lemma's inward form | `--balance`, `--odd` | 0 unbalanced achievable patterns without an achievable `\|δ\|`-reducing flip; all 148 stuck configs rescued by one {T1, T2} move |
| fixed-μ insufficiency | `--balance` | 638/1655 μ-classes carry no balanced pattern (exhaustive per shape) |
| (b′) at the stress members | `--odd` | NKo2v exact over all matchings (gap 0, dmax 4); NKp(6)/NK55(6)/NKo(6) balanced witnesses at `+0`; any gap > 2 asserts a HEADLINE failure |
| E1 clause (v) discipline | `--adv` | the impossible predicate (`na = nb + 1`, δ is even): the CAPPED search reports a CAP, the FULL enumeration reports genuine `∞` (synthetic mock, disclosed); negative control 984 balanced at the same shape |
| W3's layering must-detect | `--adv` | 12 parity-consistent maps at `d ≤ 2` over all 8 matchings, 0 balanced — must equal (12, 0), the (GR-41) layering |
| doctored SDR must-reject | `--adv` | hub-reuse REJECTED; the undoctored assignment passes |
| coset test correctness | `--adv` | `mu_in_phi == in_coset` at 200 random vectors |
| the uniform halves as statements | — | half 2's stuck case and (b′) are theorem gaps; not driver-testable |

**Determinism.**  `--validate` was re-run by the coordinator at
`PYTHONHASHSEED` 0 and 999 (both exit 0, ≈9 s): the outputs are
**byte-identical including the wall-clock lines**.

**Scratch probes (README's standing rule).**  None retained: every
figure above is produced by a committed driver mode.  (Development
iterations — the T1/T2 corollary asserts gaining the mod-global-swap
normalization, the E1(v) must-NOT-fire control reshaped from a starved
hunt to the impossible-predicate capped search, an `in_coset`
double-τ argument fix caught by the cross-check itself — changed no
mathematics; the final driver re-derives everything.)

---

### Confidence verdict (Steps G58–G62)

| | claim | standing |
|---|---|---|
| **(GR-44)** | Hall/SDR automatic; `d_par(M) = w_M` exact; `d_par < ∞` | **proven-informally** (both directions; certified 415/415 at gap 0) |
| entry 5, half 1 | the Hall/SDR parity half | **PROVEN** — (GR-37)(iii)'s parity half statement-equals-proof; the balance clause STAYS statement-beyond-proof |
| **(GR-45)** | the cut-move calculus + exact flip formula | **proven-informally** (machine-verified at 264 moves, every clause) |
| the descent lemma | some legal move reduces `\|δ\|` | free-T1 case **proven**; stuck case **OPEN** (named precisely); exhaustively true at every censused configuration |
| entry 5, half 2 | the balance half | **true-modulo-named-gap** (the stuck case); EXHAUSTIVE at 97 shapes (full `3^n` each) |
| entry 5, whole | per-shape admissibility, uniform | **OPEN — NOT a HIT**; E3 not armed |
| **(b′)** | `d_adm − d_par ≤ 2` | **OPEN — supported**: gap 0 at every commissioned stress member; mechanism one T1 = one repair unit of 2; `\|δ\|` at parity-optimal maps unmeasured |
| the `\|δ\|` spectrum | this census's `\|δ\| ≤ 2` reading | **an internal measurement only** — refuted at NKo2v (`\|δ\| = 4` exhaustive); only the structural ≤ 6 is proven |
| **(GR-15)** | | **OPEN — unchanged in both directions.**  No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.**  The
same side as TCOL's through GADM's: colourings of fixed graphs and
exact GF(2) computations on constructed configurations, never
`PencilNondegFeasible G`; no rank is computed anywhere in this pass;
no σ-fixed witness is read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G58–G62)

*(i)* **Closing the stuck-case catalogue** — a finite local case
analysis (≤ 6 odd branches, dart obstructions, the T1/T2-family
escapes) upgrades entry 5 to proven-informally; with (a′) that would
close the `Λ = ∅` `D = 0` existence target modulo (GR-4′), and only
then does an (a′) HIT fire E3 (*Step G53*'s consequence, unchanged).
*(ii)* **A habitat stuck configuration defeating EVERY (GR-45) move**
— demotes the descent route (the statement stays exhaustively true
everywhere censused; existence could still hold by other means).
*(iii)* **A `d_adm = ∞` shape at FULL enumeration** — E1 clause (v),
the arc's one unconditional escalation; nothing of the kind was seen
(every cap reported as a cap).  *(iv)* **A growing balance-repair
family** — refutes (b′); none at the commissioned members.  *(v)*
**Measuring `\|δ\|` at parity-OPTIMAL maps** — the unmeasured half of
(b′)'s proof-shaped decomposition.  *(vi)* **A min-max or polynomial
certificate for `w_M`** — deliberately NOT pursued here (ranking item
3's bar; (GR-13) caution); it would make `d_par` computable and re-arm
the growth law in exact form.

---

### Steps G63–G67 (2026-08-18, direction GDESC) — the entry-5 descent lemma's stuck case is **RESHAPED, not closed**: **(GR-46)** proves the (GR-45) legal-move family **one-move TRANSITIVE**, so the descent lemma over the FULL family is **equivalent to entry 5's balance half** (the descent framing was never a weakening, and the stuck case is not a smaller residual); **(GR-47)** puts parity-consistent maps in a (coset representative, SDR end-selection, perfect matching) **normal form** that turns balance into a matching-flexibility statement; **(GR-48)** is the escape catalogue — the exact reduction criterion, the K1/K2 rescues, a **PROVEN kill** of the {T1, T2} family at all-doubly-blocked configurations and the K3 pair-star extension that repairs it — with the kill **REALIZED at n = 30**, so the bounded {T1, T2} descent route is **DEMOTED by witness** while **entry 5 stays OPEN, NOT a HIT, E3 NOT armed**, its residual named as **input (X)**; **(b′)**'s named unmeasured half is measured (`|δ|` at parity-optimal maps `{0: 92, 2: 2}`) — (GR-15) stays **OPEN**, no gap-map status moves

Answering `notes/Pencil-fanout-archive.md` §"Fourteenth direction — GDESC":
**the entry-5 descent lemma's STUCK CASE** — the one open piece of
route-ledger entry 5's balance half, named at *Step G60* — with
**(b′)** the secondary and **(a′) deliberately NOT attempted** (it
stays entry 1's primary).  Rank-free throughout: no mode calls
`fully_good_rank`, and no `d_fg` claim is made anywhere in this pass.
Read against *Steps G58–G62* ((GR-44), (GR-45), the descent lemma and
its censuses), *Steps G53–G57* ((GR-43), entry 5's settlement) and
*Step G44* ((GR-37)).

***Notation, fixed for this whole arc*** *(the spec's warning made
binding)*: **`δ` is the odd-branch imbalance** `a − b` and nothing
else; **cuts are written `∂(S)`** — the landed (GR-45) text at *Step
G59* writes `δ(S)` for the cut, and every citation of it below
silently renames to `∂(S)`.  The driver writes `imb` for the
imbalance throughout.

**Step 0 pin (mandatory, discharged before any derivation).**
(GR-45) in full (*Step G59*: legal move sets `{(v_i, x_i)}`, distinct
hubs, `x_i ∋ v_i`, `m(v_i) ∉ x_i`, `Σ_i e_{x_i} = ∂(S) ∈ Cut(G°)`;
action = each dart to the third branch; clause (i) `Δ = ∂(R △ S)`,
`c′ = c + χ_{R△S}`; clause (ii) the two-end-consistent flip formula;
(iii) T1; (iv) T2; all mod the free global A↔B swap, which negates
`δ`).  *Step G60* in full (the descent lemma, the easy case's proof,
the stuck case's exact wording, the 148-config rescue census with its
"none at any sampled pool shape" qualifier, the fixed-μ insufficiency
638/1655, lemma (L)'s full-cube REFUTATION with its inward form at 0
failures, the `|δ|` spectrum: only the structural `≤ 6` proven, `≤ 2`
a small-shape artifact).  (GR-44) (*Step G58*: `d_par(M) = w_M`
exact, Hall automatic, the parity space nonempty at every habitat
shape — consumed, not re-derived).  *Step G53* (≤ 6 odd branches,
evenly many; balance vacuous at all-even shapes).  (GR-37)(i)/(ii)
(*Step G44*: the (c, m) model, the per-branch equation, exactly two
`c`-solutions at fixed `m`, the A↔B swap swapping the balance
counts).  (GR-41) (`Φ = τ + Cut(G°)`, `τ = [ℓ even]`, `μ(M) = 0` at
every perfect matching).  The measured record with its qualifiers:
entry 5 exhaustive at 97 shapes (full `3^n` each); (b′) gaps
`{0, 1, 2}` — **a different quantity from `|δ|`**; W3's stack floor
1 → shift +1 → balance +1; (GR-4′) covers no habitat block.

---

### Step G63 — (GR-46): the (GR-45) legal-move family is TRANSITIVE — every parity-consistent map is ONE legal move from every other — so the descent lemma, as posed over the full family, IS entry 5's balance half

**The question the spec pins first**: prove that from every stuck
configuration some legal (GR-45) move strictly reduces `|δ|`.  The
first thing this pass establishes is that the question, quantified
over the **full** legal family, is not a residual *case* of anything:
it is entry 5's balance half verbatim, because the legal-move family
is far larger than the landed record ever used.

> **(GR-46)** *(proven; machine-certified at 769 random parity-map
> pairs over 99 censused shapes plus an n = 30 demo at NKp(6), every
> clause asserted — legality guards, target sum a cut, arrival at
> `m′`, the `c′ = c + χ` law; `--stuck`)*
> Let `m`, `m′` be ANY two parity-consistent minority maps of the same
> habitat shape.  Set `R = {v : m(v) ≠ m′(v)}` and, for `v ∈ R`,
> `x_v` = the third branch at `v` (≠ branch of `m(v)`, ≠ branch of
> `m′(v)`).  Then `{(v, x_v)}_{v∈R}` is a **legal (GR-45) move set**,
> and applying it carries `m` to exactly `m′`.

*Proof.*  Hubs distinct, `x_v ∋ v`, `m(v) ∉ x_v`: immediate (the three
branch indices at a cubic loop-free hub are distinct).  The cut
condition: by the star relation `e_{x_v} = ∂({v}) + e_{cur_v} +
e_{new_v}`, so `Σ_v e_{x_v} = ∂(R) + Σ_{v∈R}(e_{cur_v} + e_{new_v}) =
∂(R) + (μ(m) + μ(m′))` — for hubs off `R` the two μ-terms cancel —
and `μ(m) ≡ τ ≡ μ(m′) (mod Cut)`, so the whole sum is a cut.  The
move's action sends each `m(v)` to the third branch ≠ `cur_v`,
≠ `x_v`, i.e. to `new_v`.  ∎

**Corollary 1 (the collapse).**  For parity-consistent `(m, c)` with
`δ ≠ 0`: *a legal (GR-45) move strictly reducing `|δ|` exists* ⟺
*some parity-consistent map of the shape has strictly smaller `|δ|`*.
Hence the **descent lemma over the full legal family ⟺ the
achievable-`|δ|` set contains 0 at every odd-carrying habitat shape ⟺
entry 5's balance half** (with (GR-44) supplying nonemptiness).  The
descent framing adds nothing over existence at this generality; the
configuration one starts from is irrelevant except through its `|δ|`.
In particular the "stuck case" is **not smaller than entry 5**: any
proof of it must construct balance, and *Step G60*'s "escape routes
exist in profusion" is, over the full family, a restatement of the
census's balanced configurations, not extra structure.

**Corollary 2 (the demotion event relocates).**  A configuration
defeating **every** legal (GR-45) move is a configuration whose `|δ|`
is the shape's spectrum minimum > 0 — which, balance being exactly
`|δ| = 0`, exists **iff `d_adm = ∞` at that shape**, i.e. iff the
shape is an E1 clause-(v) g-flank.  *Step G62(ii)*'s demotion event is
therefore meaningful only for a **restricted, named move catalogue**:
a "{T1, T2}-local demotion witness" (a stuck configuration defeating
every T1 and every T2) demotes the *local* descent route and touches
neither entry 5 nor E1.  Such witnesses exist — *Step G65* constructs
the first two.  The full-family demotion branch can never fire
separately from E1(v).

**Corollary 3 (what stays contentful).**  The landed easy case (free
T1) and the whole stuck-case programme are statements about a
**bounded local catalogue**; the inward form of lemma (L)
(single-bit-flip achievability, 0 failures everywhere censused) is
likewise *not* implied by (GR-46) — transitivity reaches any
achievable pattern in one move but says nothing about which patterns
are achievable.  The contentful open statements after this step are
exactly: (a) balance existence = entry 5's balance half (*Step G64*
gives it a new normal form), and (b) the bounded-catalogue descent
(*Step G65* gives its case analysis, its provable kill, and its first
large-shape counterexample to the {T1, T2} version).

---

### Step G64 — (GR-47): the normal form — parity-consistent maps are exactly (coset representative, SDR end-selection, complementary perfect matching) triples, and balance is a matching-theoretic statement

> **(GR-47)** *(proven; round-tripped at ALL 6220 parity-consistent
> maps of 99 censused shapes — decomposition, reconstruction and the
> pattern formula asserted at every odd branch of every map,
> `--stuck`)*
> Let `m` be a minority map of a cubic loop-free `G°`.  Write
> `n_β ∈ {0, 1, 2}` for the number of end darts on branch `β`, and set
> `X = {β : n_β = 1}`, `T = {β : n_β = 2}`, `φ(β ∈ X)` = the
> dart-holding end.  Then `m ↔ (X, φ, T)` is a bijection onto triples
> with: `φ` **injective** (an SDR of end hubs), `T` a **perfect
> matching of `V ∖ φ(X)`** with `T ∩ X = ∅`, and `V = φ(X) ⊔ V(T)`;
> and `m` is **parity-consistent iff `χ_X ∈ Φ = τ + Cut(G°)`** (since
> `μ(m) = χ_X`).  The `c`-solutions are the two potentials of
> `τ + χ_X`, and for every odd branch `γ` with end `u`:
> > `pattern(γ) = c(u) ⊕ [γ ∈ T] ⊕ [γ ∈ X and φ(γ) = u]`.

*Proof.*  Each hub darts exactly once, so `Σ_β n_β = n` and every hub
lies in exactly one of: the selected end of an `X`-branch, or an end
of a `T`-branch; `T`-branches consume both ends, so `T` is a matching
and `V = φ(X) ⊔ V(T)`; `φ` is injective since a hub darts once.
Conversely any such triple rebuilds `m`.  `μ(m) = Σ_v e_{f(v)} =
Σ_{β∈X} e_β + Σ_{β∈T} 2e_β = χ_X` over GF(2); parity-consistency is
`τ + μ(m) ∈ Cut` ⟺ `χ_X ≡ τ`.  The pattern formula is the definition
`pattern(γ) = c(u) ⊕ [m(u) ∈ γ]` read through the triple.  ∎

**What this buys.**  Combined with (GR-46) Corollary 1, entry 5's
balance half is EXACTLY:

> *(the balance half, normal form)*  Every odd-carrying habitat shape
> admits a triple — `X ∈ Φ` **as a set**, an injective end-selection
> `φ` of `X`, and a perfect matching `T` of `V ∖ φ(X)` avoiding `X` —
> whose pattern (formula above, `c` = either potential of `τ + χ_X`)
> takes the value 1 on exactly half the odd branches.

This is a **matching-theoretic existence statement with a bounded side
condition** (≤ 6 odd branches), and it names the freedom axes the move
calculus obscures: (i) shift `X` by any cut (which moves `c` by the
matching `χ`), (ii) re-select `φ` ends, (iii) re-match `T` — each
toggle flips a computable set of pattern bits.  In particular: at
fixed `(X, φ)`, replacing `T` by `T △ C` along an alternating cycle
`C` of `H(X, φ) = (V ∖ φ(X), E ∖ X)` flips **exactly the odd branches
on `C`** (`c` is untouched since `X` is); a `C` through odd `γ`
avoiding the other ≤ 5 odd branches flips `pattern(γ)` alone.
Re-selecting `φ(γ)` for `γ ∈ X ∩ O` flips `pattern(γ)` modulo the odd
branches its re-matching toggles.  The obstruction to a toggle is
**pure matching flexibility** in `H(X, φ)` — e.g. "some perfect
matching of `H` contains γ / avoids γ, reachable through few odd
branches" — which is where the 1-extendability / Plesník-type toolkit
for cubic bridgeless multigraphs applies and where the landed calculus
has no purchase.  (GR-44)'s construction supplies the *existence* of
one triple; the open content is steering its pattern, and *Step G65*'s
closing paragraph records how far the steering argument got.

---

### Step G65 — (GR-48): the stuck-case escape catalogue — the exact reduction criterion, the K1/K2/K3 cases, a PROVEN kill of the {T1, T2} family, and its first realized witnesses at n = 30

> **(GR-48)** *(the catalogue; clauses (i)–(iii) proven, clause (iv)'s
> per-instance certification by driver; `--cases`, `--stuck`)*
> Let `(m, c)` be parity-consistent, `δ ≠ 0`, WLOG `δ > 0` (majority
> side A; the swap is free).
>
> **(i) The reduction criterion, exact.**  A legal move with flip set
> `F ⊆ O` changes `δ` to `δ − 2·net(F)`, `net(F) = #(F ∩ maj) −
> #(F ∩ min)`; it **strictly reduces `|δ|` iff `1 ≤ net(F) ≤ δ − 1`**.
> (`net = δ` lands at `−δ`: NOT a reduction.  At `δ = 2` — every stuck
> configuration ever censused — the criterion is `net(F) = 1`
> exactly.)
>
> **(ii) K1/K2 (the T2 rescues).**  At a hub `v` that is an end of a
> majority branch, any legal T2@`v` flips `star(v) ∩ O` ((GR-45)(iv))
> and rescues iff `net(star(v) ∩ O) ∈ [1, δ − 1]`.  Legality is an SDR
> of the three rep sets `{r ∈ ends(β) : m(r) ∉ β}`, `β ∈ star(v)`.
> (K1: `m(v)` on the majority branch; K2: off it.)
>
> **(iii) The doubly-blocked kill (proven).**  If **every majority
> branch holds BOTH its end darts**, then NO {T1, T2} move reduces
> `|δ|`.  *Proof:* T1 at a majority branch is illegal (a dart sits on
> it); T1 elsewhere flips at most a non-majority branch (`net ≤ 0`).
> A T2 at hub `v` is legal only if every branch of `star(v)` has a
> nonempty rep set; if `v` is an end of a majority branch `γ`, `γ`'s
> rep set is empty (both ends' darts sit on `γ`), so T2@`v` is
> illegal — and a hub that is an end of no majority branch has
> `net(star(v) ∩ O) ≤ 0`.  ∎  (Asserted mechanically at every
> doubly-blocked branch of every censused stuck config, and by
> exhaustive scan at the two realized witnesses below.)
>
> **(iv) K3 (the pair-star extension).**  For a doubly-blocked
> majority `γ` with ends `S = {u, w}`: the move sets with targets =
> the branches of `∂(S)`, each repped by one of its OWN ends with dart
> off it, reps distinct, are **legal** (`Σ` targets `= ∂(S)` by
> construction — this family lies OUTSIDE {T1, T2} in general).  Every
> member flips `γ` (both `γ`-darts move off `γ`, and `u, w ∈ R ∩ S`
> cancel in `χ_{R△S}`), plus a per-instance-computable side set from
> (GR-45)(ii); reduction is certified per instance by the driver.

**The census, re-derived and classified** (`--stuck`, `--cases`; a
fresh pool subsample at this driver's seeds + W3M + W3 + NKo2v):

- The 148 stuck configs reproduce exactly (W3M 12/200, W3 120/876,
  NKo2v 16/948; **none** at 96 fresh sampled pool shapes).  Blocking
  profiles (per-majority-branch end-dart counts): `(1,1)`×116,
  `(1,1,1)`×16, `(1,2)`×16 — **all at `|δ| = 2`**, none
  all-doubly-blocked.
- **Case coverage: 148/148 fire K1** (a reducing T2 at a dart-ON end
  of a majority branch); the 16 `(1,2)`-profile configs also fire K3;
  K2 is never *needed* on this census.  Every best rescue lands at
  `|δ| = 0` directly.  (GPSA's 148/148 single-{T1, T2} rescue
  re-derived.)
- **The commissioned large-shape hunt found what the record said did
  not exist.**  At NKp(6) (n = 30, six odd branches): **110 stuck
  (map, c) configs** among 360 dp_walk samples at budgets
  `d_par..d_par+4` (**a CAPPED sample, not a census**; caps disclosed)
  — the first stuck instances above n = 10, killing the "stuck configs
  are a small-shape phenomenon" reading — with profiles up to
  `(2,2,2,2)` and `|δ|` up to 4.  At NK55(6): 4 stuck, all `(1,1)`.
- **The {T1, T2}-local demotion event is REAL.**  Two of the 110 (a
  swap pair, profile `(2,2,2,2)`, `|δ| = 2`: every majority branch
  doubly-blocked) are **unrescued by ANY single {T1, T2} move**
  (exhaustive scan) — exactly clause (iii)'s kill, realized.  This is
  *Step G62(ii)*'s named event **in its only coherent (local)
  reading** ((GR-46) Cor. 2): the {T1, T2} descent route is DEMOTED —
  its rescue universality was a small-shape artifact, the same trap
  class as the `|δ| ≤ 2` reading GPSA refuted.  Entry 5 is untouched
  (NKp(6) has balanced admissible configs — GPSA's gap-0 witness); it
  is the *route* that died, on schedule.
- **K3 repairs the catalogue where {T1, T2} dies**: at both witnesses
  a K3 pair-star at ANY of the four doubly-blocked majority branches
  rescues **directly to `|δ| = 0`**.  The extended catalogue
  {T1, T2, K3} has, as of this pass, no known failure.

**The honest residual, named.**  A uniform proof that some
{T1, T2, K3} member always rescues does not close here, and the
obstruction is structural: every case's *legality* rides on dart
positions one step outside the odd neighbourhood (K1/K2's far-end rep
conditions; K3's four far-end conditions `m(f) ∉ β_side`), and nothing
in the calculus forces those conditions — an adversarial
parity-consistent placement can, as far as this pass can prove, defeat
any fixed bounded catalogue the same way the NKp(6) witnesses defeat
{T1, T2}.  By (GR-46) Cor. 1 the uniform statement over the full
family is entry 5's balance half itself, so the input the case
analysis is missing is not another case — it is an existence
principle.  **Named input (X): balance existence in the (GR-47) normal
form** — exhibit, per shape, a triple `(X, φ, T)` with balanced
pattern, using matching flexibility (1-extendability of cubic
bridgeless multigraphs; Plesník-type avoidance; alternating-cycle
toggles through the ≤ 6 odd branches) rather than move-availability
case analysis.  Route notes recorded for the successor: (a) toggling
odd `γ` in/out of `T` flips exactly `pattern(γ)` at fixed `X, φ` — the
obstruction is `γ` forced-in/forced-out of all PMs of `H(X, φ)`;
(b) for `2k = 2` the cut-space projection onto the two odd coordinates
is onto unless `{γ₁, γ₂}` is a 2-edge cut (then every `X ∈ Φ` meets it
evenly), so the `X`-shift axis alone nearly settles the minimal
stratum, split by that dichotomy *(corrected by GBAL (GR-54)/Step G72:
the exceptional side is the PARALLEL pair — a cycle-space condition —
not a 2-edge cut; and both readings are vacuous at habitat shapes, so
the dichotomy is moot)*; (c) the pattern-weight parity is NOT
an invariant (both parities occur at NKo2v), so no parity obstruction
blocks (X).

---

### Step G66 — (b′): the named unmeasured half measured — `|δ|` at parity-OPTIMAL maps is ≤ 2 at every censused shape, and the repair-unit reading survives with zero violations

(`--opt`; exact off the full `3^n` censuses, all matchings, distances
per map; 94 odd-carrying shapes — a fresh pool subsample plus W3M, W3
and NKo2v.)

- **min `|δ|` over parity-optimal maps**: `{0: 92, 2: 2}` (W3 and one
  pool shape at 2).  *Step G61*'s decomposition — *(b′) ⟸ "at some
  parity-optimal map `|δ| ≤ 2`" + "one descent step available there"*
  — has its first half **measured TRUE at every censused shape** (a
  measured positive at these shapes, not a proof; its second half is
  exactly the stuck case).
- **Exact balance gaps**: `{0: 92, 1: 2}` — consistent with GADM's
  `{0, 1, 2}` record (nothing here moves it; the pool's single gap-2
  resident was not in this subsample).  Mechanism reading
  `gap ≤ min-|δ|-at-optimum`: **0/94 violations**.
- Pins: W3 `(d_par, d_adm, gap, opt-|δ|) = (2, 3, 1, 2)` (landed
  2, 3, 1); NKo2v `(2, 2, 0, 0)` (landed 2, 2, 0), census-derived
  layers cross-checked equal to `min_dev`'s.
- **(b′) status: OPEN as a theorem; supported, now with BOTH halves of
  its proof-shaped decomposition instantiated** — the first half
  measured true everywhere censused, the second half reduced to this
  direction's residual.  No growing repair cost; no gap > 2 anywhere
  (a `> 2` find would have been a HEADLINE and the assert would have
  fired).

**Reading downgraded by §(K-grid) *Step G88* (direction BALB,
2026-08-19) — the figures above stand, unaltered.** (GR-69) proves
`|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` from (GR-51)(i)(a)'s necessity alone, so on
this stratum (`n_hub ≤ 6`, ceiling 2) the `{0: 92, 2: 2}` min-`|δ|`
figure and the `{0: 92, 1: 2}` gap figure above are **forced by
arithmetic, not evidence for the general claim** — no configuration
there could have been more imbalanced than 2, optimal or not. A reader
citing these numbers as support for `n_hub ≥ 8` is citing the wrong
thing: (GR-69) is FALSE from `n_hub = 8` (an explicit Wagner-graph
witness reaches `|δ| = 4`), and the live evidence past the boundary is
*Step G90*'s 536 exact shapes.

---

### Step G67 — where this leaves entry 5 and the (GR-15) line (hand-off)

- **The route ledger** (statuses as updated at this landing):
  **Entry 5** — half 1 (parity) PROVEN, unchanged ((GR-44)); **half 2
  (balance) TRUE-MODULO-NAMED-GAP, the gap RESHAPED**: the descent
  lemma over the full (GR-45) family is now **proven equivalent to the
  balance half itself** ((GR-46) Cor. 1) — it is not a smaller case
  and cannot be closed by move-availability analysis alone; the
  bounded {T1, T2} descent route is **DEMOTED by witness** (two n = 30
  all-doubly-blocked stuck configs defeating every {T1, T2} move —
  clause (iii)'s kill realized); the extended {T1, T2, K3} catalogue
  rescues everything ever seen (148 census + 114 hunted, both
  witnesses to `|δ| = 0`) but its uniformity needs the named input
  (X); the proof-shaped instrument is now the **(GR-47) normal form**
  (balance existence as a coset-representative + SDR + perfect-
  matching statement).  **Entry 5 as a whole: OPEN, NOT a HIT; E3 NOT
  armed.**  Entry 1 untouched ((a′) not attempted; the cross-μ
  structure of (GR-46) — every μ-class in `Φ` one move from any
  other — is an (a′)-relevant finding, reported, not developed).
  Entries 2–4 unchanged.
- **TERMINATION check** (coordinator-run at this landing; the draft's
  reading, verified): **E1 does not fire** — no g-flank; clause (v):
  no `d_adm = ∞` anywhere (every censused shape balanced at FULL
  enumeration; the NKp(6)/NK55(6) hunts are disclosed CAPS, and an
  exhausted cap is not `∞`); clause (iv): untouched — the pass is
  rank-free, no `d_fg` claim anywhere.  The two demotion witnesses are
  **{T1, T2}-local only**, and by (GR-46) Cor. 2 a *full-family*
  demotion witness would have been E1 clause (v) itself.  **E2 does
  not fire** — entry 5 is neither refuted nor unprovable-as-posed (the
  stuck case is *re-posed*, and an equivalence is not an
  unprovability), with a named successor instrument; entry 1 still
  carries (a′) as an open-with-a-named-dispatchable-attack.  **E3 does
  not fire and is NOT armed** — no entry-5 HIT.
- **The fifteenth's natural routing** (the draft's reading of the
  spec's otherwise-clause, *"a demotion witness → the
  balance-existence question at that configuration's family, by an
  instrument other than descent"*; the dispatch itself is a
  coordinator/user call, not made here): **the balance-existence
  question in the (GR-47) normal form** — a matching-flexibility
  attack (toggle lemmas + 1-extendability / Plesník-type inputs on
  `H(X, φ)`), with the NKp(6) all-doubly-blocked family as its first
  test bed and the `2k = 2` dichotomy (route note (b)) as its opening
  case.  **(a′) stays dispatchable with no bar** as entry 1's primary.
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **an entry-5 HIT would
  not close the existence target while (a′) is open — and entry 5 did
  not HIT**; (GR-37)(iii)'s flag stays **HALF-retired** (the parity
  half repaired by (GR-44); the balance clause stays
  statement-beyond-proof).  (GR-15) OPEN, unchanged in both
  directions; **no gap-map status moves**.

---

### Verification (Steps G63–G67)

`notes/scripts/w4/gdesc.py` (**new with this pass**; imports — all
read-only — `gpsa` (`branches_at`, `is_bridgeless`, `delta_of`,
`parity_census`, `pattern_of`, `apply_cut_move`, `cut_side`,
`t1_move`, `all_moves`, `nkp_specs`, `nk55_specs`, `nko2v_specs`),
`gorient` (`cm_solve`, `odd_balance`, `perfect_matchings`,
`m_of_matching`, `prep_shape`), `gdev` (`min_dev`,
`habitat_by_lemma`), `gadm` (`cycle_masks`, `dp_pref`, `dp_walk`,
`mu_in_phi`, `complete_matching`), `cflank` (`cubic_habitat`), `gcap`
(`pool_specs`), `gunif` (`WITNESSES`), `gridcol` (`subdivide`),
`kbare_common.verts_of`.  **Rank-free**: `gexist.fully_good_rank` is
never imported or called; no `d_fg` claim is made anywhere).  Local
devices, none shadowing a §1 primitive: `imb_of`/`majority_of`/
`block_ends` (pattern readers), `transit_move` (the (GR-46)
construction), `normal_form`/`rebuild_nf` (the (GR-47) bijection),
`t2_at`/`ts_pair_moves` (the per-hub T2 family and the K3 pair-star),
`targets_cut`/`move_imb` (the legality test this driver runs itself —
`apply_cut_move` checks only per-hub guards), `rescue_scan`/
`verify_escape` (the escape search and its adversarial verifier),
`stuck_configs`, `census_layers`, `census_cases`,
`t2_illegal_at_double`.  Exact integers over GF(2); rngs seeded per
mode, seeds printed; no `set` printed; nothing samples a placement
(§(K-clos) (AC-9)).  No pool is new (fresh subsamples of
`gcap.pool_specs` at this driver's own seeds, disclosed;
NKp(6)/NK55(6)/NKo2v are GPSA's commissioned constructions, reused).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --stuck     #  ~5 s  (GR-46) at 769 pairs + n = 30; (GR-47) at 6220 maps; stuck census + profiles; the n = 30 hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --cases     #  ~3 s  K1/K2/K3 per stuck config; 148/148 coverage; the doubly-blocked kill asserted
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --opt       #  ~3 s  |δ| at parity-optimal maps; exact d_par/d_adm/gap; W3/NKo2v pins
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --adv       #  ~1 s  four F13 controls, each must-reject/-fire with a negative control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gdesc.py --validate  # ~10 s  all four in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-46): transit move legal, lands on `m′`, the `c′`-law | `--stuck` | 769 random pairs: distinct-hub/dart-off guards, target sum asserted a cut via `cut_side`, `m₃ == m′`, `c + χ ∈ sols`; the n = 30 NKp(6) demo |
| (GR-47): bijection + pattern formula | `--stuck` | ALL 6220 censused parity maps round-tripped; `X ∈ Φ` via `mu_in_phi`; `φ` injectivity, `T`-matching, hub partition, formula per odd branch — each an assert |
| (GR-48)(i): the reduction criterion | `--cases`, `--stuck` | every rescue's `\|δ\|` recomputed from the applied move (never from the flip prediction); best-reduction histogram `(2, 0): 148` |
| (GR-48)(iii): the doubly-blocked kill | `--cases`, `--stuck` | `t2_illegal_at_double` asserted at every doubly-blocked majority branch; the two n = 30 witnesses' exhaustive 0-reducer {T1, T2} scans |
| (GR-48)(iv): K3 legal + rescuing | `--stuck`, `--cases` | target sum = `∂(S)` asserted a cut; both witnesses rescued to `\|δ\| = 0`; 16 census configs fire K3 |
| the stuck census + profiles | `--stuck` | full-`3^n` censuses; 148 reproduced (W3M 12, W3 120, NKo2v 16); profile histogram |
| the n = 30 stuck hunt | `--stuck` | dp_walk samples, budgets/caps printed; a CAPPED sample, disclosed as such |
| (b′)'s first half (`\|δ\|` at optimum) | `--opt` | exact per-shape min over optimal maps; `{0: 92, 2: 2}`; gap ≤ 2 asserted (HEADLINE otherwise); W3/NKo2v pins + `min_dev` cross-check |
| doctored escape must-reject | `--adv` | `verify_escape` rejects a legal non-reducing move; the true rescue passes |
| local-demotion discriminator must-fire | `--adv` | a T1-only restricted scan of a real stuck config fires (synthetic restriction, disclosed); the full scan does not (negative control) |
| doctored transit must-reject | `--adv` | one swapped target → target sum NOT a cut → rejected; the undoctored set passes |
| E1 clause (v) discriminator | `--adv` | impossible predicate (`na = nb + 1`, `δ` even): the CAPPED search reports a CAP, FULL enumeration reports genuine `∞` (synthetic mock, disclosed); 984-balanced negative control |
| the uniform statements | — | entry 5's balance half / input (X) are theorem gaps; not driver-testable |

**Determinism.**  `--validate` was re-run by the coordinator at
`PYTHONHASHSEED` 0 and 999 (both exit 0, ≈10 s): the outputs are
**byte-identical including the wall-clock lines**.

**Scratch probes (README's standing rule).**  None retained: every
figure above is produced by a committed driver mode.  (Development
iterations — placeholder asserts in the doubly-blocked block replaced
by `t2_illegal_at_double`, the doctored-transit control generalized to
search doctorable positions — changed no mathematics; the final driver
re-derives everything.)

---

### Confidence verdict (Steps G63–G67)

| | claim | standing |
|---|---|---|
| **(GR-46)** | one-move transitivity of the legal family | **proven-informally** (3-line star-relation proof; certified at 769 pairs + n = 30) |
| (GR-46) Cor. 1 | descent lemma (full family) ⟺ entry 5's balance half | **proven-informally** — the stuck case as posed is NOT a smaller residual |
| (GR-46) Cor. 2 | full-family demotion ⟺ E1(v); demotion is a local-catalogue notion | **proven-informally** |
| **(GR-47)** | the (X, φ, T) normal form + pattern formula | **proven-informally** (round-tripped at all 6220 censused maps) |
| **(GR-48)**(i)–(iii) | the reduction criterion; K1/K2 mechanics; the doubly-blocked {T1, T2} kill | **proven-informally** (the kill asserted mechanically everywhere it applies) |
| (GR-48)(iv) | K3 pair-star legality + per-instance rescue | legality **proven-informally**; rescue **measured** (every instance ever tried, incl. both witnesses, to `\|δ\| = 0`) |
| the {T1, T2} descent route | rescue universality of the landed catalogue | **DEMOTED by witness** — two n = 30 all-doubly-blocked stuck configs defeat every {T1, T2} move; the 148/148 record was a small-shape artifact |
| the descent lemma, stuck case | | **OPEN — RESHAPED**: equivalent to balance existence ((GR-46) Cor. 1); the extended {T1, T2, K3} catalogue unbeaten but its uniformity needs input (X) |
| entry 5, half 2 / whole | | **true-modulo-named-gap / OPEN — NOT a HIT; E3 NOT armed** (the gap = input (X): balance existence in the (GR-47) normal form) |
| **(b′)** | `d_adm − d_par ≤ 2` | **OPEN — supported, decomposition instantiated**: `\|δ\|` at parity-optimal maps `{0: 92, 2: 2}` (its named unmeasured half, now measured); gaps `{0: 92, 1: 2}`; 0 mechanism violations |
| **(GR-15)** | | **OPEN — unchanged in both directions.**  No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.**  The
same side as TCOL's through GPSA's: colourings of fixed graphs and
exact GF(2)/matching computations on constructed configurations, never
`PencilNondegFeasible G`; no rank is computed anywhere in this pass;
no σ-fixed witness is read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G63–G67)

*(i)* **Discharging input (X)** — a matching-flexibility proof of
balance existence in the (GR-47) normal form (toggle lemmas +
1-extendability / Plesník-type inputs, the `2k = 2` dichotomy first)
upgrades entry 5 to PROVEN and **arms E3** (an (a′) HIT would then
fire it; never before).  *(ii)* **A shape defeating the extended
{T1, T2, K3} catalogue** — demotes the extended local route too
(entry 5 untouched); by (GR-46) Cor. 2 only a **full-family** defeat
would mean more, and that is exactly `d_adm = ∞` = E1(v).
*(iii)* **A `d_adm = ∞` shape at FULL enumeration** — E1 clause (v),
the arc's one unconditional escalation; nothing of the kind was seen
(every cap reported as a cap).  *(iv)* **A balance gap > 2** — refutes
(b′); none anywhere (assert armed).  *(v)* **A parity-optimal map
floor `\|δ\| > 2` at some shape** — breaks the first half of (b′)'s
decomposition; none at 94 censused shapes (a measured negative at
these shapes, not a proof).  *(vi)* **A cheap steering proof at
`2k = 2`** (route note (b)) — would settle the minimal odd stratum of
entry 5 outright and calibrate the general (X) attack.

---

### Steps G68–G73 (2026-08-19, direction GBAL) — input (X) is **DISCHARGED**: **(GR-49)** replaces the whole (c, m)/coset/SDR/matching apparatus by ONE BIT PER BRANCH (parity-consistent configurations = **admissible dart colourings**, and the odd-branch pattern is literally that bit read on the odd branches); **(GR-50)** turns balance into a **degree-constrained orientation** of the even branches, decided EXACTLY in polynomial time; **(GR-51)** collapses its two-sided Hall condition to a **local weight inequality** whose only negative term sits at hubs carrying two odd branches of the same colour; **(GR-52)** proves by a **parity contradiction** that at most one such hub per side is harmless; **(GR-53)** proves by exhaustion over all maximal constraint structures that a balanced pattern with at most one such hub per side ALWAYS exists — and **(GR-54)** chains the five into a **THEOREM**: every connected cubic loop-free hub multigraph with evenly many `2k ≤ 6` odd branches carries a balanced admissible configuration. **Entry 5 is PROVEN in BOTH halves** (the parity half falls out — an admissible colouring IS a parity-consistent map), so **E3 is ARMED but does NOT fire** ((a′) is open); TERMINATION clause **E1(v) is now provably unfirable at `Λ = ∅`, `D = 0`**; the (GR-45)/(GR-46)/(GR-47)/(GR-48) apparatus is **subsumed, not contradicted**; route note (b)'s `2k = 2` dichotomy is **CORRECTED** (the exceptional side is the parallel pair, a *cycle*-space condition — not a 2-edge cut) and shown **VACUOUS at habitat shapes** — **(GR-15) stays OPEN, no gap-map status move on `hK` itself**

Answering `notes/Pencil-fanout-archive.md` §"Fifteenth direction — GBAL":
**input (X) — balance existence in the (GR-47) normal form**, the
residual GDESC named when (GR-46) Cor. 1 closed the move-availability
route. Rank-free throughout: no mode imports or calls
`gexist.fully_good_rank`, and no `d_fg` claim is made anywhere ((a′)
is direction GLAW's target this wave; the one (a′)-relevant by-product
is *reported* below, not developed). Read against *Steps G63–G67*
((GR-46)–(GR-48)), *Steps G58–G62* ((GR-44), (GR-45)) and *Step G44*
((GR-37)).

***Notation, inherited unchanged.*** `δ` is the odd-branch imbalance
`a − b` and nothing else; **cuts are written `∂(S)`**. `O` is the set
of odd branches, `2k = |O| ≤ 6` and even (*Step G53*(ii)); `τ =
[ℓ even] ∈ GF(2)^E`; `Φ = τ + Cut(G°)`; `m` a minority-dart map, `c`
its potential. **New in this pass and used throughout: `z ∈ GF(2)^E`,
one bit per branch** — see *Step G68*. A branch is **even**/**odd**
according to `ℓ`; "A" is colour 0 and "B" is colour 1, and the global
A↔B swap is `z ↦ z + 𝟙`.

**Step 0 pin (mandatory, discharged before any derivation).**
(GR-37)(i)/(ii) in full (the (c, m) model, the per-branch equation
`c(u) ⊕ c(w) = τ_β ⊕ [m(u) ∈ β] ⊕ [m(w) ∈ β]`, exactly two
`c`-solutions at fixed `m`, the A↔B swap swapping the balance counts).
(GR-41) (`Φ = τ + Cut(G°)`). (GR-44) in full (Hall automatic;
`d_par(M) = w_M` exact; the parity space nonempty at every habitat
shape) — **consumed as the quantitative record, and *re-derived only in
its nonemptiness half* below; the `d_par(M) = w_M` formula is
untouched.** (GR-45) in full (the legal-move calculus, T1/T2, the
two-end-consistent flip formula). (GR-46) in full (one-move
transitivity; Cor. 1 *the descent lemma over the full family IS the
balance half*; Cor. 2 *a full-family demotion witness exists iff
`d_adm = ∞`*). (GR-47) in full (the `(X, φ, T)` normal form, the
pattern formula, and its three named freedom axes). (GR-48) in full
(the reduction criterion, K1/K2, the doubly-blocked kill, K3, and the
two realized n = 30 witnesses). *Step G53* (`2k ≤ 6`, evenly many;
balance vacuous at all-even shapes). The measured record with its
qualifiers: entry 5 exhaustive at 97 shapes; the stuck census 148; the
NKp(6) hunt a **CAPPED sample**; (b′) gaps `{0, 1, 2}`; (GR-4′) covers
no habitat block.

---

### Step G68 — (GR-49): the z-form — parity-consistent configurations are exactly the admissible dart colourings, and the odd-branch pattern IS the colouring

**Why the pass starts here.** (GR-47) is a bijection onto triples
`(X, φ, T)` whose three coordinates are *coupled*: `X` must lie in a
coset, `φ` must be an SDR, `T` must perfectly match what `φ` leaves
over. Every toggle GDESC could name had to move one coordinate while
repairing the other two, which is why its route notes end at
"1-extendability / Plesník-type inputs on `H(X, φ)`". The observation
that unlocks the problem is that the coupling is an artifact of the
coordinates.

> **(GR-49)** *(proven; machine-certified by an exhaustive round-trip
> at 4923 shapes / 425 762 configurations — every `(m, c)` of the FULL
> `3^n` census at both potentials — with the FULL `2^M` admissible-`z`
> cube enumerated and matched exactly at 136 of them; `--zform`)*
>
> Let `G°` be a cubic loop-free hub multigraph, `τ_β = [ℓ_β even]`.
> For `z ∈ GF(2)^E` define the **dart colour** at the end `(v, β)` by
> > `ζ(v, β) = z_β` if `v` is `β`'s first end, `z_β ⊕ τ_β` if its
> > second.
>
> Call `z` **admissible** if no hub sees three equal dart colours.
> Then
>
> **(i)** `z ↦ (m, c)` with `c(v) =` the majority dart colour at `v`
> and `m(v) =` the minority dart, is a **bijection** from admissible
> `z` onto pairs `(m, c)` with `m` parity-consistent and `c` one of its
> two potentials; the inverse is
> `z_β = c(u_β) ⊕ [m(u_β) = (β, 0)]`. The global A↔B swap is
> `z ↦ z + 𝟙`.
>
> **(ii)** For every **odd** branch `γ`, `pattern(γ) = z_γ`
> **identically**. Balance is therefore `wt(z|_O) = k`.

*Proof.* A branch imposes `ζ(u, β) ⊕ ζ(w, β) = τ_β`, which is exactly
(GR-37)(i)'s per-branch equation once `ζ(v, β) := c(v) ⊕ [m(v) ∈ β]`;
so the branch equations say precisely that the dart colours are the
`ζ` of some `z`, with `z_β` the first-end value. A hub's constraint in
the (c, m) model is that exactly one of its three darts differs from
`c(v)` — for three bits that is exactly "not all three equal", and it
determines `c(v)` (the majority) and `m(v)` (the minority). Parity
consistency (`μ(m) ≡ τ mod Cut`) is *equivalent* to solvability of the
branch system, hence automatic once `z` exists, and conversely every
parity-consistent `(m, c)` produces such a `z`. For (ii), `τ_γ = 0` at
an odd branch, so both its darts carry `z_γ`, and the odd-branch
majority is by definition that common end-dart colour. ∎

**What this absorbs.** The coset `Φ`, the representative `X`, the SDR
`φ`, the complementary perfect matching `T` and (GR-47)'s pattern
formula are all recovered from `z`: `X = supp(μ(m)) = {β : exactly one
end darts on β}`, and `χ_X = τ + ∂(y)` with `y = c`. **There is no
side condition left to maintain** — the *only* constraint is the
per-hub "not all three equal". In particular:

- **(GR-45)'s legal moves become flip sets** *(proven; asserted
  EXHAUSTIVELY over 284 704 (admissible `z`, flip set) pairs at 7
  shapes — all `2^M` subsets at each — `--zform`)*. `F ⊆ E` carries an
  admissible `z` to an admissible `z + χ_F` **iff at every hub**
  > `[m(v) ∈ F] = [|F ∩ star(v)| ≥ 2]`,
  i.e. iff every hub of `F`-degree 1 meets `F` in a **majority**
  branch and every hub of `F`-degree 2 has its **minority** branch in
  `F`. *Proof:* at a hub the three dart colours are `(a, ā, ā)` with
  `a` on `m(v)`; flipping `F ∩ star(v)` makes them equal exactly when
  `F ∩ star(v)` is `{m(v)}` or `star(v) ∖ {m(v)}`, which is the
  negation of the displayed condition. ∎ T1 (`F` = one dart-free
  branch) and T2 (`F` = a star) are the two smallest instances; K3 is
  the pair-star instance.
- **(GR-46) becomes a triviality.** Any two admissible `z`, `z′`
  differ by `F = supp(z + z′)`, which is legal by construction. The
  one-move transitivity theorem is the *definition* in these
  coordinates. (This corroborates (GR-46); it does not weaken it —
  what (GR-46) proved is that the calculus has no smaller residual,
  and that reading stands.)
- **The freedom axes GDESC had to keep in step are gone.** Toggling
  `z_γ` at a single branch is legal exactly when `γ` carries no dart —
  which is (GR-45)(iii)'s free-T1 case, re-derived in one line and
  asserted equal to it at 5016 single-branch flips (`--zform`).

**Certification.** `--zform` runs the whole `Λ = ∅`, `D = 0` pool
behind the (GR-25) cut criterion — **4920 habitat shapes, exhaustive,
not a subsample** — plus W3M/W3/NKo2v. At every shape each `(m, c)` of
`gpsa.parity_census`'s full `3^n` enumeration is mapped to a `z`, the
admissibility, the round-trip and `pattern = z|_O` are asserted, and
the count of distinct `z` is asserted equal to twice the number of
parity-consistent maps. At 136 shapes the full `2^M` cube is
enumerated and matched set-for-set, closing the surjectivity half. At
7 small shapes the flip-set characterization above is asserted over
**every** (admissible `z`, `F ⊆ E`) pair — 284 704 of them.

---

### Step G69 — (GR-50): balance is a degree-constrained orientation problem — an EXACT polynomial decision procedure for entry 5

> **(GR-50)** *(proven; the oracle agrees with the exhaustive `2^M`
> `z`-cube decision at **all 4920** pool habitat shapes, 0
> disagreements, and every certificate it emits is re-verified through
> `gorient.cm_solve` / `gorient.odd_balance` and accepted by
> `cflank.admissible`; `--oracle`, `--thm`)*
>
> Fix a colouring `p : O → {A, B}` of the odd branches. Write, per hub
> `v`, `q_v` for the number of odd darts at `v`, `o_v` for the number
> of **A**-coloured ones, and `d_v = 3 − q_v` for the number of even
> branches at `v`. Then an admissible `z` with `z|_O = p` exists **iff
> the even branches admit an orientation** (head = the branch's A-end,
> which is the meaning of its `z`-bit) with
> > `l_v := max(0, 1 − o_v) ≤ indeg(v) ≤ min(d_v, 2 − o_v) =: u_v`
>
> at every hub. Consequently **balance holds at the shape iff some
> balanced `p` (`|p^{-1}(A)| = k`) admits such an orientation** — a
> decision over at most `C(6, 3) = 20` patterns, each a
> degree-constrained orientation feasibility test.

*Proof.* An **odd** branch has `τ = 0`, so both its darts carry `z_γ`:
it contributes 2 darts of the colour `p(γ)`, at its two ends. An
**even** branch has `τ = 1`, so its two darts carry opposite colours:
it contributes exactly **one** A-dart, at the end selected by its
`z`-bit — i.e. choosing `z` on the even branches *is* orienting them,
head = the A-end. The number of A-darts at `v` is therefore
`o_v + indeg(v)`, and (GR-49)'s hub condition "not all three equal" is
`1 ≤ o_v + indeg(v) ≤ 2`. Rearranging, and intersecting with the
trivial `0 ≤ indeg(v) ≤ d_v`, gives the stated bounds. ∎

**The decision procedure, and what it replaces.** The feasibility test
is a bipartite assignment with two-sided vertex capacities, solved
here by augmenting paths (`assign_feasible`) in exact integers; it
either returns an orientation — from which `z_of_orientation` builds
the certificate — or returns a hub set violating the two-sided Hall
condition. It is **polynomial in `n`**, so for the first time in this
arc the balance question is decided **exactly at every shape the
harness can build**, with no cap anywhere: *Step G61*'s `n = 30`
verdicts were capped `dp_walk` samples; *Step G65*'s NKp(6) hunt was a
capped sample; the census legs were `3^n`-bounded to `n ≤ 10`. The
oracle settles NKp(6), NK55(6), NKo(6), NK(6) at `n = 30` and the same
four families at `n = 40, 50, 60` **exactly** (*Step G72*).

**Two immediate structural readings, both used later.**

- **`u_v ≥ l_v` fails exactly at a monochromatic triple**: a hub whose
  three branches are all odd and all one colour. Any admissible `z`
  forbids it, and the orientation model reports it as an empty bound
  interval.
- **`u_v = 0` exactly at hubs with `o_v = 2`** (two A-odd darts) or
  `q_v = 3`. Such a hub's even branch — it has at most one — is forced
  to point away from it. Two such hubs joined by an even branch is the
  local obstruction, and *Step G70* shows it is the *only* one, in a
  precise sense.

---

### Step G70 — (GR-51): the weight criterion — feasibility collapses to a local inequality whose only negative term is a monochromatic-pair hub

> **(GR-51)** *(proven; the criterion is asserted **equivalent** to the
> orientation oracle at 7248 (shape, balanced pattern) pairs with all
> `2^n` hub sets scanned per pair — 0 disagreements; `--oracle`)*
>
> **(i) The two-sided Hall condition.** Let `H` be the graph of even
> branches. An orientation with `l_v ≤ indeg(v) ≤ u_v` exists iff
> > (a) `e_H(S) ≤ Σ_{v∈S} u_v` for every `S ⊆ V`, and
> > (b) `Σ_{v∈S} l_v ≤ e_H(S) + ∂_H(S)` for every `S ⊆ V`
>
> (`e_H(S)` = even branches inside `S`, `∂_H(S)` = even branches
> crossing).
>
> **(ii) The local form.** Set `w_A(v) := 2u_v − d_v` and
> `w_B(v) := d_v − 2l_v`. Using the cubic identity
> `2 e_H(S) + ∂_H(S) = Σ_{v∈S} d_v`, (a) and (b) are equivalent to
> > `Σ_{v∈S} w_A(v) + ∂_H(S) ≥ 0` and `Σ_{v∈S} w_B(v) + ∂_H(S) ≥ 0`
>
> for every `S ⊆ V`.
>
> **(iii) The weight table.** With `b_v := q_v − o_v`,
> `w_A(v) = 3 − q_v` when `b_v ≥ 1` and `1 − o_v` when `b_v = 0`;
> `w_B` is the same with `o ↔ b`. Explicitly
>
> | `q_v` | colours of the odd darts | `w_A(v)` |
> |---|---|---|
> | 0 | — | `+1` |
> | 1 | A | `0` |
> | 1 | B | `+2` |
> | 2 | A A | **`−1`** |
> | 2 | A B or B B | `+1` |
> | 3 | not monochromatic | `0` |
>
> So **`w_A(v) = −1` exactly at a hub carrying two odd branches, both
> coloured A** ("an A-**monochromatic-pair hub**"), and `w_A(v) ≥ 0` at
> every other hub; symmetrically for `w_B`.

*Proof.* (i) Necessity is immediate (count the edges assigned inside
`S`; and dually). Sufficiency is the augmenting argument the driver
implements, in two phases. *Phase 1 (upper bounds).* Start from an
arbitrary assignment of each even branch to an endpoint. While some
`v` has `load(v) > u_v`, let `R` be the set reachable from `v` by
"an edge assigned to `x ∈ R` puts its other end in `R`". If some
`y ∈ R` has `load(y) < u_y`, push along the path: `load(v)` drops,
`load(y)` rises, everything else is unchanged. If not, every `y ∈ R`
has `load(y) ≥ u_y`, and **every edge assigned to a vertex of `R` lies
inside `R`**, so `e_H(R) ≥ Σ_R load ≥ Σ_R u + 1`, violating (a).
*Phase 2 (lower bounds).* Now while some `v` has `load(v) < l_v`, let
`R` be the set reachable by "an edge incident to `x ∈ R` and assigned
to its other end `y` puts `y` in `R`". If some `y ∈ R` has
`load(y) > l_y`, pull along the path: `load(v)` rises by 1 — and stays
`≤ u_v`, since `load(v) < l_v ≤ u_v` — `load(y)` drops by 1 and stays
`≥ l_y`, and no other load moves, so phase 1's work is preserved. If
not, every edge **incident** to `R` is assigned inside `R`, so
`Σ_R load = e_H(R) + ∂_H(R)` while `Σ_R l ≥ Σ_R load + 1`, violating
(b). Both potentials `Σ(load − u)⁺` and `Σ(l − load)⁺` strictly
decrease, so the process terminates. (This is the classical
degree-constrained orientation criterion — Hakimi 1965, *On the
degrees of the vertices of a directed graph*, J. Franklin Inst.
**279**(4), 290–308, which determines all orientation out-degree
sequences of a graph; the two-sided form used here is proved above in
full so that nothing in this chain rests on a citation.)

(ii) is the substitution; (iii) is the case analysis of
`u_v = min(d_v, 2 − o_v)` against `d_v = 3 − q_v`. ∎

**Reading.** Every hub *helps* except a monochromatic-pair hub, and
that hub can be paid for by a single even branch leaving `S`. The
whole balance question has become: *can the odd branches be split
half-and-half so that monochromatic-pair hubs do not cluster?*

---

### Step G71 — (GR-52) and (GR-53): one monochromatic-pair hub per side is free (a parity contradiction), and one always suffices (a finite exhaustion)

> **(GR-52)** *(proven; its hypothesis is asserted on the whole
> `2k = 2` stratum — 0 monochromatic-pair hubs over 5444 (shape,
> pattern) pairs — and the implication is exercised at every shape of
> `--split`/`--thm`, where the split (GR-53) produces is asserted
> orientation-feasible)*
>
> Let `p` be a colouring of `O` with **no monochromatic triple** and
> **at most one monochromatic-pair hub on each side**. Then both
> (GR-51) inequalities hold, so the orientation is feasible.

*Proof.* No monochromatic triple gives `o_v ≤ 2` and `b_v ≤ 2`
everywhere, so `l_v ≤ u_v` and the criterion applies. Write
`F(S) := Σ_{v∈S} w_A(v) + ∂_H(S) = Σ_{v∈S} (w_A(v) + b^{out}_v)`,
where `b^{out}_v` is the number of even branches at `v` leaving `S`
(each crossing even branch has exactly one end in `S`). By the
(GR-51)(iii) table each summand is `≥ 0` except at an
A-monochromatic-pair hub, where `d_v = 1` and the summand is `−1` if
its single even branch stays inside `S` and `0` if it leaves. With at
most one such hub, `F(S) ≥ −1`.

Suppose `F(S) = −1`. Then **every** summand is `0` except one, which
is `−1` at the unique A-monochromatic-pair hub `v₀` whose even branch
stays inside `S`. Inspecting the table, a summand can be `0` only at
`v₀`'s kind (excluded — there is only one such hub), at a hub with
`q_v = 3` (`d_v = 0`), or at a hub with `q_v = 1` whose odd branch is
A and **all** of whose two even branches stay inside `S`. Let
`a_v := d_v − b^{out}_v` be the number of even branches at `v` with
both ends in `S`; then `Σ_{v∈S} a_v = 2 e_H(S)` is **even**. But
`a_{v₀} = 1`, `a_v = 0` at the `q_v = 3` hubs and `a_v = 2` at the
`q_v = 1` hubs, so `Σ_{v∈S} a_v = 1 + 2j` is **odd** — a
contradiction. Hence `F(S) ≥ 0` for every `S`, and symmetrically for
`w_B`. ∎

> **(GR-53)** *(proven by exhaustion; 1 / 44 / 4837 maximal constraint
> structures at `2k = 2 / 4 / 6`, a good balanced split at every one;
> `--split`)*
>
> **(i) The constraint structure.** A shape imposes on `O` a multiset
> `𝒞` of constraints: one **pair** `{γ, γ′}` for each hub carrying
> exactly two odd branches, one **triple** `{γ, γ′, γ″}` for each hub
> carrying three. **Every odd branch lies in at most 2 constraints**,
> because it has exactly two ends. (Equivalently: the pair-graph has
> maximum degree ≤ 2, so it is a disjoint union of paths and cycles.)
>
> **(ii) The lemma.** For every such `𝒞` on `2k ∈ {2, 4, 6}` elements
> there is a **balanced** split `O = A ⊔ B` (`|A| = |B| = k`) with **no
> monochromatic triple** and **at most one monochromatic pair on each
> side**.

*Proof.* Adding constraints can only increase a split's
monochromatic counts, so it suffices to check **maximal** structures —
those to which no further constraint can be added, i.e. those in which
at most one element still has spare degree. Every `𝒞` extends to a
maximal one (keep adding a pair while two elements have spare degree),
and a good split for the extension is a good split for `𝒞`. The
maximal structures on `2k ≤ 6` labelled elements are a **finite,
enumerable** family — 1 at `2k = 2`, 44 at `2k = 4`, 4837 at `2k = 6`
— and `--split` exhibits a good balanced split at every one. ∎

**The bar is tight, not slack** (`--adv` (5)): at `2k = 4` the
pair-structure `{{γ₂,γ₃}, {γ₂,γ₄}, {γ₃,γ₄}}` (an odd-branch triangle
of monochromatic-pair hubs) admits **no** balanced split with zero
monochromatic pairs on both sides — so "≤ 1 per side" cannot be
strengthened to "0", and (GR-52)'s parity argument is doing real work
rather than decorating a vacuous hypothesis. The worst total
monochromatic-pair count over the maximal structures is 0 / 1 / 2 at
`2k = 2 / 4 / 6`.

**The structures are realized, not hypothetical.** Over the 4920-shape
pool the `(2k, #pairs, #triples)` profiles that actually occur are
`{(2,0,0): 1270, (2,1,0): 1116, (2,2,0): 9, (4,0,1): 62, (4,1,1): 468,
(4,2,0): 744, (4,2,1): 90, (4,3,0): 728, (4,4,0): 126, (6,0,4): 1,
(6,2,2): 66, (6,3,2): 12, (6,4,1): 78, (6,6,0): 10}`, and the
"≤ 2 constraints per odd branch" clause is asserted at every one.

---

### Step G72 — (GR-54): the balance theorem — input (X) discharged, entry 5 PROVEN, E3 ARMED

> **(GR-54)** *(proven; the theorem's own construction — not a search —
> produces a balanced certificate at all 4920 pool habitat shapes, at
> W3M/W3/W4/W5/NKo2v and at the 16 necklace members `NK/NKo/NKp/NK55`
> at `m = 6, 8, 10, 12` (`n = 30..60`), and at 1680 seeded random cubic
> bridgeless shapes with NO habitat gate, 857 of them with the odd
> branches deliberately CONCENTRATED on one hub's neighbourhood. Every
> pool certificate is re-verified through `cm_solve`/`odd_balance` and
> **accepted by `cflank.admissible`**, the (GR-37)(i) ground truth;
> `--thm`)*
>
> Let `G°` be a connected cubic loop-free hub multigraph whose odd
> branches number `2k` with `2k ≤ 6` and `2k` even. Then `G°` carries a
> **balanced admissible configuration** — equivalently, a
> parity-consistent minority map with a potential whose odd-branch
> majority pattern splits `k`–`k`.

*Proof.* Read off the constraint structure `𝒞` of (GR-53)(i). By
(GR-53)(ii) choose a balanced `p` with no monochromatic triple and at
most one monochromatic-pair hub per side. By (GR-52) both (GR-51)
inequalities hold for `p`, so by (GR-51)(i) the even branches admit an
orientation with `l_v ≤ indeg(v) ≤ u_v`. By (GR-50) that orientation,
together with `p`, is an admissible `z` with `z|_O = p`; by
(GR-49)(i)–(ii) it is a parity-consistent `(m, c)` whose pattern is
`p`, which is balanced. ∎

**What (GR-54) buys, exactly — and what it does not.**

- **Route-ledger entry 5 is PROVEN, in both halves.** Half 2
  (balance) is the theorem. Half 1 (parity) comes with it: an
  admissible `z` **is** a parity-consistent map, so the parity space
  is nonempty at every shape in the theorem's scope. This
  **re-derives (GR-44)'s nonemptiness half by a different route and
  without Petersen** — bridgelessness is not used anywhere above —
  and leaves **(GR-44)'s quantitative content (`d_par(M) = w_M`, the
  automatic Hall step, the SDR construction) completely untouched and
  still the record**.
- **The hypotheses are weaker than the habitat.** Connected, cubic,
  loop-free, `2k ≤ 6` even. *Step G53*(ii) supplies `2k ≤ 6` and
  evenness at every `Λ = ∅`, `D = 0` habitat shape from the excess law
  (`Σ(ℓ − 2) = 6` with `ℓ ≥ 2`), so the theorem covers exactly what
  entry 5 is about — and rather more: the seeded random sweep
  confirms it at shapes with no habitat certificate at all.
- **TERMINATION clause E1(v) is now provably unfirable at `Λ = ∅`,
  `D = 0`** — *given that every such habitat shape satisfies (GR-54)'s
  hypotheses, which it does: `D = 0` **is** cubicity, `cubic_habitat`
  rejects loops, class shapes are connected, and *Step G53*(ii) plus
  the excess law give `2k ≤ 6` even.* `d_adm = ∞` means no admissible
  colouring exists; (GR-54) says one always does. By (GR-46) Cor. 2 the same statement
  says that **no configuration defeats every legal (GR-45) move** — so
  the full-family demotion branch is closed too, exactly as GDESC
  predicted it would be if entry 5 held.
- **E3 is ARMED and does NOT fire.** Per the standing reading, an
  entry-5 HIT arms E3; E3 fires only if **(a′)** subsequently HITs,
  never before. **(a′) was not attempted here** (it is GLAW's target
  this wave).
- **It does NOT close (GR-15)**, and it exhibits **no g-flank**. The
  pass is rank-free; no `d_fg` claim is made; class uniformity of the
  escape is untouched, as it has been by every dispatch of this arc.
- **It does not move (b′).** (b′) bounds the *size* of the balance
  gap `d_adm − d_par ≤ 2`; (GR-54) proves `d_adm < ∞` and says nothing
  about the gap. (b′) stays OPEN, supported, exactly where GDESC left
  it.
- **Riders, verbatim.** Everything is at **`Λ = ∅`**, **`D = 0`**, and
  **modulo (GR-4′)** where a closure chain is concerned; the
  **`Λ ≠ ∅` closed-form analogue** and the **`D > 0` lift** stay
  **unswept**.

**The (GR-45)–(GR-48) apparatus is subsumed, not contradicted.** Every
landed statement of *Steps G58–G67* survives verbatim; what changes is
that they are no longer the route. (GR-46)'s transitivity is a
one-liner in the z-form (*Step G68*), and its Cor. 1 is what made this
pass abandon move-availability and attack existence — the equivalence
was the load-bearing input, not an obstacle. (GR-48)'s catalogue and
its two realized n = 30 demotion witnesses stay exactly as measured;
they demoted a *bounded local route*, and (GR-54) shows the
statement that route was chasing is true. **No landed figure moves.**

**A recorded CORRECTION to *Step G65*'s route note (b)** (the marker
precedent of *Step G56*/*Step G60*; scoped exactly, and it touches no
measurement). Route note (b) reads: *"for `2k = 2` the cut-space
projection onto the two odd coordinates is onto unless `{γ₁, γ₂}` is a
2-edge cut (then every `X ∈ Φ` meets it evenly)"*. The named exception
is **wrong**, and the correct statement is:

> The projection `Φ → GF(2)^{{γ₁, γ₂}}` fails to be onto **iff
> `γ₁` and `γ₂` are PARALLEL** (a pair of branches with the same two
> ends). *Proof:* the projection of `Cut(G°)` misses a direction iff
> the corresponding vector lies in `Cut^⊥ = Cycle(G°)`; `χ_{γ}` is a
> cycle-space element only for a loop, and `χ_{γ₁} + χ_{γ₂}` is one
> iff `{γ₁, γ₂}` is an even subgraph, i.e. iff the two are parallel. ∎

`--two` asserts `onto ⟺ not parallel` **shape by shape** over 2722
`2k = 2` shapes (2707 onto, 15 not onto, all 15 parallel), and finds
`{γ₁, γ₂}` a **2-edge cut** at 5 of the 2722 — a *different* set, so
the two conditions do not coincide and the route note names the wrong
one. The intuition behind the note is real but lives on the **other**
axis: a 2-edge cut `∂(A)` in a cubic graph forces `|A|` even, so every
perfect matching contains **both or neither** of its two branches —
that is a constraint on the `T`-matching coordinate, not on the
`X`-shift coordinate.

**Both readings are moreover VACUOUS at habitat shapes** (`--two`, 0
and 0 over the 2402 habitat/named `2k = 2` shapes; the underlying
argument): if `∂(S) = {γ₁, γ₂}` with `γ₁, γ₂` odd, then bridgelessness
makes both sides connected with `≥ 2` hubs, so the (GR-25) cut
criterion `2∂(W) + exc(E(W)) ≥ 7` gives `exc ≥ 3` on **each** side,
while `exc(γ₁) + exc(γ₂) ≥ 2` — total `≥ 8 > 6`, contradicting the
excess law. And a parallel odd pair at `n ≥ 4` is a 2-edge cut of
exactly that kind. The `n = 2` theta shapes are the whole parallel
exception, and (GR-54) covers them like everything else. **The
dichotomy is therefore moot: the minimal odd stratum is settled by
(GR-54) with no case split at all**, and `--two` records the
`2k = 2` specialization — `w_A ≡ 0` identically, since a balanced
pattern at `2k = 2` has a single A-odd branch and no hub can carry two
A-odd darts, so (GR-52)'s hypothesis holds **vacuously** on the whole
stratum (0 monochromatic-pair hubs over 5444 (shape, pattern) pairs).

**One (a′)-relevant by-product, reported and NOT developed** (the
spec's bar): the z-form makes the fully-good layer's question
*"which admissible `z` also has both ruling classes generic-`dim Z = 0`"*
a question about the **same** one-bit-per-branch object that (GR-50)
decides by orientation. Whether the fully-good condition is likewise a
degree/flow condition on the even branches is **not attacked here** and
is exactly the kind of input (a′) has been missing. Recorded for GLAW /
the successor.

---

### Step G73 — where this leaves entry 5, E3 and the (GR-15) line (hand-off)

- **The route ledger** (statuses as this landing leaves them):
  **Entry 5 — PROVEN, both halves ((GR-54); half 1 also re-derived
  without Petersen, half 2 the theorem).** It is a **HIT**. Entry 1
  untouched — **(a′) deliberately not attempted**, and it remains
  entry 1's primary with no bar. Entries 2–4 unchanged.
- **TERMINATION check** (coordinator-run at this landing; the draft's
  reading): **E1 does NOT fire** — no g-flank; clause **(iv)**
  untouched, the pass being rank-free with no `d_fg` claim anywhere,
  so nothing here found `d_adm < d_fg` finite or infinite; clause
  **(v)** does not fire and, stronger, **(GR-54) proves it can never
  fire at `Λ = ∅`, `D = 0`** (the hypothesis check is spelled out at
  *Step G72*) — `d_adm < ∞` at every shape in scope, so no
  `d_adm = ∞` shape exists to exhibit. Every figure in this pass is
  an **exact decision**, never a cap; the one `∞`-shaped object in the
  driver is the `--adv` (6) discriminator, which checks the oracle
  against the exhaustive `2^M` cube so that an `∞` verdict would be a
  genuine `∞`. **E2 does NOT fire** — (a′) is neither refuted nor
  unprovable-as-posed (it was not attempted), and the ledger has
  entries in state open-with-a-named-dispatchable-attack. **E3 is
  ARMED and does NOT fire** — the target of E3 is **entry 1**, and the
  standing reading is *(a′) + per-shape admissibility already proven ⟹
  E3 fires*: per-shape admissibility is now proven, so **E3 fires on
  the next (a′) HIT and never before**. An entry-5 HIT alone does
  **not** close the `Λ = ∅`, `D = 0` existence target.
- **The sixteenth's natural routing** (a coordinator/user call, not
  made here): **(a′), the `d_fg = d_adm` law** — it is now the *only*
  thing between the arc and E3, it was already entry 1's primary with
  no bar, and this pass hands it a new instrument (the z-form) plus
  the reported by-product above. GLAW is attacking it in this same
  wave; if GLAW HITs, the coordinator's E3 check fires on the pair of
  landings, not on either alone. Behind it: **(b′)** (the balance-layer
  bound, still open, its decomposition's second half now *proven*
  rather than reduced), **(c)** AA-glue realizability at `n_hub ≥ 8`,
  **(d′)** the corner-armed seed hunt.
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**,
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **an entry-5 HIT does
  not close the existence target while (a′) is open**. **(GR-15) OPEN,
  unchanged in both directions; no gap-map status move on `hK` itself
  — the (K-grid) row's *ledger entry 5* clause moves from
  true-modulo-named-gap to PROVEN, and the "five named dispatchable
  attacks" list loses input (X).**
- **(GR-37)(iii)'s flag.** Its parity half was repaired by (GR-44);
  (GR-54) now supplies the **existence** content its balance clause
  asserted, at every habitat shape. Whether that retires the flag in
  full, or only its existence half, depends on what (GR-37)(iii)
  claims *beyond* existence — **a coordinator call at landing; this
  draft does not make it** and leaves the flag as it stands.

---

### Verification (Steps G68–G73)

`notes/scripts/w4/gbal.py` (**new with this pass**; imports — all
read-only — `cflank` (`admissible`, `cubic_habitat`), `gcap`
(`pool_specs`), `gunif` (`WITNESSES`), `gorient` (`cm_colouring`,
`cm_solve`, `odd_balance`, `prep_shape`), `gdev` (`nk_specs`,
`habitat_by_lemma`), `gadm` (`nko_specs`), `gpsa` (`branches_at`,
`is_bridgeless`, `delta_of`, `parity_census`, `pattern_of`,
`nkp_specs`, `nk55_specs`, `nko2v_specs`). **Rank-free**:
`gexist.fully_good_rank` is never imported or called, and no `d_fg`
claim is made anywhere. Local devices, none shadowing a §1 primitive:
`dart_col`/`z_admissible`/`z_to_map`/`map_to_z`/`z_pattern` (the
(GR-49) bijection), `flip_legal` (the (GR-45) legality test in
z-coordinates), `bounds_of`/`assign_feasible`/`z_of_orientation`/
`feasible_at`/`balance_oracle` (the (GR-50) decision, with
`assign_feasible` returning an infeasibility **certificate**),
`weight_of`/`weight_criterion` (the (GR-51) local form),
`constraints_of`/`split_cost`/`good_split`/`maximal_structures` (the
(GR-53) combinatorics), `brute_balance` (the exhaustive `2^M` ground
truth), `verify_balanced` (the certificate verifier, routed through
`cm_solve`/`odd_balance`/`cflank.admissible`), `rand_cubic`/
`random_cases` (a seeded **graph** sampler — no placement is drawn, so
§(K-clos) (AC-9) does not apply), `pool_cases`/`named_cases`. Exact
integers over GF(2) throughout; no floating point; rngs seeded per
mode with the seed printed; no `set` printed. **No pool is new**: the
`Λ = ∅`, `D = 0` pool is `gcap.pool_specs` behind `cflank.cubic_habitat`
and is swept **EXHAUSTIVELY** (4920 shapes — no subsample, a first for
this arc); NKp/NK55/NKo2v/NKo/NK are GPSA's and GADM's commissioned
constructions, reused read-only and **extended to `m = 8, 10, 12`**
by the same constructors.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --zform     #  ~8 s  (GR-49) at 4923 shapes / 425762 configs + 136 full 2^M cubes + 284704 flip-set pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --oracle    #  ~4 s  (GR-50) vs the exhaustive cube at all 4920 pool shapes; (GR-51) vs the oracle
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --two       #  ~7 s  the 2k = 2 stratum; the route-note-(b) correction and its habitat vacuity
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --split     #  ~3 s  (GR-52)'s hypothesis; (GR-53) by exhaustion (1 / 44 / 4837 maximal structures)
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --thm       # ~22 s  (GR-54) end to end, incl. n = 30..60 and 1680 random stress
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --adv       #  ~1 s  six F13 controls, each must-reject/-fire with a negative control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gbal.py --validate  # ~43 s  all six in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-49)(i): the bijection | `--zform` | every `(m, c)` of the FULL `3^n` census at both potentials mapped to a `z`, admissibility asserted, round-trip asserted, `#z = 2·#maps` asserted; the FULL `2^M` cube enumerated and matched set-for-set at 136 shapes |
| (GR-49)(ii): `pattern = z\|_O` | `--zform` | asserted against `gpsa.pattern_of` at every one of the 425 762 configurations |
| (GR-49): the (GR-45) legality test in z-coordinates | `--zform` | asserted over ALL `2^M` flip sets at every admissible `z` of 7 shapes — 284 704 pairs; the `\|F\| = 1` case asserted equal to the free-T1 condition at 5016 |
| (GR-50): orientation ⟺ admissible `z` at a pattern | `--oracle` | the oracle's verdict asserted EQUAL to `brute_balance`'s exhaustive `2^M` decision at all 4920 pool shapes |
| (GR-50): the certificate is real | `--thm` | every certificate round-tripped through `cm_solve`, `odd_balance` (`na == nb` asserted) and **`cflank.admissible`** at all 4920 pool shapes |
| (GR-51)(i)/(ii): criterion ⟺ feasibility | `--oracle` | 7248 (shape, balanced pattern) pairs, ALL `2^n` hub sets per pair, verdicts asserted equal; 0 disagreements |
| (GR-51)(iii): the weight table | `--oracle`, `--split` | `weight_of` is the table; its `assert a <= 2` is the monochromatic-triple guard, and the criterion built from it matches feasibility |
| (GR-52): the hypothesis suffices | `--split`, `--thm` | at every shape the (GR-53) split is fed to `feasible_at` and feasibility is **asserted**, never searched for |
| (GR-52) at `2k = 2` | `--two` | 0 monochromatic-pair hubs asserted over 5444 (shape, pattern) pairs; the weight criterion asserted `≥ 0` at 5274 of them over all `2^n` hub sets |
| (GR-53)(i): ≤ 2 constraints per odd branch | `--split` | asserted per odd branch at every odd-carrying pool shape |
| (GR-53)(ii): the exhaustion | `--split` | 1 / 44 / 4837 maximal structures at `2k = 2/4/6`; a good split asserted at every one |
| (GR-53) bar tightness | `--adv` (5) | a structure with NO zero-monochromatic balanced split is exhibited and asserted to exist |
| (GR-54) end to end | `--thm` | the theorem's own chain (split → orientation → `z` → `(m, c)`) run at 4920 pool + 21 named + 1680 random shapes, every step asserted |
| the `n = 30..60` verdicts are EXACT | `--thm`, `--adv` (6) | the decision is the polynomial oracle, not a capped walk; (6) checks the oracle against the exhaustive cube where both are computable |
| the route-note-(b) correction | `--two` | `onto ⟺ not parallel` asserted shape by shape at 2722 shapes; the 2-edge-cut count reported separately (5) to exhibit the non-coincidence |
| the habitat vacuity of both readings | `--two` | 0 parallel odd pairs at `n ≥ 4` and 0 two-odd-branch 2-edge cuts over 2402 habitat/named shapes, both asserted |
| doctored certificate must be rejected | `--adv` (1) | `verify_balanced`'s verdict asserted EQUAL to independent ground truth at all 15 single-bit flips (10 rejected, 5 legitimately accepted) |
| infeasibility must be certified, not silent | `--adv` (3) | `assign_feasible` returns a hub set and the Hall violation `e(R) > Σ hi` is asserted |
| (a′) / `d_fg` | — | **not attempted**; no mode computes a rank |
| (GR-15) / class uniformity | — | untouched; not driver-testable and not claimed |

**Determinism.** `--validate` was run at `PYTHONHASHSEED` 0 and 999
(both exit 0, ≈43.5 s): the outputs are **byte-identical except for the
`[Ns]` wall-clock annotations**, which are inherently
non-deterministic.

**Scratch probes (README's standing rule).** Three exploratory probes
were written during the derivation (the z-form round-trip, the first
orientation oracle, and the first `n = 30`/random sweep). **None is
retained** — each became a mode of the committed driver, and every
figure above is produced by `gbal.py`. No figure in this section comes
from a probe.

---

### Confidence verdict (Steps G68–G73)

| | claim | standing |
|---|---|---|
| **(GR-49)** | the z-form bijection; `pattern = z\|_O` | **proven-informally** (short proof; exhaustive round-trip at 425 762 configurations, full cube matched at 136 shapes) |
| **(GR-50)** | balance ⟺ a feasible degree-constrained orientation at some balanced pattern; the polynomial oracle | **proven-informally** (oracle == exhaustive `2^M` decision at all 4920 pool shapes) |
| **(GR-51)** | the two-sided Hall condition and its local weight form | **proven-informally** (self-contained augmenting-path proof; criterion == feasibility at 7248 pairs over all `2^n` hub sets) |
| **(GR-52)** | ≤ 1 monochromatic-pair hub per side ⟹ feasible | **proven-informally** (parity contradiction; the implication exercised at every shape of `--split`/`--thm`) |
| **(GR-53)** | ≤ 2 constraints per odd branch; the good balanced split always exists | **proven** (finite exhaustion over all maximal structures, machine-verified; the monotonicity reduction is a two-line argument) |
| **(GR-54)** | **the balance theorem — every connected cubic loop-free `G°` with `2k ≤ 6` even odd branches carries a balanced admissible configuration** | **proven-informally** — the chain (GR-53) → (GR-52) → (GR-51) → (GR-50) → (GR-49), every link certified; **input (X) DISCHARGED** |
| **entry 5** | per-shape admissibility, both halves | **PROVEN — a HIT; E3 ARMED, not fired** |
| (GR-44) | `d_par(M) = w_M`, Hall automatic | **untouched**; its *nonemptiness* half re-derived independently (and without Petersen) |
| (GR-45)–(GR-48) | the move calculus, transitivity, the normal form, the escape catalogue | **untouched and subsumed** — every landed statement survives verbatim; (GR-46) Cor. 1 was the input that routed this pass to existence |
| route note (b) | the `2k = 2` dichotomy's exceptional side | **CORRECTED** (parallel pair, a cycle-space condition — not a 2-edge cut) and **VACUOUS at habitat shapes**; the dichotomy is moot |
| **(b′)** | `d_adm − d_par ≤ 2` | **OPEN — unchanged.** (GR-54) proves `d_adm < ∞`, not a gap bound; the decomposition's second half is now a theorem, its first half still measured-only |
| **(a′)** | the `d_fg = d_adm` law | **OPEN — not attempted** (GLAW's target this wave); one z-form by-product reported, not developed |
| **(GR-15)** | | **OPEN — unchanged in both directions.** No flank; no rank computed anywhere; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's through GDESC's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere in this pass; no σ-fixed witness is read as generic
(§(K-clos) (AC-9)), and the only sampler here draws a **graph**, not a
placement.

### What would change this (Steps G68–G73)

*(i)* **An (a′) HIT** — the `d_fg = d_adm` law proven — now **fires
E3**, since per-shape admissibility is proven. It is the only thing
left between the arc and its terminal condition at `Λ = ∅`, `D = 0`,
and it is dispatchable with no bar. *(ii)* **A refutation of (a′) at a
finite witness** (`d_adm < d_fg < ∞`) fires E2's refutation branch with
a named successor, not E1. *(iii)* **A shape with `d_adm < ∞` and
`d_fg = ∞`** is still a g-flank and still fires E1 — (GR-54) closes
clause (v) (`d_adm = ∞`), **not** clause (iv). *(iv)* **A balance gap
`> 2`** refutes (b′); (GR-54) says nothing about it, and none has been
seen. *(v)* **The `Λ ≠ ∅` or `D > 0` analogue.** (GR-54)'s proof uses
cubicity in three places (the `d_v = 3 − q_v` bookkeeping, the
`2 e_H + ∂_H = Σ d_v` identity, and "an odd branch has two ends" in
(GR-53)(i)) and `2k ≤ 6` in (GR-53)(ii)'s exhaustion; a `D > 0` lift
must redo all four, and a shape with more than 6 odd branches falls
outside the exhaustion — **that is where the theorem's boundary is,
and both strata stay unswept by standing rider**. *(vi)* **A fully-good
analogue of (GR-50)** — if the generic-`dim Z = 0` condition were also
a degree/flow condition on the even branches, (a′) would follow the
same route; this pass reports the possibility and does **not** develop
it.

---

### Steps G74–G79 (2026-08-19, direction GLAW) — attack **(a′)** gets **coordinates**, an **exhaustive** verification and a **refuted stronger variant**: **(GR-55)** puts every minority map at deviation distance `d` from a perfect matching `M` in a `(y, Z, φ)` normal form whose parity constraint involves `y` alone — so the whole deviation ladder becomes enumerable and the M-avoiding coset space is an affine space of dimension exactly `n/2 − 1`; **(GR-56)** adds the missing **SPLIT** identity `defect_A(S) − defect_B(S) = δ_S − σ_S` to (GR-32)(i)'s sum, collapsing full-goodness to **ONE inequality per chunk**, `z_mono(S) + |δ_S − σ_S| ≤ cap(S) − 6`, of which the **balance rider is exactly the whole-graph instance** — and makes admissibility and full-goodness **functions of the minority map alone**; **(GR-57)** is the SDR exchange calculus: the optimal stratum factors as a product over the path/cycle components of `supp(y)`, and the **elementary SDR shift is a distance-preserving 2-hub move that CROSSES μ-classes** — the second exchange axis GADM's census named as missing — with a measured **four-rung axis ladder**; **(GR-58)** verifies `d_fg = d_adm` at **ALL 4920 labelled shapes** of the `n_hub ≤ 6` habitat stratum (no subsample, no deviation cap) and at the first **odd-carrying** `n = 30` members NKp(6)/NK55(6), rank-certified at the optimum; **(GR-59)** **REFUTES** the **per-matching** variant of (a′) — 1278 of 24 638 (shape, matching) pairs carry a finite `d_adm(M) < d_fg(M)`, smallest witness at `n_hub = 4` — so `min_M` is **load-bearing** and no (a′) proof may fix its anchor matching; **(GR-60)** names the residual **input (Y)**, a joint matching-and-representative selection statement in the (GR-55) coordinates — **(a′) stays OPEN, NOT a HIT, E3 NOT armed; (GR-15) stays OPEN, no gap-map status moves**

Answering `notes/Pencil-fanout-archive.md` §"Sixteenth direction — GLAW":
**attack (a′), the `d_fg = d_adm` law** — route-ledger entry 1's primary,
the growth-law form's surviving half, **dispatchable with no bar**.
Read against *Steps G53–G57* ((GR-43), entry 5's settlement, the (a′)
census and its named sticking case), *Steps G58–G62* ((GR-44),
(GR-45)), *Steps G63–G67* ((GR-46)–(GR-48) and the cross-μ finding this
direction was handed), and *Steps G43–G47* ((GR-36)–(GR-39)).

***Notation, fixed for this section.*** `δ_S` is an **imbalance**
(GDESC's convention: `#A-majority − #B-majority`), never a cut; cuts are
written `∂(S)`. `z(S)` is the number of degree-2-in-`S` hubs
("interiors") and `z_mono(S)` the number of them whose `S`-dart pair is
monochromatic — equivalently, by (GR-33)(i), whose **minority dart is
the exit dart**; `cap(S) = 2z(S) + exc(S)`. `w_M` is (GR-44)'s minimum
weight of an `M`-avoiding representative of `[τ]`. `dist(m, M)` is the
number of hubs at which `m` differs from the all-`M` prescription.

**Step 0 pin (mandatory, discharged before any derivation; pinned from
the landed bodies, not from the spec's paraphrases).**
**(GR-44)** in full (*Step G58*): `d_par(shape, M) = w_M` exactly; the
Hall/SDR step **automatic** (an `M`-avoiding support has max degree 2 at
every cubic hub, so its components are paths and cycles and head-
assignment along an orientation is an SDR); `M`-avoiding representatives
exist because `span{e_β : β ∉ M} + Cut(G°) = GF(2)^E`; the recorded
Hall-tightness note (cycle components are exactly where `|N(S)| = |S|`);
and the scope — **(GR-37)(iii)'s parity half repaired, its balance
clause STILL statement-beyond-proof**.
**(GR-32)** in full (*Step G38*): the pair identity
`defect_A(S) + defect_B(S) = 2z(S) + exc(S) − z_mono(S)`; the capacity
trichotomy (`cap(S) ≥ 7` at every proper chunk, `cap(E(G°)) = 6`);
whole-graph criticality `defect_A = defect_B = 3` at every **balanced**
colouring; the anti-flank floor; `2N(S) = cap(S) + w_odd(S)`.
**(GR-33)** in full (*Step G39*): the 2-1 dart pattern and the minority
dart; the **save form** `defect_A(S) = N(S) − save_A(S)` with
`save_A(S) = #{interiors v : exit(v, S) = m(v), maj(v) = A} + #{odd
β ∈ S : β B-majority}`; binding needs `save_A ≥ N − 2`; the orientation
form in the all-even case.
**(GR-37)(i)/(ii)** (*Step G44*): the `(c, m)` model, the per-branch
equation, **exactly two `c`-solutions at fixed `m`** (complementary),
and the coordinator-verified sharpening that the A↔B swap **swaps the
balance counts**.
**(GR-41)** (*Step G49*): `Φ = τ + Cut(G°)`, `τ = [ℓ even]`,
`μ(M) = 0` at every perfect matching.
**(GR-46)** (*Step G63*) and its **Corollary 1** — the legal-move family
is one-move transitive, so descent over the full family **is** entry 5's
balance half. The **cross-μ structure** GDESC reported as (a′)-relevant
and deliberately did not develop is this direction's starting point; it
is developed here **only at fixed deviation-optimality** ((GR-57)),
which is a different quantifier and is why it does not touch entry 5.
**(GR-47)** (*Step G64*): the `(X, φ, T)` normal form of **all**
parity-consistent maps. **(GR-55)** below is a **different** normal
form — of the maps at a fixed distance from a fixed anchor matching —
and neither implies the other.
**(GR-28)(i)** (*Step G31*): the defect formula, and (ii) `a = 0`
automatic at `Λ = ∅` — **a different statement from the forest conjunct
of `cflank.admissible`**, which is measured free below, not proven.
**(GR-21)**/*Step G53*: `Σ_β(ℓ_β − 2) = 6`, hence **at most six branches
of length ≥ 3**, at most 6 odd branches, evenly many; balance vacuous at
all-even shapes.
**(GR-36)/(GR-40)**: both charges are **lower** bounds on `defect`, in
both blocks, and their naive sum is FALSE (`max` is the theorem); the
obstruction family is **binding-capable, NOT capacity-tight** — every
"0 fully-hot" figure carries that qualifier (the capable family carries
761 on a 184-shape subsample; (GR-40) prunes 815 → 573, **a prune, not
a zero**).
**The (a′) support as GADM left it**: 133 shapes all at `d ≤ 3` (131
seeded pool subsample + W3 + NK(2), **not** exhaustive) + GADM's fresh
108-shape census + the four NK members at `d` up to 10, rank-certified
at the optimum. **The named sticking case**: fixed-μ fiber exchange is
measurably insufficient (W3: 27/34 optimal μ-classes fully good; one
pool shape likewise), every measured failure at **defect exactly 2**.
**The two stronger variants GADM banned from silent substitution**: the
**per-matching** form of (a′) (*"not what the 133 shapes measure, and
may well be false"* — refuted below, as its own recorded result) and
(b′)'s constant.
**(GR-42)/(GR-43)**: the necklaces; the shift-metric layer is
**UNBOUNDED**, so **do not re-attack a shape-free `d`** — the
bounded-deviation form is refuted as posed and the growth law's
bounded-shift-correction reading with it.
**(GR-4′)'s proven-case boundary** — covers no habitat block; the rider
never dissolves silently.

---

### Step G74 — (GR-55): the deviation normal form — every minority map at distance `d` from a perfect matching is a `(y, Z, φ)` triple, and parity-consistency is a condition on `y` alone

> **(GR-55)** *(proven; the bijection certified against brute force at
> **1300** (matching, distance) cells over W3M, W3 and 48 seeded
> stratum shapes — every parity-consistent map at every distance
> `d ≤ 4` from every perfect matching, in both directions and with
> injectivity asserted; the dimension and parity clauses at 260
> (shape, matching) pairs, `--nf`)*
>
> Let `G°` be a habitat hub multigraph (cubic, loop-free, bridgeless),
> `n = |V(G°)|`, `M` a perfect matching, `τ = [ℓ even]`,
> `Φ = τ + Cut(G°)`. For a hub `v` write `M(v)` for its matching branch.
>
> **(i) The normal form.** For every `d ≥ 0` the minority maps `m` with
> `dist(m, M) = d` are in bijection with triples `(y, Z, φ)` where
> - `y, Z ⊆ E(G°) ∖ M` are **disjoint**,
> - `Z` is a **matching** of `G°`,
> - `φ` is an **injective end-selection** of `y` into `V ∖ V(Z)`
>   (`φ(β)` an end of `β`),
> - `d = |y| + 2|Z|`,
>
> the map being: the all-`M` prescription, deviated exactly at the hubs
> of `φ(y) ⊔ V(Z)`, each deviating hub `v` sending its dart to the
> **third** branch at `v` — the one that is neither `M(v)` nor the
> branch `v` selected.
>
> **(ii) Parity-consistency is a condition on `y` alone:**
> > `m` is parity-consistent **iff** `χ_y ∈ Φ`.
>
> **(iii) The per-matching distance parity.** All `M`-avoiding
> representatives of `[τ]` have the same weight parity; hence every
> parity-consistent map satisfies `dist(m, M) ≡ w_M (mod 2)`, and
> **every per-matching layer gap is even**.
>
> **Corollary 1 (the coset space).** The `M`-avoiding representatives of
> `[τ]` form an **affine subspace of dimension exactly `n/2 − 1`**;
> there are exactly `2^{n/2 − 1}` of them, so they are enumerable at
> `n = 30` (16 384) where `2^{n−1}` is not.
>
> **Corollary 2 (the optimal stratum).** `dist(m, M) = w_M` iff
> `Z = ∅` and `y` is a **minimum-weight** `M`-avoiding representative;
> hence, with (GR-57)(i),
> > `|{m : dist(m, M) = w_M}| = Σ_{y minimum} Π_{path comps}(k_c + 1)
> >  · Π_{cycle comps} 2`,
>
> the product running over the components of `supp(y)`, `k_c` = the
> number of branches of the component. (Together with (ii) this
> gives `d_par(M) = w_M` again; that equality is **(GR-44)(iii)**, and it
> is **consumed here, not re-proved**.)

*Proof.* (i): a cubic hub has exactly **two** non-matching branches, so
choosing a deviated dart at `v` is the same as choosing the *other*
non-matching branch, call it `x_v`; a distance-`d` map is exactly a set
`D` of `d` hubs together with a choice `x_v ∈ star(v) ∖ {M(v)}` for each
`v ∈ D`. A branch is chosen by at most its two ends; let `Z` be the
branches chosen **twice**, `y` the branches chosen **once**, and `φ` the
choosing end of each `y`-branch. Then `Z` is a matching (a hub chooses
once), `φ` is injective and avoids `V(Z)`, `D = φ(y) ⊔ V(Z)` and
`d = |y| + 2|Z|`; `x_v ≠ M(v)` gives `y ∪ Z ⊆ E ∖ M`. The construction
inverts this. (ii): `μ(m) = Σ_v e_{branch(m(v))}` and `μ(all-M) = 0`
((GR-37)(ii)'s cancellation), so `μ(m) = Σ_{v∈D}(e_{M(v)} + e_{m(v)})`;
the star relation `∂({v}) = e_{M(v)} + e_{x_v} + e_{m(v)}` gives
`e_{M(v)} + e_{m(v)} ≡ e_{x_v} (mod Cut)`, and the doubly-chosen
branches cancel over GF(2), so `μ(m) ≡ χ_y`. Parity-consistency is
`μ(m) ≡ τ`. (iii): two `M`-avoiding representatives differ by a cut
`∂(S)` supported off `M`, which forces `M` to match inside `S` and
inside `V ∖ S`, so `|S|` is even; at a cubic graph
`wt(∂(S)) = 3|S| − 2e(S) ≡ |S| ≡ 0 (mod 2)`.
Corollary 1: the map `GF(2)^{E ∖ M} → GF(2)^E / Cut(G°)`,
`y ↦ [χ_y]`, is **onto** — its cokernel is orthogonal to every
`e_β, β ∉ M`, i.e. supported inside `M`, and also inside the cycle
space, and a cycle-space vector has even degree at every hub while a
matching supports degree ≤ 1, so it is `0` (this is (GR-44)(i)'s
argument, consumed). The target has dimension `|E| − (n − 1) = n/2 + 1`
and the source dimension `|E ∖ M| = n`, so the fibre has dimension
`n/2 − 1`. Corollary 2: `|y| ≥ w_M` for any `M`-avoiding `y ∈ Φ`, so
`d = |y| + 2|Z| = w_M` forces `Z = ∅` and `|y| = w_M`. ∎

**What this buys, and what it is not.** (GR-47) is the normal form of
**all** parity-consistent maps of a shape; (GR-55) is the normal form of
the maps **at a fixed distance from a fixed anchor matching** — the
object (a′) is quantified over, and the one the landed record had no
handle on. Three consequences the direction uses immediately:

- **The whole deviation ladder is enumerable.** `gdev.min_dev` walks
  `Σ_M C(n, d)·2^d` candidates and is infeasible past the pool;
  (GR-55) walks the (at most `2^{n/2−1}`) coset representatives, then
  the `Z`-matchings, then the SDRs, and **only produces
  parity-consistent maps**. This is what makes *Step G77*'s exhaustive
  stratum census and the `n = 30` measurements affordable (the layer
  triple is certified equal to `gdev.min_dev`'s at 52 seeded stratum
  shapes, `--nf`).
- **The freedom at the optimum is named, in coordinates**: `(M, y, φ)`
  with `Z = ∅` (Corollary 2). GADM's μ-classes are a **coarsening** of
  this: `μ(m) = χ_y + ∂(φ(y))`, so `μ` sees only `y` and the *image* of
  the selection, never the selection's internal assignment — which is
  exactly why its fibre exchange came up short.
- **Parity is decoupled from selection.** By (ii) the only constraint
  a triple has to satisfy for parity-consistency lives on `y`; balance
  and full-goodness are then decided by `φ` (and `Z`) alone, at fixed
  `y`. This is the structural reason the exchange axes of *Step G76*
  are the right ones.

---

### Step G75 — (GR-56): the SPLIT identity, and full-goodness as ONE inequality per chunk — with the balance rider as its whole-graph instance

(GR-32)(i) gives the **sum** `defect_A + defect_B`. Its **difference**
is what decides which block binds, and the landed record never wrote it
down.

> **(GR-56)** *(proven; both identities asserted at **803 264**
> (admissible colouring, chunk) pairs — W3M and W3 exhaustively over
> all `3^n` minority maps, plus 91 seeded stratum shapes exhaustive per
> shape — the criterion checked against `gorient.fully_good_scan` at all
> 6434 admissible colourings, the whole-graph clause at 9990 instances
> and the `c`-independence at 3217 complementary pairs, `--law`; the
> `|δ_S − σ_S|` term shown **load-bearing** by an F13 control, `--adv`)*
>
> Let `(m, c)` be an admissible colouring of a habitat shape and `S` a
> chunk. Write
> - `δ_S := #{odd β ∈ S : β A-majority} − #{odd β ∈ S : β B-majority}`,
> - `σ_S := #{v ∈ z_mono(S) : maj(v) = A} − #{v ∈ z_mono(S) : maj(v) = B}`.
>
> **(i) The split identity.**
> > `defect_A(S) − defect_B(S) = δ_S − σ_S`.
>
> **(ii) The min form.** With (GR-32)(i),
> > `min(defect_A, defect_B)(S) = ½ ( cap(S) − z_mono(S) − |δ_S − σ_S| )`,
>
> and `cap(S) − z_mono(S) ≡ δ_S − σ_S (mod 2)`, so the right-hand side
> is an integer.
>
> **(iii) The one-inequality criterion.** An admissible colouring is
> **fully good** iff for **every proper chunk** `S`
> > `z_mono(S) + |δ_S − σ_S| ≤ cap(S) − 6`,
>
> a budget that is `≥ 1` by (GR-32)(ii) and `≥ 1 + ch(S)` when `S` has
> chords.
>
> **(iv) The balance rider is the whole-graph instance.** At
> `S = E(G°)`: `z(S) = z_mono(S) = σ_S = 0` and `cap(S) = 6`, so the
> inequality reads `|δ| ≤ 0` — **exactly the balance rider**
> ((GR-37)(i)), and (GR-32)(iii) is its `δ = 0` case.
>
> **(v) Everything is a function of the minority map alone.** At fixed
> `m` the two `c`-solutions are complementary ((GR-37)(ii)); the swap
> negates `δ_S` and `σ_S` **simultaneously**, hence fixes
> `|δ_S − σ_S|` and exchanges `defect_A ↔ defect_B`. So balance,
> admissibility and full-goodness are **properties of `m`**, not of
> `(m, c)`.

*Proof.* (i): (GR-33)(ii) in both blocks gives
`save_A − save_B = σ_S − δ_S` (each mono interior contributes to exactly
one of the two by its majority colour; each odd branch of `S` to exactly
one by its majority), and `defect = N − save` in both blocks with the
same `N`. (ii) is (i) with (GR-32)(i); the parity clause is
`exc(S) ≡ w_odd(S) (mod 2)`. (iii) is (ii) against `min ≥ 3`, using that
`2·min` is even. (iv) is the evaluation. (v) is (GR-37)(ii) plus the
observation that the swap moves every odd branch's majority and every
hub's majority together. ∎

**Why this is the right coordinate for (a′).** The two-block chunk scan
becomes a **single scalar budget per chunk**, and the two things that
spend it are visibly of different kinds: `z_mono(S)` is a pure
**orientation** count — how many of `S`'s interiors point their minority
dart out — while `|δ_S − σ_S|` is a **signed cancellation** between the
odd-branch imbalance inside `S` and the majority colours of those
outward-pointing interiors. Three readings the direction uses:

- **(a′) is a statement about minority maps only.** By (v) the whole
  question — admissible optimum, fully-good optimum — is a question
  about `m`, i.e. about the `(y, Z, φ)` coordinates of (GR-55). No
  colouring extension is ever a free variable. (This *confirms* GADM's
  caution that "the freedom lives in which deviation set is used", and
  makes it exact.)
- **The `|δ_S − σ_S|` term is not decoration.** F13 control `--adv`
  (3): the criterion **with the term dropped** misclassifies **30 of
  504** admissible W3 colourings; with it, 0 of 6434.
- **A restatement, not new, recorded because it is the shape the proof
  keeps meeting:** since `|δ_S − σ_S| ≤ w_odd(S) + z_mono(S)`, binding
  forces `z(S) − z_mono(S) ≤ 2 − w₄(S) − w₅(S)` — a binding chunk has at
  most `2 − w₄₅` interiors **not** pointing out, and a chunk with
  `w₄₅ ≥ 3` can never bind. This is (GR-33)(iii) in orientation
  language and it recovers `gcap.tec_candidates`' landed prefilter; it
  is cited here, not claimed.

**One entry-5-relevant by-product, reported and NOT developed** (that
half is another direction's target this wave): (iv) says the balance
rider and full-goodness are **the same inequality at different chunks**.
A proof of entry 5's balance half is the `S = E(G°)` case of what (a′)
needs at every proper chunk — the two residuals are, in these
coordinates, instances of one statement rather than two.

**One measured, unproven side fact, flagged as measured:** the *forest*
conjunct of `cflank.admissible` never bit — **0** balanced
parity-consistent colourings failed it over the whole `--law` census.
This is **not** (GR-28)(ii)'s proven `a = 0` (a statement about cut
vectors inside a class); it is measured on this census only.

---

### Step G76 — (GR-57): the SDR exchange calculus — the elementary shift is a distance-preserving move that CROSSES μ-classes, and the exchange-axis ladder is four rungs deep

GADM's census named the missing ingredient: *"a fixed-μ fiber-exchange
argument cannot prove (a′) alone; the argument needs a second exchange
axis across optimal μ-classes."* GDESC handed over the raw material —
(GR-46)'s cross-μ transitivity — but at the wrong quantifier: its moves
do not respect the deviation distance. (GR-55) supplies the missing
axis **inside** the optimal stratum.

> **(GR-57)** *(proven; the component product formula and the shift-graph
> component count asserted at **565** (matching, representative) cells
> over W3M/W3/W4 and 49 seeded stratum shapes; all **2459** elementary
> shifts checked to move exactly two hubs, to preserve the distance and
> to move `μ` by the two-hub cut, `--sdr`)*
>
> Let `M` be a perfect matching and `y` a minimum-weight `M`-avoiding
> representative of `[τ]`.
>
> **(i) The SDR space factors.** `supp(y)` has maximum degree 2
> ((GR-44)(ii)), so its components are paths and cycles. The injective
> end-selections of `y` are the product, over components, of:
> - a **path** component with `k` branches and `k+1` hubs: `k+1`
>   selections — *choose the one hub left unrepresented, and orient
>   away from it*;
> - a **cycle** component with `k` branches: **2** selections — the two
>   cyclic orientations.
>
> **(ii) The elementary shift, and what it connects.** Moving a path
> component's unrepresented hub by one step changes the representative
> of exactly one branch. On the SDR graph whose edges change exactly one
> representative, the components are exactly `2^{#cycle components}`,
> each of size `Π_{path comps}(k_c + 1)`: the two orientations of a
> cycle component are at Hamming distance `k`, and this is precisely the
> **Hall-tight** case (GR-44) recorded.
>
> **(iii) The shift is distance-preserving and cross-μ.** An elementary
> shift changes the minority map at **exactly two hubs** `v_out, v_in`,
> leaves `dist(·, M)` unchanged, and moves the coset representative by
> > `μ(m′) = μ(m) + ∂({v_out}) + ∂({v_in})` — a nonzero cut.
>
> So it stays inside the deviation-optimal stratum while **changing the
> μ-class** in the (GR-37)/GADM vector sense.
>
> **(iv) The exchange-axis ladder.** At the optimum the freedom is
> nested: `φ` (the SDR) ⊂ `Z` (the doubled-branch matching) ⊂ `y` (the
> coset representative) ⊂ `M` (the anchor matching). Measured over the
> **whole** `n_hub ≤ 6` habitat stratum (4920 labelled shapes), taking
> for each shape the **worst** optimal cell — how far one may be forced
> to move to reach a fully-good optimum — the deepest axis required is
> `φ` alone (the SDR) at **3787** shapes, `Z` at **6**, `y` at **162**,
> and the anchor matching `M` at **965**.

*Proof.* (i): an SDR of a path assigns each branch an end injectively;
scanning from one end, the assignment is forced once the unrepresented
hub is chosen, and every choice works. On a cycle every hub is
represented and the assignment is a fixed-point-free rotation, i.e. an
orientation. (ii): the per-component graphs are `P_{k+1}` (paths) and
edgeless on 2 vertices (cycles, `k ≥ 2`), and the whole graph is their
Cartesian product. (iii): the shift changes `φ` only at the branch
between the old and the new unrepresented hub, so `m` changes exactly at
those two hubs; the count of deviating hubs is unchanged; and
`μ(m) = χ_y + ∂(φ(y))` with `φ(y)` changing by the symmetric difference
`{v_out, v_in}`. ∎

**Reading (iv), which is the step's real content.** The SDR axis alone —
the one (GR-55) newly exposes — **already suffices at 77 % of the
stratum**. But it is **not** enough: at 1133 shapes some deviation-
optimal cell carries no fully-good selection, and at **965** of them the
rescue needs the **anchor matching** to move. The `Z` axis is nearly
inert (6 shapes), which is a useful negative: doubling a branch buys
almost nothing. So (a′)'s exchange argument needs, in order of
increasing depth, the SDR, then the coset representative, then the
matching — and *Step G78* shows the last rung is not optional.

---

### Step G77 — (GR-58): (a′) verified EXHAUSTIVELY on the whole `n_hub ≤ 6` habitat stratum, and at the first odd-carrying `n = 30` members

> **(GR-58)** *(measured, exhaustively where stated; `--exh`, `--big`)*
>
> **(i) The stratum, exhaustively.** At **every one of the 4920 labelled
> shapes** of the `Λ = ∅`, `D = 0`, `n_hub ≤ 6` habitat stratum — the
> same stratum as (GR-39)'s exhaustive census, **no subsample** — the
> exact layer triple, with the optimum computed by (GR-55) enumeration
> at **no deviation cap**, satisfies
> > `d_fg = d_adm`.
>
> Layer-triple distribution `(d_par, d_adm, d_fg) → count`:
> `(0,0,0): 368`, `(0,2,2): 13`, `(1,1,1): 2647`, `(1,2,2): 126`,
> `(2,2,2): 1766`.
>
> **(ii) The law has content there.** **2409** of the 4920 shapes carry
> a **non**-fully-good deviation optimum, so (a′) is not vacuous at
> half the stratum; the worst fully-good fraction among a shape's optima
> is **2/6**, and the smallest optimal stratum anywhere is **2** maps.
> Restricted to the 4780 odd-carrying shapes the worst fraction is the
> same 2/6.
>
> **(iii) Off the pool.** Min-form, **exhaustive** (full chunk scan, all
> perfect matchings, no cap): **W3M** `(2,2,2)` (18 optimal maps in 6
> cells, 11 fully good), **W3** `(2,3,3)` (78 in 14 cells, 38 good),
> **W4** `(2,2,2)` (16 in 8, 16 good), **NKo2v** `(2,2,2)` (40 optimal,
> 40 good), **NK(2)** `(2,2,2)` (agreeing with GADM's landed 2/2/2).
> Rank-light (the `2^M` chunk scan out of budget; full-goodness by
> **rank certificate**, README §4 convention 2): **CL5** `d_fg = d_adm
> = 2`, **CL6** `= 0`, **W5** `= 2`.
>
> **(iv) The first ODD-CARRYING large-`n` tests.** At **NKp(6)**
> (`n = 30`, six odd branches) and **NK55(6)** (`n = 30`, two odd
> branches) — GPSA's commissioned odd-rich constructions, at which no
> `d_fg` had ever been measured — over **40 sampled** perfect matchings
> (**a CAP, disclosed**; `gorient.perfect_matchings` is never called at
> `n = 30`), `min w_M = 6` in both (sampled range 6..8), and at the
> achieving matching every optimal map is balanced and admissible
> (64 of 128 and 576 of 832 deviation-optimal maps at
> that matching) with the optimum
> **fully good, rank-certified**:
> > `d_par(M) = d_adm(M) = d_fg(M) = 6` at both members.
>
> **What is NOT claimed at `n = 30`:** `min_M` over **all** perfect
> matchings of a 30-hub cubic multigraph is out of reach, so the
> **min-form** (a′) equality at these two members rests on the matching
> sample. Every previous large-`d` (a′) test (GADM's NK(2)/6/8/10) was
> **all-even**, i.e. balance-vacuous; these are the first where the
> balance rider is live.

**Provenance, stated so the figure is quotable.** The 4920 are
**labelled** shapes of `gcap.pool_specs` behind the `cflank.
cubic_habitat` gate — the generator carries isomorphic duplicates, so
read (i)–(ii) as labelled-instance counts (README §4 convention 7's
discipline), never as isomorphism-class counts. What *is* exhaustive is
the quantifier that matters: **every shape of the stratum, and within
each shape every parity-consistent map at every distance up to `d_fg`**,
with no cap reached anywhere (the `dmax = 8` guard was never approached;
the largest layer value on the stratum is 2).

**Against the named risk.** GADM's own statement of the risk was that
(a′)'s support was *"a coincidence across 133 shapes, all at `d ≤ 3`"*,
and that the three preceding directions each died where a measured
regularity was pushed past its sample. This step pushes (a′) past its
sample in **both** directions available — completeness (subsample →
whole stratum, capped → uncapped) and reach (all-even large `d` →
odd-carrying `n = 30`) — and it did not break. That is evidence, not a
proof, and *Step G79* keeps it labelled as such.

**One entry-5-relevant by-product, reported and NOT developed:** every
one of the 4920 shapes carries a **balanced admissible** colouring
**at its deviation optimum**, exhibited — extending the exhaustive
per-shape `d_adm < ∞` record from GPSA's 97 censused shapes. Entry 5's
status is unchanged by this direction. **One (b′)-relevant by-product,
likewise reported only:** the exhaustive balance-gap distribution on the
stratum is `d_adm − d_par ∈ {0: 4781, 1: 126, 2: 13}` — GADM's
`{0, 1, 2}` record confirmed with counts, **no gap > 2 anywhere on the
stratum**. (b′) was not this direction's secondary and is not developed.

---

### Step G78 — (GR-59): the PER-MATCHING variant of (a′) is REFUTED — `min_M` is load-bearing, and no (a′) proof may fix its anchor matching

GADM recorded the per-matching form as *"a separate recorded result"*
and warned that it *"may well be false"*. It is.

> **(GR-59)** *(refuted, by exhaustive census; `--exh` part (b))*
> The statement
> > *for every habitat shape and **every** perfect matching `M`, the
> > least deviation distance from `M` carrying an admissible colouring
> > equals the least carrying a fully-good one*
>
> is **FALSE**. Over **all 24 638 (shape, perfect matching) pairs** of
> the `n_hub ≤ 6` habitat stratum, **1278** pairs — at **1014 distinct
> shapes** — carry
> > `d_adm(M) < d_fg(M) < ∞`.
>
> Gap distribution `d_fg(M) − d_adm(M)`: `{2: 1251, 4: 27}` — **always
> even**, as (GR-55)(iii) forces. Violations by hub count:
> `{n_hub = 4: 27, n_hub = 6: 1251}`.
>
> **Smallest witness** (`n_hub = 4`, the `K4` hub multigraph with branch
> lengths `(5, 4, 2, 2, 2, 3)` in the order
> `01, 02, 03, 12, 13, 23`), at its first perfect matching:
> > `(d_par(M), d_adm(M), d_fg(M)) = (0, 0, 2)`,
>
> while the **min-form** triple at that very shape is `(0, 0, 0)`.

*Discussion — what dies and what does not.* **(a′) is untouched.** The
min-over-matchings quantifier is what the closure chain consumes
(GADM's *Step G55* is explicit), and *Step G77* verifies it at every
shape of the same stratum, including all 1014 shapes carrying a
per-matching violation. What (GR-59) kills is the stronger reading, and
it kills it at the very bottom of the habitat — `n_hub = 4`, gap 2,
`d_adm(M) = 0` — so no amount of scaling would have rescued it.

**The proof-side consequence, which is the point.** An (a′) proof
**cannot fix its anchor matching**: there is no matching-uniform version
of the statement to induct on, and the `M` rung of *Step G76*'s ladder
is not a convenience but a necessity — it is required at 965 stratum
shapes, and (GR-59) exhibits 1014 shapes at which *some* matching
supports an admissible optimum and no fully-good one at the same
distance. Combined with (GR-55) Corollary 2 (the optimal stratum is
`(y, φ)` at a **fixed** `M`), this says the (a′) argument must be a
**joint** selection: it chooses the matching and the coset
representative together.

**This is NOT an E1 or E2 event, and the two quantifiers are kept apart
mechanically.** GADM's E1 clause (iv) is stated over the min-form
`d_adm`, `d_fg`; the quantities here are per-matching. The `--adv` (5)
control asserts exactly this separation at the smallest witness: the
per-matching triple is `(0, 0, 2)` and the min-form triple is
`(0, 0, 0)`, both reported, neither substituted for the other. And no
`∞` is claimed anywhere: every `d_fg(M)` above is a **finite** exact
value; `--adv` (6) exhibits the discriminator (the same search at
`dmax = 1` reports NOT-FOUND-WITHIN-CAP, never `∞`, against a synthetic
genuinely-unsatisfiable predicate with 0 solutions at FULL `3^10`
enumeration).

---

### Step G79 — (GR-60): the residual named as input (Y), and where this leaves entry 1 and the (GR-15) line (hand-off)

> **(GR-60) — input (Y), the named residual of (a′).** By (GR-55) and
> (GR-56)(iii)+(v), (a′) is **equivalent** to:
> > *at every habitat shape there exist a perfect matching `M`, a
> > minimum-weight `M`-avoiding representative `y ∈ Φ`, and an injective
> > end-selection `φ` of `supp(y)` — together with, when
> > `d_adm > d_par`, an `M`-avoiding matching `Z` disjoint from `y` with
> > `|y| + 2|Z| = d_adm` and `φ` avoiding `V(Z)` — such that the
> > resulting minority map `m` is balanced and satisfies, for every
> > proper chunk `S`,*
> > > `z_mono(S) + |δ_S − σ_S| ≤ cap(S) − 6`.
>
> By (GR-59) the quantifier over `M` **cannot be dropped**; by
> (GR-57)(iv) the `y` rung cannot either. So input (Y) is a **joint
> matching-and-representative selection** statement — a
> matching-flexibility question in the same sense as, and in coordinates
> compatible with, GDESC's input (X), and **not** a move-availability
> case analysis.

- **The route ledger** (coordinator updates on landing):
  **Entry 1** (uniform fully-good existence at `Λ = ∅` `D = 0`,
  growth-law re-anchoring) — **OPEN, unchanged in status**; **(a′)
  stays its primary and still carries NO bar**. What moved is the
  evidence and the shape of the proof obligation, not the status:
  (a′) is now exhaustive on the `n_hub ≤ 6` stratum at no cap and true
  at the first odd-carrying `n = 30` tests ((GR-58)); its search space
  has coordinates ((GR-55)); its criterion is one inequality per chunk
  ((GR-56)); its exchange axes are named and measured ((GR-57)); its
  stronger per-matching variant is **refuted** ((GR-59)); and its
  residual is **input (Y)** ((GR-60)). (b′)/(c)/(d′) untouched, still
  named and unclaimed.
  **Entry 5** — **untouched by this direction** (another direction's
  target this wave); two by-products reported at *Steps G75* and *G77*
  and deliberately not developed. **Entries 2–4** unchanged.
- **TERMINATION check** (coordinator's to run; the draft's reading).
  **E1 does not fire** — no g-flank. Clause **(iv)** applied
  explicitly: **nothing found min-form `d_adm < d_fg`**, finite or
  infinite; every `d_fg` reported is an exact equality by full chunk
  scan or a **rank-certified** equality at the optimum; the only finite
  `d_fg > d_adm` anywhere in this pass is the **per-matching** quantity
  of (GR-59), which is a different statement, is labelled as such, and
  is separated from the min-form by a dedicated control. Clause **(v)**
  applied explicitly: **on the safe side** — no `d_adm = ∞` anywhere;
  every one of the 4920 stratum shapes carries a balanced admissible
  colouring **at its optimum**, and the `n = 30` members carry them at
  every sampled matching; the matching sample and the `dmax` guard are
  reported as **CAPS** (an exhausted cap is not `∞`, and the guard was
  never approached). **E2 does not fire** — (a′) is neither refuted nor
  unprovable-as-posed; and (GR-59), read at its worst as a refutation of
  a *variant*, comes with a successor named (input (Y)) and leaves entry
  1 open with (a′) carrying no bar, so the retained carve-out applies.
  **E3 does not fire, and is NOT armed** — entry 1 is unproven, and E3
  is armed only by an **entry-5** HIT, which this direction neither
  sought nor produced.
- **The successor's natural routing** (the draft's reading; the dispatch
  is a coordinator/user call, not made here): **input (Y)** — the joint
  `(M, y)` selection, attacked with matching-flexibility instruments
  (alternating-cycle toggles on the `M`-avoiding coset space, whose
  affine structure and dimension `n/2 − 1` are now exact) rather than
  with local exchange. Two calibrating opening cases fall out of the
  measurements: the **965** stratum shapes whose worst optimal cell
  needs the `M` rung, and the **13** shapes at balance gap 2. **A
  structural observation worth the coordinator's attention:** input (Y)
  and GDESC's input (X) are, in the (GR-56) coordinates, the **proper-
  chunk** and **whole-graph** instances of one inequality — a single
  matching-flexibility instrument could serve both, which is a
  cross-entry finding no earlier direction was in a position to see.
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**, and
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **an (a′) HIT alone
  would still not close the existence target while entry 5 is open, and
  would not fire E3** — and (a′) did **not** HIT here;
  (GR-37)(iii)'s flag stays **HALF-retired** (the parity half repaired
  by (GR-44); the balance clause statement-beyond-proof). Every
  "0 fully-hot"-style figure keeps its **family qualifier**
  (binding-capable, not capacity-tight; (GR-40)'s 815 → 573 is a prune,
  not a zero). (GR-15) **OPEN**, unchanged in both directions;
  **no gap-map status moves.**

---

### Verification (Steps G74–G79)

`notes/scripts/w4/glaw.py` (**new with this pass**; imports — all
read-only — `kbare_common` (`verts_of`), `gridcol` (`subdivide`),
`cflank` (`admissible`, `cubic_habitat`, `hub_model`), `gcap`
(`branch_stats`, `pool_specs`), `gunif` (`WITNESSES`), `gexist`
(`fully_good_rank`, `ladder_specs`), `gorient`
(`cm_solve`, `cm_colouring`, `odd_balance`, `perfect_matchings`,
`m_of_matching`, `prep_shape`, `fully_good_scan`, `fast_defects`,
`darts_at`), `gdev` (`min_dev`, `even_vec`, `fundamental_cycles`,
`in_coset`, `nk_specs`, `light_hm`), `gadm` (`complete_matching`), `gpsa` (`branches_at`,
`is_bridgeless`, `delta_of`, `xor_vec`, `nkp_specs`, `nk55_specs`,
`nko2v_specs`); rank enters **only** through `gexist.fully_good_rank`,
README §4 convention 2). Local devices, none shadowing a §1 primitive:
`gf2_affine` (a GF(2) **affine solver** — §1 lists `exactcore.nullspace`
over ℚ and `kbare_common.rank_modp` for a rank, so no GF(2) solve
exists to reuse), `hm_spec_map` (hub-model ↔ spec branch index via the
`('i', spec, j)` interior tag `gridcol.subdivide` writes),
`chunk_inv` (the (GR-56) invariants `cap, z_mono, δ_S, σ_S`),
`avoid_space`/`avoid_all`/`min_avoiders` (the `M`-avoiding coset affine
space of (GR-55) Cor. 1 — a **different device** from
`gpsa.min_m_avoiding_rep`, which enumerates all `2^{n−1}` cuts behind an
`n ≤ 16` guard and returns one minimiser; this one solves the cycle
system and enumerates the `2^{n/2−1}` fibre, which is what `n = 30`
needs), `sdr_space`/`sdr_graph` (**all** injective end-selections and
the elementary-shift graph — `gpsa.sdr_build` emits **one** selection
per component, a different job), `map_from`/`matb`/`dist_stratum`
(the (GR-55) enumerator), `layers_exact`/`layers_at_matching`/
`min_form`/`rank_light` (the exact layer triples), `all_maps`,
`stratum_shapes`, `sample_matchings`, `verify_triple` (the adversarial
(GR-55) verifier). Exact integers and GF(2) throughout; **no floating
point**; every rng seeded from `R_SEED = 20260819` and printed; no bare
`set` printed; nothing samples a placement (§(K-clos) (AC-9)). **No pool
is new:** `--exh` and `--sdr`'s ladder sweep the **whole** existing
`gcap.pool_specs` stratum behind the `cflank.cubic_habitat` gate;
`--law`/`--nf`/`--sdr`'s certification legs take seeded subsamples of
it, disclosed as such; W3M/W3/W4/W5, the ladders, NK(2), NKo2v, NKp(6)
and NK55(6) are landed constructions, reused.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --law       #  ~7 s  (GR-56): both identities + the one-inequality criterion, 803 264 (colouring, chunk) pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --nf        #  ~7 s  (GR-55): the normal form vs brute force, the 2^(n/2-1) count, the parity clause, min_dev cross-check
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --exh       # ~33 s  (GR-58)(i)-(ii) the exhaustive (a') census + (GR-59) the per-matching refutation
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --sdr       # ~19 s  (GR-57): the component formula, the shift, the four-rung axis ladder over the whole stratum
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --big       #  ~8 s  (GR-58)(iii)-(iv): off-pool min-form, rank-light members, the n = 30 odd-carrying tests
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --adv       #  ~2 s  six F13 controls, each must-reject/-fire with a negative control
PYTHONHASHSEED=0 python3 notes/scripts/w4/glaw.py --validate  # ~81 s  all six in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-55)(i)–(ii): the normal form is a bijection onto the distance-`d` parity-consistent maps | `--nf` | at 1300 (matching, distance) cells the enumerated triples' maps are asserted **injective** and **set-equal** to the brute-force `3^n` filtered stratum, in both directions |
| (GR-55) Cor. 1: the `M`-avoiding coset space has dimension `n/2 − 1` | `--nf`, `--adv` | `len(avoid_all) == 2**(n//2 - 1)` at 260 (shape, matching) pairs; `--adv` (4) shows the cycle system is non-degenerate (dropping one equation raises the dimension) |
| (GR-55)(iii): the per-matching distance parity | `--nf`, `--exh` | all `M`-avoiding representatives asserted of one weight parity at 260 pairs; every per-matching gap asserted even over all 24 638 pairs |
| (GR-55) Cor. 2 + (GR-57)(i): the optimal-stratum product formula | `--nf` | `Σ_y Π(k+1)·Π2` asserted equal to the enumerated optimal stratum at 260 (shape, matching) pairs |
| the (GR-55) layer triple is the landed one | `--nf` | `(d_par, d_adm, d_fg)` asserted equal to `gdev.min_dev`'s at 52 seeded stratum shapes |
| (GR-56)(i) the split identity, (GR-32)(i) the sum | `--law` | both asserted at every one of 803 264 (admissible colouring, chunk) pairs; W3M/W3 exhaustive over all `3^n` maps |
| (GR-56)(iii) the one-inequality criterion | `--law` | the criterion's verdict asserted equal to `gorient.fully_good_scan`'s at all 6434 admissible colourings |
| (GR-56)(iii) is SHARP (the `\|δ_S − σ_S\|` term is load-bearing) | `--adv` (3) | the term-dropped criterion misclassifies 30/504 W3 colourings — a **must-fire** control |
| (GR-56)(iv) balance = the whole-graph instance | `--law` | 9990 instances: at balanced colourings `cap = 6, z_mono = σ = 0, defect = (3,3)` asserted; at unbalanced ones `δ ≠ 0` asserted |
| (GR-56)(v) full-goodness is a function of `m` | `--law` | both `c`-solutions' verdicts asserted equal at 3217 complementary pairs |
| the forest conjunct never bites | `--law` | counted, **reported as MEASURED** (0 of the census), not asserted as a theorem |
| (GR-57)(ii) the shift-graph component count | `--sdr` | `2^#cycles` components of equal size `Π_paths(k+1)`, asserted at 565 (matching, representative) cells |
| (GR-57)(iii) the shift is 2-hub, distance-preserving, cross-μ | `--sdr` | all 2459 shifts: exactly two hubs moved, equal deviation counts, `μ` difference asserted equal to the two-hub cut and asserted nonzero |
| (GR-57)(iv) the axis ladder | `--sdr` | the whole 4920-shape stratum: per shape, the worst optimal cell's minimal rescuing axis |
| (GR-58)(i) `d_fg = d_adm` exhaustively | `--exh` | all 4920 shapes; `d_fg != d_adm` raises a HEADLINE assertion; `d_adm`/`d_fg` both required found inside the guard |
| (GR-58)(iii)–(iv) off-pool and `n = 30` | `--big` | min-form exhaustive at W3M/W3/W4/NKo2v/NK(2); rank certificates at CL5/CL6/W5/NKp(6)/NK55(6); matching sample and rank-test caps printed |
| (GR-59) the per-matching refutation | `--exh` | per-matching triples at all 24 638 (shape, matching) pairs; the violation count, the gap histogram and the smallest witness printed |
| the (GR-55) verifier rejects doctored triples | `--adv` (1)–(2) | a hub-reusing selection and a matching-meeting representative are both REJECTED; the honest triple PASSES (negative control) |
| E1 clause (iv) discriminator | `--adv` (5) | at the smallest (GR-59) witness the per-matching triple `(0,0,2)` and the min-form triple `(0,0,0)` are both computed and reported — the quantifiers cannot be conflated |
| E1 clause (v) discriminator | `--adv` (6) | the same search at `dmax = 1` returns NOT-FOUND-WITHIN-CAP; a synthetic unsatisfiable predicate has 0 solutions at FULL `3^10` enumeration (the only thing that is an `∞`) |
| input (Y) / (a′) / (GR-15) as statements | — | theorem gaps; not driver-testable |

**Determinism.** `--validate` was run at `PYTHONHASHSEED` 0 and 999
(both exit 0): the outputs differ in **exactly four wall-clock `[Ns]`
annotations** and in no other byte — the documented exception.

**Scratch probes (README's standing rule).** None retained: every figure
above is produced by a committed driver mode. (Development iterations —
a first matching sampler that forced a single branch and reached only 13
distinct matchings at `n = 30`, raised to a random independent forced
set reaching 40; a first layer computer that enumerated all `3^n` maps
before (GR-55) replaced it — changed no mathematics; the final driver
re-derives everything.)

---

### Confidence verdict (Steps G74–G79)

| | claim | standing |
|---|---|---|
| **(GR-55)**(i)–(iii) | the `(y, Z, φ)` deviation normal form; parity on `y` alone; the distance parity | **proven-informally** (proof above; the bijection certified against brute force at 1300 cells) |
| (GR-55) Cor. 1 | the `M`-avoiding coset space is affine of dimension `n/2 − 1` | **proven-informally** (surjectivity is (GR-44)(i)'s argument, consumed; certified at 260 pairs and F13-controlled) |
| (GR-55) Cor. 2 | the optimal stratum is `(minimum-weight y, SDR)` | **proven-informally**; the count formula certified at 260 pairs |
| **(GR-56)**(i)–(v) | the split identity; the min form; the one-inequality criterion; balance as the whole-graph instance; `m`-dependence only | **proven-informally** (two lines from (GR-32)(i) + (GR-33)(ii) + (GR-37)(ii); asserted at 803 264 pairs; the criterion agrees with `fully_good_scan` at all 6434 admissible colourings) |
| **(GR-57)**(i)–(iii) | the SDR component product; the shift graph; the shift is 2-hub, distance-preserving, cross-μ | **proven-informally** (certified at 565 cells / 2459 shifts) |
| (GR-57)(iv) | the four-rung exchange-axis ladder `3787 / 6 / 162 / 965` | **measured, exhaustive on the `n_hub ≤ 6` stratum** (labelled shapes) |
| **(GR-58)**(i)–(ii) | `d_fg = d_adm` at every shape of the stratum, no cap; the law has content at 2409 of them | **measured, EXHAUSTIVE on that stratum** — a measured positive, not a proof |
| (GR-58)(iii) | the off-pool min-form values; the rank-light members | **measured** (exhaustive where stated; rank certificates at the optimum, caps printed) |
| (GR-58)(iv) | `d_par(M) = d_adm(M) = d_fg(M) = 6` at NKp(6) and NK55(6) | **measured, per matching**, rank-certified at the optimum; the **min over matchings is NOT computed** at `n = 30` (a disclosed CAP) |
| **(GR-59)** | the **per-matching** variant of (a′) | **REFUTED** — 1278 of 24 638 pairs, 1014 shapes, smallest witness `n_hub = 4`; **not** a refutation of (a′) and **not** an E1/E2 event |
| **(a′)** | `d_fg = d_adm` at every habitat shape | **OPEN — measured true everywhere probed, now exhaustively on the whole `n_hub ≤ 6` stratum at no cap and at the first odd-carrying `n = 30` tests**; not proven; residual named as input (Y) |
| **(GR-60)** | input (Y): the joint `(M, y, φ, Z)` selection statement equivalent to (a′) | **proven-informally as an equivalence** (it is (GR-55) + (GR-56)(iii)+(v) restated); the statement itself **OPEN** |
| entry 5 | | **untouched by this direction** — status as GDESC left it (half 1 PROVEN, half 2 true-modulo-named-gap, input (X)); two by-products reported, not developed |
| **(GR-15)** | | **OPEN — unchanged in both directions.** No flank; no gap-map status moves; (GR-4′)/(GR-10) untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's through GDESC's: colourings of fixed graphs, exact GF(2)
linear algebra on hub multigraphs, and exact ranks of constructed
configurations — never `PencilNondegFeasible G`; no σ-fixed witness is
read as generic (§(K-clos) (AC-9)).

### What would change this (Steps G74–G79)

*(i)* **Discharging input (Y)** — a joint matching-and-representative
selection proof in the (GR-55) coordinates (alternating-cycle toggles on
the affine `M`-avoiding coset space; the `965` `M`-rung shapes as the
calibrating family) proves **(a′)**. It still would **not** close the
`Λ = ∅` `D = 0` existence target while entry 5 is open, and would
**not** fire E3.
*(ii)* **A habitat shape with min-form `d_adm < d_fg < ∞`** — refutes
(a′), E2's branch; none exists on the whole `n_hub ≤ 6` stratum at full
optimal enumeration, nor at any off-pool member measured.
*(iii)* **A shape with `d_fg = ∞` at finite `d_adm`** — a g-flank, E1,
unconditional; nothing of the kind was seen, and every cap is reported
as a cap.
*(iv)* **A per-matching gap larger than 4**, or one at `n_hub ≥ 8` —
sharpens (GR-59) quantitatively; the stratum's spectrum is exactly
`{2, 4}` and the parity clause (GR-55)(iii) forbids odd gaps.
*(v)* **A shape whose deviation-optimal stratum is a single map** —
would make (a′) a coincidence with no exchange freedom at all; the
minimum over the stratum is **2**, so no such shape exists at
`n_hub ≤ 6`.
*(vi)* **An `n_hub = 8` habitat enumerator** — the one structural
extension every quantitative claim here is capped by; `gridcol.
multigraphs`' silently-truncating `cap = 4000` and the leaf-blowup
recursion still price it as genuinely-new engineering (GDEV's finding,
re-verified in spirit here: nothing in this pass reaches past
`n_hub = 6` except by named construction).

---

### Steps G80–G85 (2026-08-19, direction YLOC) — GBAL's instrument does **NOT** localize, and the break point is **NOT** the predicted one: **(GR-61)** carries the (GR-56) chunk invariants into the z-form exactly (so step 1 of the pinned route succeeds, and buys notation only), but **(GR-62) REFUTES step 2 by witness** — full goodness is **not** a function of the (GR-50) degree data, so the chunk system is not a degree-constraint system and (GR-51)'s criterion does not apply, with the failure boundary **exact** (the localization's premise survives on a **10-shape** exceptional family and dies at all **4914** others, and the witness pair is **rank-certified** at `n_hub = 4`); **(GR-63)** shows the coordinator's expected obstruction — (GR-52)'s parity contradiction — is **not** where the chain breaks (its `2 e_H(R)` step is a per-hub-subset identity, valid at every `R`), the break being two links earlier at (GR-50)→(GR-51), and adds the deeper reason the transfer was never going to work: **(X) and (Y) share the inequality but not the quantifier**; the positive half is **(GR-64)**, the **collision bound** — a colouring-free lower bound on `d_fg` that prices exactly the coupling between (Y)'s distance quantifier and its chunk constraints, with a **proven `≤ 2` per-chunk ceiling**, a packing form, and a **sound anchor-matching prune** — and **(GR-65)**, the **fit identity**: `dist(m, M)` and `z_mono(S)` are the *same statistic*, which names both what the successor instrument must control and why GBAL's forgets it; **(GR-66)** measures the consequence on GBAL's own certificate. **Input (Y) stays OPEN, (a′) is NOT hit, E3 (ARMED by GBAL) does NOT fire; (GR-15) OPEN, no gap-map status moves.**

**Notation** (on top of *Steps G38–G42*, *Steps G68–G73* and
*Steps G74–G79*). `G°` cubic, loop-free, bridgeless; `n = |V(G°)|`;
`τ_β = [ℓ_β even]`; `z ∈ GF(2)^{E}` a branch colouring with dart colours
`ζ(v, β) = z_β` at `β`'s first end and `z_β ⊕ τ_β` at its second
((GR-49)); `z` **admissible** iff no hub sees three equal dart colours.
`ε(x) := (−1)^x` (so `ε(0) = +1`, colour **A** `= 0`). For a chunk `S`,
`Z2(S)` is its **interior** set (the `S`-degree-2 hubs); every hub of
`W_S` has `S`-degree 2 or 3, and an interior `v` has two `S`-branches
`β₁(v), β₂(v)` and one **free** branch `β₃(v)` (an exit or a chord).
`cap(S) = 2|Z2(S)| + exc(S)`; `ch(S)` the chords. `M` a perfect matching
of `G°`, `M(v)` its branch at `v`, `dist(m, M) = #{v : m(v) ≠ M(v)}`.

---

### Step G80 — (GR-61): the (GR-56) chunk invariants in the z-form, and the **degeneracy** that confines GBAL's reduction to the whole graph

The pinned route's step 1 was *"re-express `cap(S)`, `z_mono(S)`, `δ_S`,
`σ_S` in (GR-49)'s coordinate `z`"*, on the reasoning that (GR-56)(v)
makes them functions of the minority map and (GR-49) makes the minority
map `z`. That reasoning is right and the translation is immediate — and
writing it down is what exposes why the *rest* of the chain is not.

> **(GR-61)** *(proven; every clause machine-asserted against the landed
> oracles at **31 047 708** (admissible `z`, chunk) pairs over **4924**
> shapes — the exhaustive `Λ = ∅`, `D = 0`, `n_hub ≤ 6` habitat stratum
> (4920 labelled shapes, no subsample) plus W3M / W3 / W4 / NKo2v —
> with **433 938** admissible `z` round-tripped through
> `gbal.z_to_map` / `map_to_z` and the z-side criterion asserted equal to
> `gorient.fully_good_scan` at every one; `--loc`)*
>
> Let `z` be admissible and `S` a chunk. Then
>
> **(i)** `cap(S) = 2|Z2(S)| + exc(S)` — colouring-free ((GR-32), consumed).
>
> **(ii)** `z_mono(S) = #{v ∈ Z2(S) : ζ(v, β₁(v)) = ζ(v, β₂(v))}` — the
> interiors whose **two `S`-darts agree**.
>
> **(iii)** `σ_S = Σ_{v ∈ Z2(S), mono} ε(ζ(v, β₁(v)))` — those interiors
> signed by that shared colour.
>
> **(iv)** `δ_S = Σ_{odd γ ∈ S} ε(z_γ)`.
>
> **(v)** So (GR-56)(iii)'s criterion is the system, over proper chunks,
> > `#{v ∈ Z2(S) : ζ(v,β₁) = ζ(v,β₂)} + |Σ_{odd γ∈S} ε(z_γ) − Σ_{v mono} ε(ζ(v,β₁))| ≤ cap(S) − 6.`
>
> **(vi) The degeneracy.** `Z2(S) = ∅` **iff** `S = E(G°)`
> ((GR-32)(ii)). Hence `E(G°)` is the **unique** chunk at which
> `z_mono` and `σ` vanish *identically*, and therefore the **unique**
> chunk whose inequality is a function of `z|_O` alone. Every proper
> chunk's inequality reads the **even** bits.

*Proof.* (ii)/(iii): by (GR-49) a hub's three dart colours are a 2–1
split and `m(v)` is the minority dart; so *"the minority dart is the
exit `β₃(v)`"* — which is (GR-56)'s definition of a monochromatic
`S`-pair — is exactly *"the two `S`-darts agree"*, and in that case the
majority colour `c(v)` **is** that shared colour, which is (GR-56)'s
`σ_S` summand. (iv): an odd branch has `τ_γ = 0`, so both its darts carry
`z_γ` and its majority colour is that common value ((GR-49)(ii)); `ε` is
(GR-56)'s `±1`. (v) is the substitution. (vi): `Z2(S) = ∅` makes both
sums empty; conversely (GR-32)(ii) forces `S = E(G°)`, and there
`δ_{E(G°)} = Σ_{odd} ε(z_γ)` is the balance functional, whose vanishing
is (GR-37)(i) — (GR-56)(iv) restated in the z-form. ∎

**Why (vi) is the load-bearing sentence, and not a remark.** It is the
whole reason GBAL's chain exists. At `S = E(G°)` the inequality
`|δ| ≤ 0` constrains **only** `z|_O`; the even bits are then free subject
to *admissibility alone*, and admissibility at a hub is *"the A-dart
count is 1 or 2"* — a **degree** condition on the even branches. That is
(GR-50), verbatim. At a proper chunk the two terms that vanished come
back, and they are read off *which* dart is the odd one out at each
interior, not how many darts are A. Step 2 of the pinned route is
therefore not a harder version of (GR-50); it is a statement about a
**finer quotient of the admissible cube** — and *Step G81* shows the
finer quotient is genuinely finer.

**The exceptional family, measured exhaustively and recorded because it
is the exact boundary.** The localization's *premise* — every chunk
invariant a function of the odd pattern — survives at exactly **10** of
the 4924 inventory shapes: the **9** one-even-branch θ shapes (profiles
`{2,5,5}` and `{3,4,5}`, where the single even branch's bit only swaps
*which* of the two hubs is monochromatic, leaving every `z_mono(S)`
constant) and the **all-length-3 `K4`**, which has **no even branch at
all** (so `z = z|_O` and there is nothing to forget). It fails at all
**4914** others. This is the (GR-29)/(GR-30) exact-boundary shape:
GBAL's premise is a theorem on a thin family and false immediately
outside it, and the family is exactly *"no even-branch freedom"*.

**What (GR-61) buys.** Notation, and one structural fact ((vi)). It does
**not** reduce anything: the four invariants are the same local functions
of `m` that (GR-56) already had, now spelled in `z`. The coordinator's
step 1 succeeds, and the honest accounting is that its value is entirely
in making step 2's failure visible.

---

### Step G81 — (GR-62): full goodness is **NOT** a function of the (GR-50) degree data — the pinned route's step 2 is **REFUTED by witness**

> **(GR-62)** *(the negative clause **REFUTED by witness**, hence proven;
> the census exhaustive over the same 4924-shape inventory, with the
> witness pair **rank-certified** through `gexist.fully_good_rank`
> (README §4 convention 2); `--fibre`, control (5) of `--adv`)*
>
> Fix a shape and a balanced pattern `p` on the odd branches. By (GR-50)
> the admissible `z` with `z|_O = p` are exactly the orientations of the
> even-branch graph `H` obeying `l_v ≤ indeg(v) ≤ u_v`. Then:
>
> **(i)** Balance **is** constant on each such fibre — it is a function
> of `p` (asserted at every fibre of every inventory shape).
>
> **(ii)** Full goodness is **not** constant on the fibre over a fixed
> `(p, indeg)` pair: it **splits** on **7982** of the **217 468** balanced
> admissible fibres of the inventory, at **1499** of its **4924** shapes,
> the smallest witness at **`n_hub = 4`**. Split-shape counts by `n_hub`:
> `{4: 72, 6: 1424, 8: 1, 10: 1, 12: 1}` of
> `{2: 10, 4: 312, 6: 4598, 8: 1, 10: 2, 12: 1}`.
>
> **Read that honestly.** No `n_hub = 2` shape splits, consistent with
> (GR-61)'s exceptional family; but the converse fails badly — at
> **3425** of the 4924 shapes full goodness *is* a function of the degree
> data, so failing (GR-61)'s premise does not force a split, and a
> shape's non-split means nothing (its fibres merely happen to be
> goodness-homogeneous). A split is a **sufficient** refutation and one
> suffices: a criterion of the (GR-51) kind must work at *every* shape,
> and 1499 of them defeat it.
>
> **(iii)** Consequently the set of orientations satisfying the
> proper-chunk instances of (GR-56)(iii) is **not a union of in-degree
> classes**, so the chunk system is **not a degree-constraint system** and
> **(GR-51)'s two-sided Hall criterion does not apply to it** — that
> criterion's entire content is *feasibility of a degree-constrained
> orientation ⟺ a local weight inequality*, and its hypothesis fails
> here.
>
> **(iii′) The precision that (iii) needs, stated because overclaiming it
> would be the easy error.** Two different questions must be kept apart.
> *Deciding a given configuration* — "is this `z` fully good?" — is
> **provably not** a degree predicate, by (ii). *Deciding existence at a
> given pattern* — "is some admissible `z` with `z|_O = p` fully good?" —
> is trivially a function of `p` alone, so a criterion for **it** is not
> excluded by (ii); what (ii) does exclude is that such a criterion be
> **(GR-51)'s**, i.e. that the feasible orientations be cut out by
> in-degree bounds. Any successor existence criterion must therefore
> characterize a set the degree quotient cannot see.

*Proof.* (i) is (GR-61)(vi). (iii) is immediate from (ii): a predicate
of the degree data takes one value on a fibre, and full goodness takes
two. (ii) is the witness below. ∎

**The witness** (smallest; `n_hub = 4`, `E = 6` — the `K4` hub
multigraph with lengths `(5, 4, 2, 3, 2, 2)`):

```
specs = [(0,1,5), (0,2,4), (0,3,2), (1,2,3), (1,3,2), (2,3,2)]
odd branches = {0, 3};  pattern (z_0, z_3) = (1, 0)  [balanced]
in-degree vector = (1, 1, 1, 1);  fibre size 2
z_good = [1, 1, 0, 0, 0, 1]      fully good
z_bad  = [1, 0, 1, 0, 0, 0]      binds at S = {3, 4, 5} -- the triangle on hubs 1, 2, 3
                                 cap 7, z(S) = 3, exc(S) = 1,
                                 z_mono = 3, |δ_S − σ_S| = 0, budget = 1
```

Both members are admissible (`cflank.admissible`, the (GR-37)(i) ground
truth), balanced, and carry the **same** odd pattern and the **same**
even-branch in-degree vector; they differ only in *which* even branches
point in — i.e. by reversing a directed cycle of the even-branch graph
`H`, the move that preserves every in-degree.
`gexist.fully_good_rank` returns **True** on the first and **False** on
the second, so the split is a property of the **geometry**, not an
artifact of the combinatorial evaluator. Note how badly the bad member
fails: all three interiors of the triangle point their minority dart
out, `z_mono = 3` against a budget of `1`.

**The mechanism, stated so it is reusable.** The in-degree at `v` fixes
the *number* of A-darts, hence the majority colour `c(v)`; it does not
fix *which* dart is the minority. `z_mono(S)` and `σ_S` read exactly the
latter. So the orientation model is the quotient of the admissible cube
that remembers `c` and forgets `m` — and by (GR-56)(v) the whole
full-goodness question is a question about `m`. GBAL's instrument
survives at the whole graph only because there the question is about `c`
too (`δ` is a sum of odd-branch colours, and odd branches carry the same
colour at both ends).

**A quantitative form of the same statement** (`--adv` (5)): the *best
possible* degree-only classifier of full goodness — the one that answers
with each fibre's majority verdict — has an **irreducible error of 26 of
252** balanced admissible configurations already at **W3M** (`n_hub = 8`).
An instrument cannot be repaired into existence at that error rate.

---

### Step G82 — (GR-63): the predicted obstruction is **REFUTED as stated**; the break is two links earlier, and the deeper reason is a **quantifier**, not a count

The dispatch predicted the break precisely: *"GBAL's argument is
whole-graph-only because (GR-52)'s parity contradiction uses `2 e_H(S)`
over the whole side… At a proper chunk that global count is not
available."*

> **(GR-63)** *(the refutation proven; the identity asserted at
> **305 704** (shape, hub subset) pairs over the whole 4924-shape
> inventory — every `R ⊆ V(G°)` of every shape — 0 failures; `--par`)*
>
> **(i)** In (GR-52)'s proof the set `S` is **not a chunk**: it is an
> arbitrary **hub subset** — the two-sided Hall violator of (GR-51)(i) —
> and the step in question is the identity
> > `Σ_{v ∈ R} a_v = 2 e_H(R)`,  `a_v := d_v − b^{out}_v`,
>
> a per-subset double count of `H`'s edges inside `R`. It holds for
> **every** `R ⊆ V(G°)` of **every** shape; no global quantity enters.
> So (GR-52) is not the obstruction, and needs no chunk analogue: it is
> a lemma *inside* the orientation model and would localize for free if
> the orientation model did.
>
> **(ii) The chain audit.** (GR-49) → **localizes** ((GR-61)), buying
> notation only. (GR-50) → **FAILS** ((GR-62)): the per-chunk terms are
> not degree functions. (GR-51) → **unreachable**: its input is
> (GR-50)'s bound interval. (GR-52) → **would localize** ((i)), with
> nothing to act on. (GR-53) → **a second, independent obstruction**: it
> exhausts the pair/triple constraint structure the shape imposes on its
> `≤ 6` **odd branches** (a finite family, 1 / 44 / 4837 at
> `2k = 2/4/6`) — a family bounded **shape-independently**, since the
> excess law `Σ(ℓ − 2) = 6` caps `2k` at 6. The chunk system is indexed
> by **chunks**, and that family carries no such cap: the mean
> proper-chunk count per shape, measured over the whole inventory, is
> `{2: 3.0, 4: 12.8, 6: 45.9, 8: 163.0, 10: 543.5, 12: 1148.0}` by
> `n_hub`. Even a working (GR-51) analogue would therefore face an
> exhaustion with **no shape-independent bound** — a second, independent
> reason the chain does not survive localization.
>
> **(iii) The deeper reason, and the correction to the transfer
> premise.** (GR-56)(iv) correctly identifies (X) and (Y) as the
> whole-graph and proper-chunk instances of one **inequality**. What does
> not transfer is not only the argument but the **quantifier**: input (X)
> is *unconstrained* existence of a balanced admissible configuration
> (GBAL's (GR-54)), while input (Y) ((GR-60)) demands one **inside the
> minimum-deviation stratum of some perfect matching**. GBAL's
> instrument carries no distance datum whatever — no matching appears in
> the z-form — so it could not deliver (Y) even with the chunk terms
> free. *Steps G83–G85* price that gap.

**Scope of the refutation.** It is a refutation of the *predicted
location*, not of the prediction's spirit: the chain does break, and it
breaks whole-graph-only, exactly as the dispatch expected. The value of
locating it precisely is that the two candidate repairs are different
work — repairing a parity argument is local combinatorics, while
replacing (GR-50) means finding a *new* feasibility criterion for a
predicate that the degree quotient cannot see (*Step G85*'s routing).

**What would have to replace (GR-50)/(GR-51).** A feasibility criterion
for a **selection** — the map `v ↦ m(v)` choosing one of three branches
per hub — under a family of upper bounds indexed by the capacity-tight
chunks. GORIENT already named this frame at *Step G43* (*"choose minority
darts so that no capacity-tight chunk collects `N − 2` weaknesses… a
Hall-type condition over the tight-chunk hypergraph decides
feasibility"*), and (GR-56)(iii) has since replaced its two-block scan by
one scalar budget per chunk. That frame — **not** degree-constrained
orientation — is where (GR-51)'s analogue would live.

---

### Step G83 — (GR-64): the **collision bound** — a colouring-free lower bound on `d_fg` that prices the coupling between (Y)'s two quantifiers

The positive content of this pass. (GR-61)(ii) says `z_mono(S)` counts
interiors whose **minority dart is the exit**; (GR-65)(ii) will say
`dist(m, M)` counts hubs whose minority dart is **not** the matching
dart. Where a chunk's exit and the matching coincide, the two demands
collide — and that is the *only* place they interact.

> **(GR-64)** *(clauses (i)–(v) proven; (i) asserted at **209 432 030**
> (shape, admissible `z`, matching, proper chunk) instances with
> **3 449 374** at equality, the (iv) ceiling **attained** (per-chunk max
> exactly **2**) over the whole inventory, and every one of the **1250**
> prunes verified **sound** against the exhaustive ground truth;
> `--coll`, controls (3)/(4) of `--adv`)*
>
> Let `M` be a perfect matching, `m` a minority map, `d = dist(m, M)`,
> `S` a proper chunk. Put
> > `Coll_M(S) := {v ∈ Z2(S) : M(v) = β₃(v)}`,
> > `coll_M(S) := |Coll_M(S)| = |M ∩ ∂(W_S)| + 2 |M ∩ ch(S)|`
>
> (the interiors whose **matching** branch is their **free** branch).
> Then
>
> **(i)** `z_mono(S) ≥ coll_M(S) − #{v ∈ Coll_M(S) : m(v) ≠ M(v)} ≥ coll_M(S) − d`.
>
> **(ii)** If `m` is fully good then `d ≥ coll_M(S) − cap(S) + 6` for
> every proper chunk `S`.
>
> **(iii) Packing form.** If `𝒫` is a family of proper chunks with
> **pairwise disjoint** collision sets, a fully-good `m` at distance `d`
> from `M` satisfies
> > `d ≥ Σ_{S ∈ 𝒫} (coll_M(S) − cap(S) + 6)⁺ =: B_𝒫(M)`,
>
> and with `B(M) := max_𝒫 B_𝒫(M)`,
> > `d_fg ≥ min_M B(M)`,
>
> while any `M` with `B(M) > d_adm` **cannot anchor a fully-good
> optimum** — a colouring-free **prune** on (Y)'s matching quantifier.
>
> **(iv) The ceiling.** `coll_M(S) ≤ z(S)` and `cap(S) = 2z(S) + exc(S)`,
> so each term is `≤ 6 − z(S) − exc(S)`; a proper habitat chunk has
> `z(S) ≥ 2` (bridgelessness: `∂(W_S) = z − 2ch ≥ 2`) and `cap(S) ≥ 7`,
> hence **every term is `≤ 2`**, with `2` only at
> `(z, exc) ∈ {(3,1), (4,0)}` and `coll_M(S) = z(S)`. **No single chunk
> can demand more than two deviations**; an unbounded demand requires a
> packing.
>
> **(v) Parity.** `coll_M(S) ≡ |W_S| (mod 2)`, so a chunk with an odd hub
> set always has `coll_M(S) ≥ 1`.

*Proof.* (i): at `v ∈ Coll_M(S)` with `m(v) = M(v)` we get
`m(v) = β₃(v)`, i.e. `v`'s minority dart is its exit, i.e. `v` is counted
in `z_mono(S)` by (GR-61)(ii); the hubs of `Coll_M(S)` not so counted are
deviating, and there are at most `d` of those in total. (ii): full
goodness gives `z_mono(S) ≤ cap(S) − 6` ((GR-56)(iii), dropping
`|δ_S − σ_S| ≥ 0`). (iii): the deviating hubs charged at distinct
`S ∈ 𝒫` lie in disjoint sets, so their counts add; `d_fg` is a minimum
over `M` of such distances. (iv): the displayed arithmetic, with
`z(S) ≥ 2` because `W_S` proper in a bridgeless graph has `|∂(W_S)| ≥ 2`
and `∂(W_S) = z(S) − 2 ch(S)` (bridgelessness itself follows from the
(GR-25) cut criterion: both sides of a bridge would need `exc ≥ 5`,
totalling `≥ 10 > 6`). (v): each `M`-edge of `∂(W_S)` has exactly one end
in `W_S` and that end is an interior; chords in `M` contribute two. ∎

**What the sweep says, and what it does not.**

- **The inequality is tight, not slack**: **3 449 374** of
  **209 432 030** instances hold at equality, and the (iv) ceiling `2` is
  **attained**. The per-matching bound itself reaches **4**:
  `B(M)` distribution over all 24 671 (shape, matching) pairs is
  `{0: 19 633, 1: 3482, 2: 1068, 3: 380, 4: 108}` — so the *packing* does
  stack the `≤ 2` per-chunk terms, exactly as (iv) predicts it must.
- **`min_M B(M) = 0` at every one of the 4924 shapes.** So on this
  stratum the bound never lower-bounds `d_fg` above `0` — and that is
  itself the finding: *there is always an anchor matching whose collision
  statistic is chunk-wise slack.* Read against (GR-59) — which proved
  `min_M` **load-bearing**, no (a′) proof may fix its anchor matching —
  this is a *mechanism* for what the `M`-quantifier buys: it dodges
  collision-heavy matchings. Whether that is a theorem is **open**, and
  named as residual **(GR-64)(R2)** below; a proof would say the
  collision mechanism can never obstruct (a′).
- **The prune bites, and it is sound.** **1250** of **24 671** (shape,
  matching) pairs are killed by `B(M) > d_adm`, at **1156** shapes;
  **every** kill was verified against the exhaustive ground truth (no
  killed matching hosts a fully-good map at distance `≤ d_adm`). Its
  **incompleteness** is measured too: **7856** matchings host no
  fully-good optimum and are *not* killed — so the bound is a genuine
  necessary condition and far from sufficient. (`d_adm` itself, exact and
  uncapped: `{0: 368, 1: 2647, 2: 1908, 3: 1}`.)
- **The disjointness hypothesis in (iii) is load-bearing** (`--adv` (4)):
  dropping it — summing every positive term — exceeds the sound bound at
  **38** (shape, matching) pairs of the control sample and is outright
  **unsound** (exceeds a *realized* fully-good distance) at **27** of
  them.
- **E1(iv)/E2 detector.** `0` shapes have `min_M B(M) > d_adm`. Nothing
  here refutes (a′); had a shape fired, it would have exhibited
  `d_adm < d_fg` finite, which is **E2's refutation branch, not E1**
  (GADM clause (iv)).

**Cap disclosed.** Chunk enumeration is `gcap.two_ec_subsets`' `2^M`
scan, so this leg is the `n_hub ≤ 6` stratum plus W3M / W3 / W4 / NKo2v
(`E ≤ 18`). W5 (`E = 24`) and the necklaces (`E ≥ 45`) are **out of
reach for the chunk scan** — a disclosed cap, never a measured 0. The
large-`n` extension is residual **(GR-64)(R1)**: a positive-term chunk
has `z(S) ≤ 6`, `exc(S) ≤ 2` and `|∂(W_S)| ≤ 6`, i.e. it is a
**small-boundary** hub set, so the extension is a bounded-boundary
enumeration, not a `2^M` scan — a compute question, not a new idea.

---

### Step G84 — (GR-65): the **fit identity** — `dist(m, M)` and `z_mono(S)` are one statistic, which names what an instrument must control

> **(GR-65)** *(proven; clause (ii) asserted at **2 270 294** (shape,
> admissible `z`, matching) instances over the whole inventory, 0
> failures; `--fit`)*
>
> For a hub `v` and `β ∈ star(v)` say `m` **fits** the selection `β` at
> `v` if `m(v) = β`. Then, at an admissible `z`:
>
> **(i)** `m(v) = β` **iff** the two darts at `v` other than `β`'s have
> **equal** colour.
>
> **(ii)** `dist(m, M) = n − #{v : the two non-`M` darts at v agree}` —
> the deviation count is `n` minus the fit count against the selection
> `v ↦ M(v)`.
>
> **(iii)** `z_mono(S)` is the fit count against the **exit selection**
> `v ↦ β₃(v)`, over the interiors of `S` ((GR-61)(ii)).
>
> **(iv)** Hence **input (Y) is a simultaneous fit-extremization on one
> statistic**: find an admissible `m`, a matching `M` and (when
> `d_adm > d_par`) a `Z`, with `fit(M)` **maximal** (`= n − d_adm`) while
> `fit(exit_S)` is **capped** by `cap(S) − 6 − |δ_S − σ_S|` at every
> proper chunk `S`, and `δ = 0`.
>
> **(v)** `fit` is a function of the minority **branch identity** at each
> hub — of *which* of the three darts is the odd one out. The (GR-50)
> orientation model records only *how many* darts at each hub are A,
> which determines `c(v)` and not `m(v)`. So the orientation model is
> precisely the quotient of the admissible cube that forgets the datum
> **both** of (Y)'s constraints read. This is (GR-62) restated
> intrinsically.

*Proof.* (i): admissibility makes the three dart colours a 2–1 split, so
the minority dart is `β`'s exactly when the other two agree. (ii)–(iii)
are (i) at the two selections, and (iv)–(v) are the restatement. ∎

**Why this is worth a label rather than a remark.** It converts (Y) from
*"a balance-type condition and a distance-type condition"* into *one
extremal problem in one statistic*, which (a) makes (GR-64) a two-line
consequence rather than a construction, (b) locates the tension exactly —
at interiors whose matching branch leaves the chunk — and (c) states the
successor's design constraint without reference to any particular
instrument: **an instrument for (Y) must be a statement about selections,
not about dart-colour counts.**

---

### Step G85 — (GR-66): GBAL's own certificate measured against (Y) — and where this leaves input (Y), (a′), E3 and the (GR-15) line (hand-off)

> **(GR-66)** *(measured, exhaustive over the 4924-shape inventory; every
> certificate re-verified through `gbal.verify_balanced` and accepted by
> `cflank.admissible`, the (GR-37)(i) ground truth; `--cert`)*
>
> Run (GR-54)'s own construction — `gbal.balance_oracle`: the first
> feasible balanced odd pattern, then a degree-constrained orientation —
> at every inventory shape, and compare its minority map against (Y)'s
> two constraints. Then:
>
> **(i)** its deviation distance `min_M dist(m, M)` **exceeds `d_adm`** at
> **3514 of 4924** shapes and equals it at only **1410**; the gap
> `dist − d_adm` distributes as
> `{0: 1410, 1: 1249, 2: 2172, 3: 2, 4: 91}`;
>
> **(ii)** it is **fully good** at **4273 of 4924** — so it fails (Y)'s
> chunk constraints outright at **651**.
>
> At the four named shapes: **W3M** `d_adm = 2`, certificate distance
> **4**, fully good; **W3** `d_adm = 3`, distance **5**, fully good;
> **W4** `d_adm = 2`, distance **5**, **not** fully good; **NKo2v**
> `d_adm = 2`, distance **5**, fully good.
>
> The construction carries **no distance datum and no chunk datum**;
> (i)–(ii) measure that this is not a formality.

**Reading.** Even granting a hypothetical chunk-aware (GR-51) analogue,
GBAL's certificate would still need a **distance-aware selection rule**,
and the z-form has no coordinates for one — no matching appears in it.
(GR-55)'s `(y, Z, φ)` coordinates do. So the honest conclusion is a
**composite**, not either override:

- **the chunk rung wants the z-form** ((GR-61)): one bit per branch,
  four invariants read locally off the dart colouring;
- **the distance rung wants the coset coordinates** ((GR-55)): the
  `M`-avoiding affine space of dimension `n/2 − 1`, where "minimum
  weight" is a statement one can quantify over;
- **(GR-65)'s `fit` is the bridge**, and **(GR-64)** is the first
  inequality linking the two rungs.

**The coordinator's routing override, re-scoped by this pass** (recorded,
scoped, traceable — the GPSA/GADM precedent). The override was right that
GBAL's instrument absorbs the matching apparatus for the **balance**
question, and right to try the localization first: it is cheap and it
either lands or produces a precise obstruction, which is what happened.
It was wrong only in the inference *"therefore the instrument is the
first thing to try on (Y)"* being **exclusive**: GLAW's clause —
matching-flexibility instruments on the `M`-avoiding coset space — is
**reinstated for the distance rung specifically**, because that rung is
the one GBAL's instrument dissolves *and loses*. Neither clause is wrong;
they address different rungs of one statement.

- **The route ledger** (coordinator updates on landing):
  **Entry 1** (uniform fully-good existence at `Λ = ∅`, `D = 0`) —
  **OPEN, unchanged in status**; **(a′) stays its primary and still
  carries NO bar**. What moved is the route map, not the status: the
  pinned GBAL-localization route is **DEMOTED by witness** ((GR-62)), its
  break point **located** ((GR-63)), and input (Y) acquires its first
  quantitative coupling ((GR-64)) and a coordinate-free restatement
  ((GR-65)). **Entry 5** — **untouched** (PROVEN by (GR-54); one
  measurement about its certificate, (GR-66), which does not move its
  status). **(b′)** — untouched; **BALB's target this wave**, and the one
  by-product below is reported and **not developed**. Entries 2–4
  unchanged.
- **TERMINATION check** (coordinator's to run; this draft's reading).
  **E1 does NOT fire** — no g-flank; nothing here exhibits a shape whose
  every admissible colouring binds. Clause **(iv)** applied explicitly:
  **nothing found min-form `d_adm < d_fg`**, finite or infinite. `d_fg`
  is never *computed* in this pass — the (a′) verdict is **consumed from
  (GR-58)**, not re-derived — and the one `d_fg`-directed quantity here
  is (GR-64)'s **lower bound**, whose detector reports `0` shapes with
  `min_M B(M) > d_adm`. Clause **(v)** applied explicitly: `d_adm` is
  computed **exactly, by exhaustive `z`-cube enumeration with no
  deviation cap**, at every one of the 4924 inventory shapes and is
  **finite at every one** — on the safe side, and a corroboration of
  (GR-54)'s proof that clause (v) is unfirable at `Λ = ∅`, `D = 0`, not a
  new claim. Clause (iii) is respected: nothing here is a large-`d`
  claim. **E2 does NOT fire** — (a′) is neither refuted nor
  unprovable-as-posed; what is refuted is a **route** ((GR-62)) and a
  **predicted obstruction location** ((GR-63)), and a route demotion is
  explicitly not an E2 event; the successor is named above and below.
  **E3 is ARMED (by GBAL's entry-5 HIT) and does NOT fire** — E3's target
  is **entry 1**, and (a′) did **not** HIT here. **Stated as the dispatch
  required:** an (a′) HIT *would* fire E3, whose consequence is that the
  coordinator surfaces a **phase-shape decision to the user** instead of
  dispatching a successor (with GORIENT's retained deviation: the
  Lean-hold question goes to the user). **This draft does not fire it,
  and must not — firing is a coordinator action.**
- **The successor's natural routing** (this draft's reading; the dispatch
  is a coordinator/user call, not made here): **input (Y), attacked as a
  two-rung selection problem** — (GR-61)'s z-form for the chunk
  arithmetic, (GR-55)'s coset/SDR coordinates for the distance, (GR-65)'s
  `fit` as the single statistic, and a **Hall/deficiency condition over
  the tight-chunk hypergraph of exit selections** as the instrument to
  try in place of degree-constrained orientation (GORIENT *Step G43*'s
  frame, now with one scalar budget per chunk by (GR-56)(iii)).
  Two sub-targets fall out and are strictly smaller than (Y):
  - **(GR-64)(R2)** *"every habitat shape carries an anchor matching `M`
    with `B(M) = 0`"* — measured at all 4924 shapes, **open** as a
    theorem. It would prove the collision mechanism can never obstruct
    (a′), and it is a statement about matchings and small-boundary hub
    sets alone: no colouring, no rank, no deviation ladder.
  - **(GR-64)(R1)** the large-`n` extension of the collision sweep, a
    bounded-boundary enumeration rather than a `2^M` scan.
  Behind (Y): **(b′)**, **(c)** AA-glue realizability at `n_hub ≥ 8`,
  **(d′)** the corner-armed seed hunt.
- **One (b′)-relevant by-product, reported and NOT developed** (BALB owns
  (b′) this wave, per the spec's bar): (GR-65)(ii) expresses the
  *deviation count* in the same dart-colour language ((GR-49)) in which
  (GR-50) decides *balance*, so `d_adm − d_par` becomes a statement about
  two `fit` counts against two selections (a matching and the parity
  optimum's) on one colouring. Recorded for BALB / the successor;
  nothing here measures or claims a gap bound.
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**, and
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **(GR-15) OPEN,
  unchanged in both directions; no gap-map status moves** — the
  (K-grid) row's *four named dispatchable attacks* list is unchanged
  ((a′) still first, still no bar), and the row gains only that input
  (Y)'s pinned GBAL-localization route is demoted with its break point
  located. (GR-37)(iii)'s flag stays exactly as GLAW left it
  (**HALF-retired**). No landed figure moves.

---

### Verification (Steps G80–G85)

`notes/scripts/w4/yloc.py` (**new with this pass**, untracked at draft
time; imports — all **read-only** — `cflank` (`admissible`,
`cubic_habitat`), `gcap` (`pool_specs`, `branch_stats`), `gunif`
(`WITNESSES`), `gexist` (`fully_good_rank`), `gorient` (`cm_colouring`,
`cm_solve`, `odd_balance`, `prep_shape`, `perfect_matchings`,
`m_of_matching`, `fully_good_scan`), `gbal` (`dart_col`, `z_admissible`,
`z_to_map`, `map_to_z`, `odd_idx`, `z_pattern`, `balance_oracle`,
`verify_balanced`, `bounds_of`, `balanced_patterns`), `glaw`
(`chunk_inv`, `hm_spec_map`), `gdev` (`nk_specs`), `gadm`
(`nko_specs`), `gpsa` (`branches_at`, `nkp_specs`, `nk55_specs`,
`nko2v_specs`)). Rank enters **only** through `gexist.fully_good_rank`,
on the (GR-62) witness pair (README §4 convention 2). Local devices, none
shadowing a §1 primitive: `chunk_static` / `chunk_inv_z` (the (GR-61)
translation — `glaw.chunk_inv` stays the **oracle**, this is the object
under test), `good_z` (the (GR-56)(iii) criterion in `z`, asserted equal
to `gorient.fully_good_scan`), `adm_zs` (the admissible cube),
`indeg_of` (the (GR-50) degree read-off), `collide` / `coll_terms` /
`pack_bound` (the (GR-64) statistic), `dist_of` / `fit_M` (the (GR-65)
identity), `matb`, `is_balanced_z`, `d_adm_exact`, `pool_shapes` /
`named_small` / `all_shapes` / `shape_ctx` (inventory bookkeeping).

**One independent cross-check of the `d_adm` this pass computes.** `d_adm`
here is an **exhaustive z-cube** minimum over all balanced
`cflank.admissible` configurations and all perfect matchings, with no
deviation cap — a different enumeration from GLAW's, which walks the
(GR-55) `(y, Z, φ)` coset triples. They agree where the record pins a
value: this pass returns `d_adm(W3) = 3`, and the landed record
(*Steps G48–G52*, as corrected by GADM *Step G56*) has
`d_par(W3) = 2 < d_adm(W3) = d_fg(W3) = 3`. **No landed figure moves**,
and nothing here re-derives (GR-58)'s census: `d_fg` is never computed in
this pass at all.

**No geometry is sampled anywhere in this pass** — every object is a hub
multigraph, a branch colouring or a perfect matching — so the standing
`plane_basis` degeneracy guard has no sampled placement to protect. It is
discharged instead by routing **every** structural verdict through a
landed oracle and asserting agreement: `cflank.admissible` for
admissibility, `gorient.fully_good_scan` for full goodness,
`glaw.chunk_inv` for the (GR-56) invariants, `gbal.verify_balanced` for
every (GR-54) certificate, and `gexist.fully_good_rank` for the (GR-62)
witness pair. Exact integers / GF(2) only; no floating point; the two
rngs are seeded from `R_SEED = 20260819` and printed.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --loc     # ~278 s  (GR-61): 31 047 708 (z, chunk) pairs vs glaw.chunk_inv; the z(S)=0 degeneracy; the 10-shape exceptional family; the chunk-count growth
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --fibre   #  ~38 s  (GR-62): 217 468 degree fibres, 7982 split at 1499 shapes; the rank-certified n_hub = 4 witness pair
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --par     #   ~4 s  (GR-63): (GR-52)'s counting identity at all 305 704 (shape, hub subset) pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --coll    # ~459 s  (GR-64): 209 432 030 collision instances, the <= 2 ceiling + its profile + the parity, the packing bound, the 1250 sound prunes, exact uncapped d_adm
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --fit     #  ~28 s  (GR-65): the fit identity at 2 270 294 instances
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --cert    #  ~45 s  (GR-66): GBAL's certificate vs exact d_adm and vs full goodness
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --adv     #  ~34 s  F13: five controls, all must fire
PYTHONHASHSEED=0 python3 notes/scripts/w4/yloc.py --validate  # ~890 s -- OVER the 600 s foreground budget
```

**Budget note for the landing dispatch** (the README's *Two invocations do
not fit a 600 s foreground budget* row, extended by one entry): `--validate`
runs **~890 s** and therefore does **not** fit a foreground sitting;
`--coll` (~459 s) and `--loc` (~278 s) each fit **alone**, and the other
five together run under 150 s. So the landing gate is: run `--coll`
alone, run `--loc` alone, run the rest in one invocation — or run
`--validate` backgrounded-*first* with the foreground work alongside it
(the README's dispatched-agent reading; never backgrounded with nothing
left to do). Every figure quoted in *Steps G80–G85* was produced at
`PYTHONHASHSEED=0` and re-confirmed per mode after the driver's last
edit.

**The F11 table — which driver mode tests which sentence.**

| sentence | mode | what is asserted |
|---|---|---|
| (GR-61)(i)–(v): the four chunk invariants are these z-formulas | `--loc` | equality with `glaw.chunk_inv` at **31 047 708** (admissible `z`, chunk) pairs over 4924 shapes; the z-side criterion equal to `gorient.fully_good_scan` at all **433 938** admissible `z` |
| (GR-61)(vi): `E(G°)` is the **unique** interior-free chunk | `--loc` | `#{chunks with z(S)=0} = #{shapes}` and every one improper |
| (GR-61) exceptional family: the premise holds at exactly 10 shapes | `--loc` | per-shape count of proper (chunk, pattern) cells with non-constant `z_mono` (**1 719 029** such cells at **4914** shapes); the 10 exceptions classified by `(n_hub, #even branches)`: `{(2,1): 9, (4,0): 1}` |
| (GR-63)(ii): the chunk family has no shape-independent cap | `--loc` | mean proper chunks per shape by `n_hub`: `{2: 3.0, 4: 12.8, 6: 45.9, 8: 163.0, 10: 543.5, 12: 1148.0}` |
| (GR-62)(i): balance **is** a degree statement | `--fibre` | balance constant on every one of the **217 468** `(p, indeg)` fibres |
| (GR-62)(ii): full goodness is **not** | `--fibre` | **7982** split fibres at **1499**/4924 shapes + the explicit `n_hub = 4` witness pair, **rank-certified** both ways |
| (GR-62)(iii): **no** degree criterion can decide it | `--adv` (5) | the *best possible* degree-only classifier's irreducible error is **26 of 252** at W3M — the "no instrument exists" claim gets its own quantitative test, per F11's treatment of "the only"/"forced" |
| (GR-63)(i): (GR-52)'s step is per-subset | `--par` | `Σ_{v∈R} a_v = 2 e_H(R)` at all **305 704** (shape, hub subset) pairs — every `R` of every inventory shape |
| (GR-64)(i): `z_mono(S) ≥ coll_M(S) − d` | `--coll` | asserted at **209 432 030** (shape, `z`, matching, proper chunk) instances, **3 449 374** tight |
| (GR-64)(iv): the per-chunk ceiling is **2** | `--coll` | per-chunk term max over the inventory asserted `≤ 2` and **attained** (`= 2`), while the packed bound reaches **4** |
| (GR-64)(iv): the ceiling **profile** — term `= 2` only at `(z,exc) ∈ {(3,1),(4,0)}` with `coll = z` | `--coll` | asserted at every (proper chunk, matching) pair of the inventory whose term equals 2, together with `z(S) ≥ 2` at every proper chunk (the step (iv)'s proof uses) |
| (GR-64)(v): `coll_M(S) ≡ \|W_S\| (mod 2)` | `--coll` | asserted at every (proper chunk, matching) pair of the inventory |
| (GR-64)(iii): the prune is **sound** | `--coll` | all **1250** killed matchings checked against exhaustive ground truth, 0 unsound; incompleteness **7856** counted too |
| (GR-64)(iii): **disjointness is load-bearing** | `--adv` (4) | the naive sum exceeds the sound bound, and is **unsound** against a realized fully-good distance |
| (GR-64): the bound is neither empty nor always-on | `--adv` (3) | positive at **323** (shape, `M`) pairs, vacuous at **1229** |
| `min_M B(M) = 0` everywhere (**measured**) | `--coll` | the min-over-`M` distribution: `{0: 4924}`, cap disclosed |
| E1(iv)/E2 detector | `--coll` | `#{shapes : min_M B(M) > d_adm} = 0`; a nonzero count would be the headline |
| E1(v): `d_adm < ∞` | `--coll` | exact `d_adm` by exhaustive `z`-cube, **no cap**, finite at every shape: `{0: 368, 1: 2647, 2: 1908, 3: 1}` |
| (GR-65)(ii): the fit identity | `--fit` | `dist(m, M) = n − fit_M` at **2 270 294** instances |
| (GR-66): GBAL's certificate misses both constraints | `--cert` | its distance vs exact `d_adm` (above the optimum at **3514**/4924) and its full-goodness verdict (**4273**/4924), per shape, all 4924 |
| the (GR-61) translation is *tested*, not vacuous | `--adv` (1) | a sign-flipped `δ` **must** disagree with the oracle — **27 647** disagreements |
| `\|δ_S − σ_S\|` is load-bearing in `z` too | `--adv` (2) | dropping it misclassifies **452** of **23 518** admissible colourings (GLAW's (GR-56) F13 control, re-run on this pass's own evaluator). **Recorded because it is a live trap:** on the `n_hub ≤ 6` pool *alone* the count is **0** — the term only bites at the named larger shapes, which is why they are in the control sample |

---

### Confidence verdict (Steps G80–G85)

| claim | verdict |
|---|---|
| **(GR-61)** the z-form translation of the four chunk invariants, and the `Z2(S) = ∅ ⟺ S = E(G°)` degeneracy | **proven-informally** (short proofs; machine-asserted exhaustively against the landed oracle) |
| **(GR-61)** the 10-shape exceptional family (the localization premise's exact boundary) | **proven-informally at the swept inventory** — an exhaustive statement about `n_hub ≤ 6` plus four named shapes, *not* a general theorem about the boundary; its characterization ("no even-branch freedom") is a reading, not a proof |
| **(GR-62)(i)–(iii)** full goodness is not a degree predicate, so the chunk system is not a degree-constraint system and (GR-51)'s criterion does not apply | **REFUTED by witness** (of the pinned route's step 2), hence the negative statement is **proven**; the witness is rank-certified. **Scoped by (iii′):** what is excluded is a *(GR-51)-shaped* criterion (feasible set cut out by in-degree bounds), **not** every conceivable existence criterion — a shape's existence question is trivially a function of its odd pattern |
| **(GR-63)(i)–(ii)** (GR-52) localizes for free; the break is at (GR-50)→(GR-51); (GR-53) is a second obstruction | **proven-informally** ((i) an identity, machine-asserted; (ii) a chain audit whose only load-bearing new link is (GR-62)); the coordinator's predicted obstruction is **REFUTED as stated** |
| **(GR-63)(iii)** (X) and (Y) differ in **quantifier**, not only in argument | **proven-informally** (a reading of (GR-54) vs (GR-60), with (GR-66) as its measurement) |
| **(GR-64)(i)–(v)** the collision bound, its packing form, the `≤ 2` ceiling and its profile, the parity | **proven-informally** (three-line proofs; (i), (iv) — including the `(z,exc) ∈ {(3,1),(4,0)}` profile and the `z(S) ≥ 2` step — and (v) all machine-asserted exhaustively over the inventory; the prune's soundness checked against exhaustive ground truth) |
| **(GR-64)** `min_M B(M) = 0` at every shape | **measured, not proved** — exhaustive at `n_hub ≤ 6` + four named shapes, cap disclosed; open as residual **(GR-64)(R2)** |
| **(GR-65)(i)–(v)** the fit identity and its two readings | **proven-informally** (one-line identity; machine-asserted) |
| **(GR-66)** GBAL's certificate versus (Y)'s two constraints | **measured** (exhaustive over the inventory; every certificate re-verified through the landed oracles) |
| **input (Y) / (a′)** | **OPEN, unchanged in status.** Not hit, not refuted. The *pinned route* is demoted; the *target* is untouched |
| **(GR-15)** | **OPEN**, unchanged in both directions; no gap-map status move |

---

### What would change this (Steps G80–G85)

- **(GR-62) overturned** would need a *degree-only* invariant that
  separates the witness pair — impossible as stated, since the two
  members share the odd pattern **and** the in-degree vector. What could
  legitimately reopen step 2 is a **different** orientation model: e.g.
  orienting a modified graph (splitting each hub into three darts and
  encoding the minority choice as a degree condition there). That is a
  *new* model, not (GR-50), and it is the one repair this pass did not
  attempt — worth naming as a live option rather than a closed door.
- **(GR-63) overturned** would need a reading of (GR-52) in which the
  count is not per-subset. The driver's identity forecloses that at every
  hub subset of every inventory shape; only a *different* (GR-52) would
  reopen it.
- **(GR-64) strengthened** by any of: keeping `|δ_S − σ_S|` in (ii)
  (dropped for a colouring-free bound; a colouring-aware version is
  strictly stronger and still cheap); a laminar/uncrossing argument
  ((GR-38)) turning the packing into a min-max; or the large-`n`
  extension (R1). **Weakened** by a shape where a killed matching does
  host a fully-good optimum — that would refute (i) or the arithmetic,
  and the driver asserts against it.
- **(GR-64)(R2) proven** — every shape carries an anchor matching with
  `B(M) = 0` — would remove the collision mechanism as an obstruction to
  (a′) outright. **Refuted** by one shape where every perfect matching
  has `B(M) ≥ 1`: then (GR-64) becomes a genuine floor on `d_fg`, and the
  comparison with `d_adm` becomes a live E1(iv)/E2 question at every
  larger stratum. Either outcome is a real result; this is the sharpest
  cheap sub-target the pass produced.
- **(GR-66) reread** if a future pass makes (GR-54)'s construction
  *choose* among feasible balanced patterns and orientations (the oracle
  takes the **first**). The measurement is about the construction as
  landed, not about the best certificate the model can produce — a
  distance-minimizing search inside the model is exactly the missing
  ingredient, and measuring it is a cheap follow-up.
- **The whole verdict is scoped to the swept inventory.** Everything is
  `n_hub ≤ 6` plus W3M / W3 / W4 / NKo2v; W5 and the necklaces are out of
  reach for the chunk scan. A large-`n` counterexample to any *measured*
  clause is not excluded by anything here.


---

### Steps G86–G91 (2026-08-19, direction BALB) — **(b′)'s PRICE half becomes a THEOREM and its AVAILABILITY half is re-shaped at an exact boundary**: **(GR-67)** anchors the z-form at a perfect matching — the perfect-matching instance of GLAW's landed (GR-65)(i) fit identity, independently re-derived and now corroborating it — where the deviation count is a **2-factor sign-change count** and a one-line branch sum gives the **PARITY LAW** `dist(m, M) ≡ #{even branches outside M} (mod 2)` for *every* parity-consistent map — so **every per-matching layer gap is EVEN** and per-matching (b′) is the dichotomy *gap 0 or gap ≥ 2*; **(GR-68)** prices **every** legal (GR-45)/(GR-49) move in closed form, `Δdist = |W(F) ∖ S| − |W(F) ∩ S|` with `W(F)` the endpoints of `F`'s path components inside the 2-factor — so matching branches and whole 2-factor cycles are **FREE**, `|Δdist| ≤ 2·(number of path components)`, and a **single-path repair costs at most 2 REGARDLESS of its length**, which proves the "one repair unit costs 2" half of (b′)'s decomposition outright; **(GR-69)** proves the **imbalance ceiling** `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` from the *necessity* half of (GR-51)(i)(a) alone, so `|δ| ≤ 2` is a **theorem at `n_hub ≤ 6`** — the whole stratum — and **FALSE from `n_hub = 8`**, realized at the Wagner habitat shape V8, with the ceiling **tight at `n_hub = 2, 4, 6, 8, 10, 12`**; **(GR-70)** reduces per-matching (b′) to **one availability clause** and verifies it **EXHAUSTIVELY** over all 4780 odd-carrying habitat shapes (all 23 939 (shape, matching) pairs, all 96 930 unbalanced parity-optimal configurations, full `3^n` censuses, no cap) — while **REFUTING** the landed T1-only instance of that clause **from `n_hub = 8`** with stuck witnesses at `n_hub = 8, 10, 12`, each repaired at price **0** by a named **mixed-pair** move; **(GR-71)** carries (b′) to 536 exact shapes at `n_hub = 8/10/12` and to **cap-free per-matching certificates** at `n = 30`; **(b′) stays OPEN, NOT a HIT** (its price half is proven, its availability half is not), **(GR-15) stays OPEN, no gap-map status move on `hK` itself**

Answering `notes/Pencil-fanout.md` §"Twenty-first direction — BALB
(seventh fan-out)": **(b′), the balance-layer bound `d_adm − d_par ≤ 2`**
— open and supported since GDEV, ridden as a *secondary* three times
(GADM *Step G56*, GPSA *Step G61*, GDESC *Step G66*) and a **primary**
for the first time. Rank-free throughout: nothing imports or calls
`gexist.fully_good_rank`, and **no `d_fg` claim is made anywhere** —
(a′) / input (Y) is direction YLOC's target this wave, and the one
(Y)-relevant by-product is *reported* below, not developed. Read against
*Steps G68–G73* ((GR-49)–(GR-54)), *Steps G58–G62* ((GR-44), (GR-45)),
*Steps G63–G67* ((GR-46)–(GR-48)) and *Step G49* ((GR-41)).

***Notation, inherited unchanged.*** `δ` is the odd-branch imbalance
`a − b` and nothing else (`a` = #A-coloured odd branches, `b` = #B; A is
colour 0); **cuts are written `∂(S)`**. `O` is the set of odd branches,
`2k = |O| ≤ 6` and even (*Step G53*(ii)); `τ = [ℓ even] ∈ GF(2)^E`;
`Φ = τ + Cut(G°)`; `z ∈ GF(2)^E` is §(K-grid) (GR-49)'s one bit per
branch and `ζ(v, β)` its dart colour; `H` is the set of even branches;
`n = n_hub`, `M = |E| = 3n/2`. **New in this pass and used
throughout:** a perfect matching `M` is fixed and written `M`; `F` is
its complementary **2-factor** `G° ∖ M`; `S` is the set of hubs at which
the minority map deviates from `M`; `W(F)` is defined at *Step G87*.
Layers as landed: `d_par(M)`, `d_adm(M)`, `d_fg(M)` are the minimum
deviation counts from `M` over parity-consistent / admissible
(= parity-consistent **and balanced**) / fully-good maps, and
`d_• = min_M d_•(M)`.

**Step 0 pin (mandatory, discharged before any derivation).**
(GR-37)(i)/(ii) in full (the `(c, m)` model, the per-branch equation, two
`c`-solutions at fixed `m`, the A↔B swap). (GR-41) (`Φ = τ + Cut(G°)`;
the floor). (GR-44) in full (`d_par(M) = w_M` exact, Hall automatic, the
SDR construction) — **consumed as the record and not re-derived**.
(GR-45) in full (the legal-move calculus, T1/T2, the flip formula) and
(GR-46) (one-move transitivity; Cor. 1, Cor. 2). (GR-47), (GR-48) (the
reduction criterion, K1/K2/K3, the doubly-blocked kill and its realized
`n = 30` witnesses). (GR-49)–(GR-54) in full — in particular (GR-49)'s
**flip-set legality test** (`F` carries an admissible `z` to an
admissible `z + χ_F` iff at every hub `[m(v) ∈ F] = [|F ∩ star(v)| ≥ 2]`),
(GR-50)'s `o_v`/`q_v`/`d_v`/`l_v`/`u_v`, (GR-51)(i)(a)/(b) and its weight
table, and (GR-54)'s theorem with its scope line *"It does not move
(b′)"*. *Step G53*(ii) (`2k ≤ 6`, evenly many). The measured (b′) record
with its qualifiers: gaps `{0, 1, 2}`; W3 `(d_par, d_adm, gap) = (2, 3, 1)`;
GDESC *Step G66*'s min `|δ|` at parity-optimal maps `{0: 92, 2: 2}` over
94 shapes; the necklace shift layer **UNBOUNDED** ((GR-43)); (GR-4′)
covers no habitat block.

---

### Step G86 — (GR-67): the M-anchored z-form — the deviation count is a 2-factor sign-change count, and its PARITY is a matching invariant

**Why the pass starts here.** (GR-49) turned the balance question into
one bit per branch and (GR-50)/(GR-51) decided it exactly. But (b′) is
not a question about *which* configurations exist; it is a question about
**how far they are from a perfect matching**, and the z-form as landed
says nothing about that distance — GBAL's own scope line records exactly
this. The first move is therefore to express `dist(·, M)` in `z`.

> **(GR-67)** *(proven; certified EXHAUSTIVELY — the anchored identity at
> 2 188 534 (shape, matching, parity-consistent map, potential)
> quadruples over 24 661 (shape, matching) pairs, covering the **whole**
> `Λ = ∅`, `D = 0` pool (all 4920 shapes, all-even included) plus
> W3M/W3/NKo2v, and the parity law at all 1 094 267 (matching, map)
> pairs; `--anchor`)*
>
> Let `G°` be cubic and loop-free and `M` a perfect matching, so
> `F := G° ∖ M` is a **2-factor** — every hub has exactly two non-`M`
> branches `f_1(v), f_2(v)`, and `F` is a disjoint union of cycles
> covering every hub.
>
> **(i) The anchored identity.** For every admissible `z`,
> > `m(v) = M(v)` ⟺ `ζ(v, f_1(v)) = ζ(v, f_2(v))`,
>
> hence
> > `dist(m, M) = #{v : ζ(v, f_1(v)) ≠ ζ(v, f_2(v))}`.
>
> The deviation count is therefore a function of **`z|_F` alone** — a
> count of *sign changes* read around `F`'s cycles. Call the counted
> hubs the **changeover** hubs; they are exactly `S`.
>
> **(ii) The parity law.** For every parity-consistent `m`,
> > `dist(m, M) ≡ #{even branches outside M}  (mod 2)`.
>
> **(iii) The changeover parametrization.** On each cycle `C` of `F`,
> > `#(S ∩ V(C)) ≡ #{even branches in C}  (mod 2)`,
>
> and conversely `z|_C` is determined by the changeover set together with
> one base bit per cycle.

*Proof.* (i) At a hub the three dart colours are 2–1 ((GR-49)). Write
`s = ζ(v, M(v))`, `t_i = ζ(v, f_i)`. If `t_1 = t_2` then admissibility
forbids `s = t_1`, so the minority dart is `M(v)`'s. If `t_1 ≠ t_2` then
one of them equals `s`, so two darts carry `s` and one carries `s̄`, and
the minority dart is a non-`M` one. ∎

(ii) Sum the indicator of (i) over all hubs. Each **non-`M`** branch `β`
contributes its two darts, one at each end, and `ζ(u, β) ⊕ ζ(w, β) = τ_β`
by (GR-49)'s definition; each `M`-branch contributes nothing. So
`Σ_v (ζ(v,f_1) ⊕ ζ(v,f_2)) ≡ Σ_{β ∉ M} τ_β`, which is the number of even
branches outside `M`. ∎

(iii) Travel round `C`: the dart colour changes by `τ_β` across a branch
and by the changeover indicator across a hub, and the total change is 0.
∎

**Cross-reference — (i)/(ii) is the perfect-matching instance of the
landed (GR-65)(i), independently re-derived.** GLAW's *Step G84* already
proves, for **any** per-hub selection `β`, that `m` fits `β` at `v` iff
the two non-`β` darts agree, hence `dist(m, M) = n − #{v : the two
non-`M` darts agree}` — the exact complement of the identity above at
the selection `β = M(v)`. This pass derived (i)/(ii) independently,
blind to (GR-65) (concurrent seventh-fan-out dispatches), and each side
certified its own construction exhaustively with 0 failures (GLAW:
2 270 294 (shape, admissible `z`, matching) instances via `--fit`; this
pass: 2 188 534 (shape, matching, map, potential) quadruples via
`--anchor`) — a genuine **corroboration**, the wave's third such
convergence (after OCON/FRES and YLOC/BALB's own (GR-65)/(GR-67)(i)
pairing is itself one instance of it). What this pass adds beyond the
identity is new: the **parity law** (ii) and the **changeover
parametrization** (iii), neither in (GR-65).

**Corollary 1 — every per-matching layer gap is EVEN.** `d_par(M)`,
`d_adm(M)` and `d_fg(M)` are minima of `dist(·, M)` over three nested
sets of parity-consistent maps, so by (ii) **all three have the same
parity**. Hence
> `d_adm(M) − d_par(M)`, `d_fg(M) − d_adm(M)` and `d_fg(M) − d_par(M)`
> are all **even**,

and **per-matching (b′) is a dichotomy: the gap is 0, or it is `≥ 2`** —
a violation cannot creep up by one, it must jump to 4. Verified: the
per-matching gaps over the whole stratum are `{0: 23 444, 2: 495}` —
even at every one of the 23 939 pairs (*Step G89*).

**Corollary 2 — why the *shape*-level gap can be odd.** The parity
constant `#{even branches outside M}` **depends on `M`**, so distances
from different matchings need not share a parity, and
`d_• = min_M d_•(M)` can mix them. That is the recorded explanation of
the arc's `{0, 1, 2}` shape-level histogram, and of W3 specifically:
`d_par = 2`, `d_adm = 3`, gap **1**, with per-matching gaps `[0, 2]`
(*Step G90*) — the odd shape-level gap is a matching-parity artifact, not
a balance phenomenon.

**Corollary 3 — the cycle floor.**
`d_par(M) ≥ #{cycles of F carrying an odd number of even branches}`,
immediate from (iii). Asserted at 24 661/24 661 (shape, matching) pairs,
**tight** at 11 266 of them.

**The odd-branch dart dictionary, recorded because *Step G89* runs on
it.** For an odd branch `γ` with ends `u, w`: `τ_γ = 0`, so both darts
carry `z_γ`, and the minority dart at `u` lies on `γ` iff
`z_γ ≠ c(u)`. Hence
> `γ` is **dart-free** ⟺ `c(u) = c(w) = z_γ`,

i.e. a majority-side odd branch is T1-blocked exactly when one of its
ends has the *opposite* potential.

---

### Step G87 — (GR-68): the price of a legal move, in closed form — matching branches and whole 2-factor cycles are FREE, and a single-path repair costs at most 2 whatever its length

> **(GR-68)** *(proven; the general formula asserted at 508 816
> (configuration, **legal** flip set) pairs — every one of the `2^M`
> subsets tested for legality at every parity-consistent configuration of
> every sampled shape and **every** perfect matching — and the
> single-path specialization at 4 419 364 (admissible `z`, F-path) pairs,
> 879 560 of them legal, with the legality criterion agreeing with
> `gbal.flip_legal` at every one; `--flip`, F13 control `--adv` (2))*
>
> Let `F ⊆ E` be a **legal** flip set at an admissible `z` ((GR-49)), and
> put
> > `W(F) := {v : exactly one of f_1(v), f_2(v) lies in F}`.
>
> **(i) The price.**
> > `Δdist = |W(F) ∖ S| − |W(F) ∩ S|`.
>
> **(ii) What `W(F)` is.** `W(F)` is the set of odd-degree hubs of the
> subgraph `F ∖ M` **inside the 2-factor** — i.e. the **endpoints** of its
> path components. So `|W(F)| = 2·t(F)` with `t(F)` the number of those
> path components, and
> > `|Δdist| ≤ 2·t(F)`.
>
> **Branches of `M` and whole `F`-cycles inside `F` contribute nothing to
> `W(F)`: they are FREE.**
>
> **(iii) The single-path move.** Let `A` be the branch set of a proper
> contiguous path of one `F`-cycle, with endpoint hubs `e_1, e_2` and
> interior hubs `I`. Then `A` is legal iff **every hub of `I` deviates
> from `M`** and **neither endpoint holds its minority dart on its
> `A`-branch**; the price is `Σ_{i} (+1 if e_i ∉ S else −1) ∈ {−2, 0, 2}`,
> **independent of `|A|`**; and the odd-branch pattern flips exactly on
> `A ∩ O`.
>
> **(iv) The two free companions.** A **whole `F`-cycle** is legal iff
> every hub of that cycle deviates, and then costs **0**. A single
> **`M`-branch** is legal iff it is dart-free (equivalently: both its ends
> deviate), and then costs **0**.
>
> **(v) (GR-45)'s T1 is the `|F| = 1` case**: at a dart-free `γ ∈ M` the
> price is 0; at a dart-free `γ ∈ F` it is
> `#(non-deviating ends of γ) − #(deviating ends of γ)`.

*Proof.* (i) By (GR-67)(i) the deviating indicator at `v` is
`D(v) = ζ(v, f_1) ⊕ ζ(v, f_2)`. Flipping `F` flips the darts of the
branches in `F`, so `D(v)` flips **iff exactly one of `f_1(v), f_2(v)`
lies in `F`**, i.e. iff `v ∈ W(F)`. A flip at `v ∉ S` raises the count by
1; at `v ∈ S` it lowers it by 1. ∎

(ii) `W(F)` is by definition the odd-degree vertex set of `F ∩ E(F)`
inside the 2-factor `F`; a subgraph of a disjoint union of cycles is a
disjoint union of paths and cycles, and only the paths have endpoints. ∎

(iii) Legality: at an interior hub `|F ∩ star(v)| = 2`, so (GR-49)
requires `m(v) ∈ F` — and the two `A`-branches at an interior hub are
exactly `f_1(v), f_2(v)`, so `m(v) ∈ F` says precisely `m(v) ≠ M(v)`. At
an endpoint `|F ∩ star(v)| = 1`, so (GR-49) requires `m(v) ∉ F`. At every
other hub `F ∩ star(v) = ∅`. The price is (i) with
`W(A) = {e_1, e_2}` (interiors have *both* their `F`-branches in `A`).
The pattern claim is `pattern(γ) = z_γ` ((GR-49)(ii)). ∎

(iv)/(v) are (i)–(iii) at `t(F) = 0` and `|F| = 1`. ∎

**What this buys, exactly.** GPSA *Step G61* wrote (b′)'s proof-shaped
decomposition as *"at some parity-optimal map `|δ| ≤ 2`"* **plus** *"one
descent step available there"*, and priced the second half by
(GR-45)(iii) — *one T1 costs at most 2 deviations*, a statement about one
**2-hub** move. (GR-68) replaces that with a **theorem about the whole
legal family**, and the replacement is strictly stronger in three ways:

- it prices moves of **unbounded size**: the certified single-path family
  reaches length 9 in the sampled pool, and the price is 2 at every
  length (histogram `{-2: 217 008, 0: 445 544, 2: 217 008}` over 879 560
  legal path flips, path lengths 1–9);
- it identifies the **free** directions — matching branches and whole
  2-factor cycles cost nothing at all, so a repair may traverse them
  without paying;
- it makes "price ≤ 2" a **local combinatorial condition** (`t(F) = 1`,
  or more generally at most one surplus non-deviating endpoint) rather
  than a property of a named move.

So **the price half of (b′) is PROVEN**, at every shape, with no habitat
hypothesis, no cap and no restriction on the repair's length. What
remains of (b′) is *availability*, and nothing else (*Step G89*).

**A minimality corollary, recorded** *(a two-line consequence of the
landed (GR-44); not separately machine-asserted)*. At a **parity-optimal**
configuration no legal `F` has `Δdist < 0`, so by (v) **every dart-free
`F`-branch has at least one non-deviating end**; and the third-branch
vector `x = Σ_{v ∈ S} e_{x_v}` is an `M`-avoiding representative of `τ` of
weight `≤ |S| = w_M`, so by (GR-44) `wt(x) = |S|` and the `x_v` are
**pairwise distinct** — the (GR-44) minimum representative is literally
read off the changeover set.

---

### Step G88 — (GR-69): the imbalance ceiling `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)` — a theorem at `n_hub ≤ 6`, FALSE from `n_hub = 8`, and tight at every rung

The *first* half of GPSA's decomposition is an imbalance bound. It turns
out to be a **counting consequence of (GR-51)(i)(a)'s easy direction**,
with an exactly computable boundary.

> **(GR-69)** *(proven; asserted at all 408 688 parity-consistent
> configurations of the whole `Λ = ∅`, `D = 0` odd-carrying stratum
> (4780 shapes, both potentials) and at every configuration of 534
> seeded habitat shapes at `n_hub = 8, 10, 12`; the boundary witness
> grounded through `cm_solve` / `odd_balance` and, on its balanced
> configurations, through `cflank.admissible`; `--ceil`)*
>
> **(i) The slack identity.** With (GR-50)'s notation,
> > `u_v = d_v − [b_v = 0]`,  where `b_v := q_v − o_v`.
>
> **(ii) The global count.** For every pattern realized by an admissible
> `z`,
> > `#{v : b_v = 0} ≤ |H| = M − 2k`,  and its A-mirror
> > `#{v : o_v = 0} ≤ |H|`;
>
> more generally `#{v ∈ S′ : b_v = 0} ≤ e_H(S′) + ∂_H(S′)` for every hub
> set `S′`.
>
> **(iii) The ceiling.**
> > `|δ| ≤ 2·min(k, ⌊n_hub/4⌋)`.
>
> In particular `|δ| ≤ 2` **at every configuration of every habitat shape
> with `n_hub ≤ 6`**.

*Proof.* (i) If `b_v ≥ 1` then `o_v ≤ q_v − 1`, so
`2 − o_v ≥ 3 − q_v = d_v` and `u_v = min(d_v, 2 − o_v) = d_v`. If
`b_v = 0` then `o_v = q_v`, so `2 − o_v = d_v − 1 < d_v` and
`u_v = d_v − 1`. (At a monochromatic triple this reads `u_v = −1`, which
is (GR-50)'s empty-interval report.) ∎

(ii) By (GR-50) an admissible `z` with this pattern is a
degree-constrained orientation, so (GR-51)(i)(a) — whose **necessity** is
the one-line edge count, not the augmenting argument — holds. At
`S′ = V` it reads `e_H(V) ≤ Σ_v u_v`, i.e. with `e_H(V) = |H|` and
`Σ_v d_v = 2|H|`,
`|H| ≤ 2|H| − #{v : b_v = 0}`. The general form is the same substitution
with `Σ_{v ∈ S′} d_v = 2e_H(S′) + ∂_H(S′)`. The mirror is (GR-51)'s A↔B
symmetry. ∎

(iii) The `2b` ends of the B-coloured odd branches meet at most `2b`
hubs, so `#{v : b_v = 0} ≥ n − 2b`; with (ii) and `|H| = 3n/2 − 2k`,
`n − 2b ≤ 3n/2 − 2k`, i.e. `b ≥ k − n/4`; mirrored, `a ≥ k − n/4`. Since
`a + b = 2k`, `δ = 2(a − k)`, so `|δ| = 2|a − k| ≤ n/2`; and `|δ|` is
**even**, so `|δ| ≤ 2⌊n/4⌋`. With the trivial `|δ| ≤ 2k` this is (iii).
∎

**The exact boundary — and it is REALIZED.** At `n_hub ≤ 6` the ceiling
is 2 (`⌊6/4⌋ = 1`), so *Step G66*'s and this pass's `|δ| ≤ 2` on the
stratum are **arithmetic**. At `n_hub = 8` the ceiling is 4, and 4 is
attained at an explicit habitat shape:

> **V8** — the Wagner graph: the 8-cycle `0-1-…-7-0` plus the four long
> chords `(i, i+4)`, with the **four chords odd (`ℓ = 3`)** and one cycle
> edge at `ℓ = 4` (total excess `4·1 + 2 = 6`). `cflank.cubic_habitat`
> **accepts** it and so does the independent `gdev.habitat_by_lemma`
> ((GR-42)'s polynomial certificate); it is bridgeless. Its `|δ|`
> spectrum over **all 418** parity-consistent configurations is
> `{0: 230, 2: 184, 4: 4}`, and all 230 balanced ones are accepted by
> `cflank.admissible`, the (GR-37)(i) ground truth. The `ℓ5`-chord
> variant behaves identically.

*Why V8 works, in the (GR-50) coordinates:* the four odd branches form a
**perfect matching of the hubs**, so `q_v = 1` and hence `o_v = 1`,
`l_v = 0`, `u_v = 1`, `d_v = 2` at every hub when all four are coloured
A; orienting the even 8-cycle consistently gives `indeg(v) = 1`
everywhere. Both (GR-51) inequalities hold with `Σ_v u_v = |H| = 8`
**exactly saturated** — the ceiling's own equality case, made concrete.

**The ceiling is tight at every rung reached.** Maximum achieved `|δ|`
against the ceiling: `n = 2` → 0 (ceiling 0); `n = 4, 6` → 2 (ceiling 2);
`n = 8, 10` → 4 (ceiling 4); `n = 12` → 6 (ceiling 6, at `2k = 6`). And `|δ| = 4`
is not an isolated accident of V8: in `--ceil`'s seeded `n = 8` pool the
ceiling 4 is **attained** at both `2k = 4` and `2k = 6`, and at `n = 12`
the ceiling 6 is attained at `2k = 6`.

**What this CORRECTS — an evidence downgrade, not a claim refutation.**
GDESC *Step G66* measured min `|δ|` at parity-optimal maps as
`{0: 92, 2: 2}` over 94 shapes and recorded (b′)'s first decomposition
clause as *"measured TRUE at every censused shape"*; this pass extends
that to the whole stratum (`{0: 4641, 2: 139}`). **On the `n_hub ≤ 6`
stratum both figures are forced by (GR-69)(iii)** — no configuration
there can be more imbalanced than 2, optimal or not. So the stratum
evidence for that clause carries **no weight for `n_hub ≥ 8`**, where the
clause becomes a genuine statement about *optimality*. It survives every
test past the boundary — min `|δ|` at a shape-optimal map is `{0: 313, 2: 12}`
at `n = 8`, `{0: 141, 2: 8}` at `n = 10`, `{0: 61, 2: 1}` at `n = 12`
(*Step G90*) — but it is now supported by 536 exact shapes rather than by
a ceiling.

**One landed reading sharpened, not moved.** (GR-53)'s tight `2k = 4`
case (the odd-branch triangle of monochromatic-pair hubs, which admits no
zero-monochromatic-pair balanced split) is carried by **854** stratum
shapes; max `|δ|` there is still 2. So (GR-53)'s tightness is about the
**split**, not about the imbalance — the two bars are independent
(`--adv` (5)).

---

### Step G89 — (GR-70): (b′) reduced to ONE availability clause, verified EXHAUSTIVELY on the stratum — and the landed T1-only instance REFUTED from `n_hub = 8`

> **(GR-70)** *(the reduction proven; the stratum verification EXHAUSTIVE
> — 4780 odd-carrying habitat shapes, all 23 939 (shape, matching) pairs,
> full `3^n` censuses, every perfect matching, no deviation cap; the
> refutation by explicit witness; `--exh`, `--big`, `--adv` (6))*
>
> **(i) The reduction.** Fix `M`. By (GR-46)/(GR-49) one-move
> transitivity every parity-consistent map is one legal flip set away
> from every other, so
> > `d_adm(M) ≤ d_par(M) + 2` **iff** at some parity-optimal
> > configuration there is a legal `F` with `z + χ_F` balanced and
> > `Δdist(F) ≤ 2`.
>
> By (GR-68) `Δdist(F)` is a closed formula. **Call the right-hand side
> Clause A′.** Nothing but availability is left: the arithmetic is
> discharged.
>
> **(ii) The stratum: Clause A′ holds, in its T1 instance.** At **every
> one** of the 96 930 unbalanced parity-optimal configurations of the
> stratum some majority-side odd branch is **dart-free**, and its
> (GR-68) price is 0 or 2 — never more (worst per-pair minimum price:
> `{0: 11 183, 2: 4393}`). Consequently
> `d_adm(M) − d_par(M) ∈ {0, 2}` at all 23 939 pairs
> (`{0: 23 444, 2: 495}`, even as (GR-67) Cor. 1 requires), and the
> **shape-level** gaps are `{0: 4641, 1: 126, 2: 13}`: **(b′) holds
> exhaustively on the whole `Λ = ∅`, `D = 0` stratum, with the bound 2
> attained.**
>
> **(iii) The T1 instance is FALSE from `n_hub = 8`.** Among seeded
> habitat shapes swept exactly (full census, all matchings, no cap):
> **32 / 15 088** unbalanced parity-optimal configurations at `n = 8`,
> **120 / 16 502** at `n = 10` and **52 / 15 904** at `n = 12` have **no**
> dart-free majority-side odd branch. GPSA *Step G61*'s second clause
> — *"one descent step available there"*, instantiated as one T1 — is
> therefore **refuted with an exact boundary**: exhaustively true at
> `n_hub ≤ 6`, false from `n_hub = 8` with explicit witnesses.
>
> **(iv) The successor is named and priced at 0.** For the **48** stuck
> configurations of the independently-seeded `n = 8` audit pool
> (`--adv` (6)) an **exhaustive `2^M` search over legal flip sets** finds
> a balancing move at every one, and its cheapest price is **0**. Its
> structure is always **one `M`-branch plus one or two 2-factor
> branches** — `(#M, #F, #path components) = (1,1,1)` at 32 and
> `(1,2,2)` at 16 — a **mixed pair**. *(The `n = 10` and `n = 12` stuck
> configurations counted in (iii) are **not** covered by this exhaustive
> audit: `--adv` (6)'s own `n = 10` pool contains none, so the structural
> classification is an `n = 8` statement.)*

**The mechanism, and why the mixed pair is the *right* successor.** By
*Step G86*'s dictionary a majority-side odd branch `γ` is T1-blocked
exactly when some end `u` has `c(u) ≠ z_γ`, i.e. when `γ` **holds the
minority dart at `u`**. Adjoin any second branch at `u`: then
`|F ∩ star(u)| = 2`, and (GR-49)'s legality condition at `u` *demands*
`m(u) ∈ F` — which is precisely the blocking condition. **The obstruction
to T1 is the hypothesis that legalizes its two-branch extension.** This
is chain-following at the blocked end, and (GR-68) prices the result:
adjoining an `M`-branch is **free** (`W` unchanged), so a one-end-blocked
majority branch is repairable at the *same* price as the unblocked T1.

**Therefore the honest shape of (b′) after this pass** — the price side
proven, the availability side re-aimed:

> **(b′) ⟸ Clause A′**, and Clause A′ ⟸ *at every unbalanced
> parity-optimal configuration, some majority-side odd branch is
> **one-end**-blocked-or-free* (then the mixed pair repairs it at price
> ≤ 2 by (GR-68)) — with the **doubly-blocked** case, (GR-48)'s named
> kill, as the exact residual: there the chain must be followed at
> *both* ends, `F` acquires two path components, and (GR-68) prices it at
> `≤ 4` unless the extra endpoints land on deviating hubs.

The measured facts are consistent with this being the whole story: every
stuck configuration found is repaired at price **0**, i.e. the extra
endpoints *do* land on deviating hubs. Whether that is forced is the
residual (*Step G91*).

---

### Step G90 — (GR-71): beyond the stratum — 536 exact shapes at `n_hub = 8/10/12`, the named shapes, and cap-free per-matching certificates at `n = 30`

> **(GR-71)** *(measured; the `n = 8/10/12` legs EXACT per shape — full
> `3^n` census, ALL perfect matchings, no deviation cap — over a seeded
> habitat pool whose seed and try counts are printed; the `n = 30`
> certificates **cap-free**; `--big`)*

| leg | shapes | shape gaps | per-matching gaps | min `\|δ\|` at a shape-optimal map |
|---|---|---|---|---|
| stratum `n ≤ 6` (**exhaustive**) | 4780 | `{0: 4641, 1: 126, 2: 13}` | `{0: 23 444, 2: 495}` | `{0: 4641, 2: 139}` |
| `n_hub = 8` (seeded, exact) | 325 | `{0: 313, 1: 9, 2: 3}` | `{0: 1831, 2: 60}` | `{0: 313, 2: 12}` |
| `n_hub = 10` (seeded, exact) | 149 | `{0: 141, 1: 8}` | `{0: 1162, 2: 41}` | `{0: 141, 2: 8}` |
| `n_hub = 12` (seeded, exact) | 62 | `{0: 61, 1: 1}` | `{0: 657, 2: 10}` | `{0: 61, 2: 1}` |

**Named shapes, pinned** (exact, all matchings): W3M `(2, 2, 0)` at
opt-`|δ| = 0`; **W3 `(2, 3, 1)` at opt-`|δ| = 2`**, per-matching gaps
`[0, 2]` — reproducing GADM *Step G56*'s and GDESC *Step G66*'s landed
figures and now *explaining* the odd gap by (GR-67) Cor. 2; NKo2v
`(2, 2, 0)` at opt-`|δ| = 0`.

**Cap-free certificates at `n = 30`.** `d_par(M)` is computed **exactly**
by the landed `gadm.dp_pref` DP at a constructed matching, and a balanced
admissible configuration is **exhibited** at `d_par(M) + 0` — so the
per-matching gap is certified `= 0` with **no cap anywhere** (an exact
lower object and an explicit upper witness): NKo(6) `d_par(M) = 6`,
NKp(6) `d_par(M) = 6`, NK55(6) `d_par(M) = 8`. This is a genuine
strengthening of GPSA *Step G61*'s "gap upper bound 0 at this matching",
which quoted a `dp_walk` sample.

**Cap disclosed, and it is a real reach limit.** The necklace leg stops
at `m = 6` (`n = 30`) because `dp_pref`'s table is `2^dim` with
`dim = |E| − n + 1`: 16 at `n = 30`, **21** at `n = 40`, 26 at `n = 50`,
**31** at `n = 60`. **GBAL's `n = 40/50/60` reach does not transfer**:
(GR-54) needs only balance *existence*, which (GR-50) decides
polynomially, whereas any (b′) statement needs `d_par(M)`, and that is
the exponential object. Recorded so the next pass does not read GBAL's
reach as this pass's. An exhausted table is not `∞` and a `m = 6` leg is
not an `m = 12` leg.

**The `n = 30` level-split probe** (`--adv` (4); `dp_walk`, 200
walks/level, **a capped sample, not a census**). At level 0 — exactly
parity-optimality — NKp(6) and NKo(6) produce **0** unbalanced
configurations at all (so gap 0), and NK55(6) produces 224, **every one
of them with a free majority T1**. So no stuck optimum was found at
`n = 30`; max `|δ|` at level 0 is 2 in all three, and 4 appears only at
level `d_par + 4` at NKp(6).

---

### Step G91 — (GR-72): where this leaves (b′), the residual, and the hand-off

> **(GR-72)** *(the status statement; no new mathematics)* **(b′) stays
> OPEN as a theorem, and is NOT a HIT.** What moved:
>
> - its **price** half is **PROVEN** — (GR-68), in closed form, for the
>   whole legal move family, at every shape, with no cap and no length
>   restriction;
> - its **first** clause is **PROVEN at `n_hub ≤ 6`** and given an
>   **exact boundary** — (GR-69), false from `n_hub = 8` at an explicit
>   habitat witness — so the stratum evidence for it is re-read as
>   arithmetic and its live support is now 536 exact shapes past the
>   boundary;
> - its **second** clause, as landed (one T1), is **REFUTED from
>   `n_hub = 8`** with stuck witnesses, and replaced by a named,
>   (GR-68)-priced **mixed-pair** successor that repairs every witness
>   found at price 0;
> - a new structural theorem constrains any future violation:
>   **(GR-67) Cor. 1** — per-matching gaps are **even**, so a
>   per-matching counterexample must show a gap of **4**, never 3, and
>   an odd *shape-level* gap is a matching-parity artifact (Cor. 2);
> - (b′) itself now holds **exhaustively** on the whole `Λ = ∅`, `D = 0`
>   stratum (no subsample, no cap — a first for (b′)) and at 536 exact
>   larger shapes, with cap-free per-matching certificates at `n = 30`.

**The residual, named exactly.** *Clause A′*: **at every unbalanced
parity-optimal configuration there is a legal flip set `F` with
`z + χ_F` balanced and `|W(F) ∖ S| − |W(F) ∩ S| ≤ 2`.** Two sub-clauses,
in the order a successor should take them:

1. **The one-end-blocked case is nearly done** — *Step G89*'s mechanism
   plus (GR-68)(iv) prices the mixed pair at the unblocked T1's price,
   because an `M`-branch is free. What is left is the far-end side
   condition `m(w_β) ≠ β` for at least one of the two available `β`, and
   that is a short, bounded derivation. It covers every stuck witness this
   pass found (48/48 at `n = 8`, cheapest price 0).
2. **The doubly-blocked case is the real residual** — (GR-48)'s named
   kill, realized at `n = 30`. There the chain must be followed at both
   ends, `t(F) = 2`, and (GR-68) gives only `≤ 4` unless both extra
   endpoints are deviating hubs. **What would close it:** a proof that at
   a *parity-optimal* configuration the second chain's endpoint is forced
   onto `S`. (GR-68)'s own minimality corollary is the natural input —
   optimality already forbids `Δdist < 0`, hence constrains where
   dart-free `F`-branches can sit.
3. **A third route, untried and cheap to state:** minimizing `dist(·, M)`
   over admissible `z` at a *fixed* balanced pattern is, by (GR-50), a
   **minimum-cost degree-constrained orientation** — a min-cost flow, so
   polynomial. (b′) per-matching is then an exchange statement between
   two such flow problems (pattern-free vs pattern-fixed), and flow
   theory has exchange machinery this arc has not used.

**Hand-off — the route ledger** (statuses as this landing leaves them).
**Entry 5 — PROVEN, unchanged** ((GR-54); this pass consumes it and
touches nothing). **Entry 1 — unchanged; (a′) not attempted** (YLOC's
target this wave); it remains entry 1's primary with no bar. **(b′) —
OPEN, supported, price half PROVEN, availability half re-shaped with an
exact boundary; its named residual is Clause A′ sub-clause 2.** (c)
AA-glue realizability and (d′) untouched.

**One (Y)-relevant by-product, reported and NOT developed** (the spec's
bar). (GR-67) Cor. 1 applies to `d_fg(M)` as well: **`d_fg(M) − d_adm(M)`
is EVEN at every matching.** (GR-59) refuted the per-matching (a′)
variant with 1278 of 24 638 (shape, matching) pairs carrying
`d_adm(M) < d_fg(M) < ∞`; the parity law predicts every one of those gaps
is `≥ 2`, and that a per-matching (a′) gap of exactly 1 **cannot exist**.
This pass is rank-free and does not compute the check itself, but the
prediction is already **corroborated**: GLAW's own landed (GR-59)
measurement of that gap distribution is `{2: 1251, 4: 27}` — every one
of the 1278 gaps **is already even**, exactly what the parity law
predicts, and no gap of exactly 1 appears among them. Recorded here as
a landed corroboration against existing figures, not a fresh
computation, and offered to YLOC / the successor as a constraint any
(Y) argument may use for free.

**Riders, verbatim.** Everything is at **`Λ = ∅`**, **`D = 0`**, and
**modulo (GR-4′)** where a closure chain is concerned; the **`Λ ≠ ∅`
closed-form analogue** and the **`D > 0` lift** stay **unswept**. **None
of this closes (GR-15)**, and no `g`-flank is exhibited: the pass is
rank-free, computes no rank anywhere, and makes no claim about class
uniformity. The **shift-metric layer is UNBOUNDED** ((GR-43),
`d_par = d_adm = d_fg = m` exactly at the necklaces) — so (b′) is stated
throughout as a bound on the **difference**, never on `d_adm`, and every
necklace figure above carries that qualifier.

---

### Verification (Steps G86–G91)

`notes/scripts/w4/balb.py` (**new with this pass**; imports — all
read-only — `cflank` (`cubic_habitat`), `gadm` (`complete_matching`,
`cycle_masks`, `dp_pref`, `dp_walk`, `nko_specs`), `gbal` (`dart_col`,
`flip_legal`, `map_to_z`, `odd_idx`, `named_cases`, `pool_cases`,
`rand_cubic`, `verify_balanced`, `z_admissible`, `z_to_map`), `gdesc`
(`imb_of`, `majority_of`), `gdev` (`habitat_by_lemma`, `nk_specs`),
`gorient` (`cm_solve`, `m_of_matching`, `odd_balance`,
`perfect_matchings`, `prep_shape`), `gpsa` (`branches_at`,
`is_bridgeless`, `nk55_specs`, `nkp_specs`, `parity_census`,
`pattern_of`, `t1_move`)). **Rank-free**: `gexist.fully_good_rank` is
never imported or called and no `d_fg` claim is made anywhere. Local
devices, none shadowing a §1 primitive (checked against the README index
and the *Divergences* table): `matching_branches`/`dev_set`/
`dist_anchored`/`even_outside` ((GR-67)(i)/(ii)), `two_factor`/
`cycle_paths` (the 2-factor and its paths), `w_set`/`price_pred`
((GR-68)), `path_legal_pred`/`path_cost_pred` ((GR-68)(iii)), `ceiling`/
`bfree_counts` ((GR-69)), `layers_exact` (exact per-matching layers off a
full census), `clause_scan` (the Clause O / Clause A′ audit),
`rand_habitat` (a seeded **graph** sampler on top of `gbal.rand_cubic`
behind `cflank.cubic_habitat` — no placement is drawn, so §(K-clos)
(AC-9) does not apply), `v8_specs`, `stratum_cases`, `hist`. Exact
integers over GF(2) throughout; no floating point; rngs seeded per mode
with the seed printed; no `set` printed. **No pool is new**: the
`Λ = ∅`, `D = 0` stratum is `gcap.pool_specs` behind
`cflank.cubic_habitat` via `gbal.pool_cases`, swept **EXHAUSTIVELY**;
the named shapes and the necklaces are GUNIF's / GPSA's / GADM's
constructions reused read-only; the only new *shape* is **V8**, and it is
gated by two independent habitat oracles.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --anchor    # ~25 s  (GR-67) over the WHOLE pool: 2188534 identity + 1094267 parity-law asserts
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --flip      # ~35 s  (GR-68): 4419364 path pairs + 508816 general legal-flip-set prices
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --ceil      # ~28 s  (GR-69) at 408688 stratum configs + V8 + the n = 8/10/12 tightness ladder
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --exh       # ~10 s  (GR-70) exhaustive (b') on the stratum: 23939 pairs, 96930 optimal configs
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --big       # ~23 s  (GR-71) n = 8/10/12 exact + named + the cap-free n = 30 certificates
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --adv       # ~14 s  F13 controls + the level-split n = 30 hunt + the stuck-at-optimum audit
PYTHONHASHSEED=0 python3 notes/scripts/w4/balb.py --validate  # ~135 s all six in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-67)(i) the anchored identity | `--anchor` | `dist_anchored` asserted **equal** to the canonical Hamming count `#{v : m(v) ≠ M(v)}` at all 2 188 534 (shape, matching, map, potential) quadruples of the WHOLE pool |
| (GR-67)(ii) the parity law | `--anchor` | `dist % 2 == #{even ∉ M} % 2` asserted at all 1 094 267 (matching, map) pairs; the doctored constant must fail (`--adv` (1)) |
| (GR-67) Cor. 1 (gaps even) | `--exh`, `--big` | `assert g % 2 == 0` on the **measured** per-matching gap at all 23 939 stratum pairs and at every `n = 8/10/12` pair |
| (GR-67)(iii) changeover parity | `--anchor` | asserted per `F`-cycle at every one of the 2 188 534 quadruples |
| (GR-67) Cor. 3 (cycle floor) | `--anchor` | `assert d_par(M) >= #odd-even-count cycles` at 24 661/24 661 pairs; tightness counted separately (11 266) |
| (GR-68)(i) the general price | `--flip` | over **all `2^M`** subsets at every configuration of a sampled sub-pool and every matching, legality filtered by `gbal.flip_legal` and `|W∖S| − |W∩S|` asserted **equal** to the recomputed anchored count: 508 816 legal pairs |
| (GR-68)(ii) `\|Δdist\| ≤ 2 t(F)` | `--flip` | `assert got <= len(W)` at every one of those pairs; path-component histogram `{0: 37 088, 1: 280 384, 2: 184 400, 3: 6944}` reported so the `t = 0` (free) class is exhibited, not assumed |
| (GR-68)(iii) path legality criterion | `--flip`, `--adv` (2) | the predicted criterion asserted **equal** to `gbal.flip_legal` at all 4 419 364 (admissible `z`, F-path) pairs; (2) re-checks the 55 186 rejections as a guard (never over-accepts) |
| (GR-68)(iii) price independent of length | `--flip` | cost histogram `{-2, 0, 2}` over 879 560 legal path flips **bucketed by length 1–9**; the assert is `-2 <= cost <= 2` per flip |
| (GR-68)(iii) pattern flips on `A ∩ O` | `--flip` | `assert (p1 ^ p2) == χ_{A ∩ O}` at every legal path flip |
| (GR-68)(iv) the two free companions | `--flip` | whole-cycle: criterion asserted equal to `flip_legal` at 122 170 (configuration, cycle) pairs, price asserted 0 at the 11 636 legal ones; `M`-branch: criterion and price 0 asserted at 167 692 instances |
| (GR-68)(v) T1 price formula | `--exh` | the closed formula asserted **equal** to the recomputed anchored difference at every free T1 examined in the stratum audit |
| (GR-69)(i)/(ii) the `S = V` count | `--ceil` | `#{no B-odd dart} ≤ \|H\|` and its mirror asserted at all 408 688 stratum configurations |
| (GR-69)(iii) the ceiling | `--ceil` | `assert \|δ\| <= 2 min(k, ⌊n/4⌋)` at all 408 688 stratum configurations **and** at every configuration of 534 seeded `n = 8/10/12` habitat shapes |
| (GR-69) tightness at each rung | `--ceil` | achieved max `\|δ\|` reported per `(n, 2k, ceiling)`: 0/2/2/4/4/6 at `n = 2/4/6/8/10/12` |
| (GR-69) the `n = 8` boundary witness | `--ceil` | V8 gated by `cflank.cubic_habitat` **and** `gdev.habitat_by_lemma` and `is_bridgeless`; `assert spec[4] > 0`; the witness re-checked through `cm_solve` + `odd_balance` (= 4), and all 230 balanced configurations of the same shape through **`cflank.admissible`** |
| (GR-70)(i) the reduction | — | **proof**, not driver-testable: it is (GR-46)/(GR-49) transitivity plus (GR-68); the modes test its two inputs |
| (GR-70)(ii) (b′) on the stratum | `--exh` | `assert g <= 2` per matching **and** per shape at all 4780 shapes / 23 939 pairs; `assert g is not None` guards against a vacuous pass |
| (GR-70)(ii) Clause A′, T1 instance | `--exh` | `assert free == unb` at every (shape, matching): 96 930/96 930 unbalanced parity-optimal configurations carry a dart-free majority-side odd branch |
| (GR-70)(iii) the T1 refutation | `--big`, `--adv` (6) | the same audit run past the boundary **reports** `unb − free`: 32 / 120 / 52 at `n = 8/10/12`; (6) re-derives it at an independent seed (48 at `n = 8`) |
| (GR-70)(iv) the mixed-pair successor | `--adv` (6) | for each stuck configuration an **exhaustive `2^M`** search over legal flip sets, minimizing `(price, \|F\|)`; cheapest price `{0: 48}` and structure `{(1,1,1): 32, (1,2,2): 16}` |
| (GR-71) the `n = 8/10/12` legs are EXACT | `--big` | full `3^n` census per shape, ALL perfect matchings, no deviation cap — the sweep is over a *seeded* shape pool (seed printed), which is the only sampling |
| (GR-71) the `n = 30` certificates are cap-free | `--big` | `d_par(M)` from `gadm.dp_pref` (exact DP) plus an **exhibited** balanced witness re-checked through `cm_solve`/`odd_balance`; `assert dim <= 18` makes the reach limit an explicit guard, not a silent cap |
| the `n = 30` level-0 probe is a SAMPLE | `--adv` (4) | 200 `dp_walk` walks per level, disclosed in the printed line as "a CAPPED sample, not a census" |
| the (b′) assert is live | `--adv` (3) | a synthetic gap-4 verdict fires it |
| (GR-53) tightness ≠ imbalance | `--adv` (5) | the 854 carrying stratum shapes counted and their max `\|δ\|` reported (2) |
| (a′) / `d_fg` / the (Y) by-product | — | **not attempted**; no mode computes a rank. The `d_fg(M)` parity prediction is **corroborated** against GLAW's landed (GR-59) figures (`{2: 1251, 4: 27}`, all even), not independently computed here |
| (GR-15) / class uniformity | — | untouched; not driver-testable and not claimed |

**Determinism.** `--validate` was run at `PYTHONHASHSEED` 0 and 999
(both exit 0, ≈135 s): the outputs are **byte-identical except for the
`[Ns]` wall-clock annotations**, which are inherently non-deterministic.

**Scratch probes (README's standing rule).** Ten exploratory probes were
written during the derivation (the stratum layer sweep, the anchored
identity, the parity law, the `|δ|` spectrum, the V8 construction, the
`n = 8/10` sweeps, the stuck-configuration family classification). **None
is retained** — each became a mode of the committed driver, and every
figure quoted above is produced by `balb.py`. No figure in this section
comes from a probe.

---

### Confidence verdict (Steps G86–G91)

| | claim | standing |
|---|---|---|
| **(GR-67)(i)** | the anchored identity; `dist` is a function of `z\|_F` | **proven** (three-line proof; asserted against the canonical count at 2 188 534 quadruples over the whole pool) |
| **(GR-67)(ii)** | the parity law | **proven** (one-line branch sum; asserted at 1 094 267 pairs, with a doctored-constant control) |
| **(GR-67)** Cor. 1 | every per-matching layer gap is EVEN; per-matching (b′) is the dichotomy 0 / ≥ 2 | **proven** (immediate from (ii); the measured gaps are even at all 23 939 + 3650 pairs) |
| **(GR-67)** Cor. 2/3 | the odd shape-level gap explained; the cycle floor | **proven** (Cor. 3 asserted at 24 661 pairs) |
| **(GR-68)** | **the price of any legal move in closed form**; `M`-branches and whole `F`-cycles free; single-path repairs cost ≤ 2 at any length | **proven** (two-line proof; the formula asserted at 508 816 legal flip sets — every `2^M` subset filtered — and the path specialization at 4 419 364 pairs) |
| **(GR-69)** | the imbalance ceiling `\|δ\| ≤ 2 min(k, ⌊n/4⌋)`; `\|δ\| ≤ 2` at `n_hub ≤ 6` | **proven** (from (GR-51)(i)(a)'s *necessity* only; asserted at 408 688 stratum + 534 larger-shape configurations) |
| **(GR-69)** boundary | `\|δ\| ≤ 2` is **FALSE from `n_hub = 8`** | **refuted with an exact boundary** (V8, double-gated habitat, `\|δ\| = 4` at 4 of 418 configurations) |
| **(GR-70)(i)** | (b′) per-matching ⟺ Clause A′ | **proven-informally** (composition of (GR-46)/(GR-49) transitivity with (GR-68); not driver-testable) |
| **(GR-70)(ii)** | (b′) on the whole stratum, and Clause A′ in its T1 instance | **verified EXHAUSTIVELY** — 4780 shapes, 23 939 matchings, 96 930 optimal configurations, no subsample and no cap (a first for (b′)) |
| **(GR-70)(iii)** | the landed **T1-only** availability clause | **REFUTED from `n_hub = 8`** (32 / 120 / 52 stuck optima at `n = 8/10/12`, two independent seeds at `n = 8`) |
| **(GR-70)(iv)** | the mixed-pair successor, priced 0 at every witness | **measured** (exhaustive `2^M` per witness; the *mechanism* is proven, the *universality* is not) |
| **(GR-71)** | (b′) past the stratum; the cap-free `n = 30` certificates | **measured** (exact per shape; the shape pool is seeded, the necklace reach limit disclosed as a guard) |
| **(b′)** | `d_adm − d_par ≤ 2` | **OPEN — NOT a HIT.** Price half proven; first clause proven at `n ≤ 6` with an exact boundary; second clause refuted as landed and replaced by a named successor. Residual: **Clause A′, doubly-blocked case** |
| GDESC *Step G66* | min `\|δ\|` at parity-optimal maps `{0: 92, 2: 2}` | **figures stand; their *reading* is downgraded** — on the stratum they are forced by (GR-69), so they are not evidence for `n ≥ 8` |
| GPSA *Step G61* | the (b′) decomposition | **both clauses re-scoped**: clause 1 proven-then-bounded, clause 2 refuted-with-successor. No landed *figure* moves |
| (GR-44)–(GR-54) | the parity formula, the move calculus, the balance theorem | **untouched and consumed**; (GR-45)(iii)'s T1 pricing is **subsumed** by (GR-68), not contradicted |
| **(a′)** | the `d_fg = d_adm` law | **OPEN — not attempted** (YLOC's target); one by-product reported, not developed |
| **(GR-15)** | | **OPEN — unchanged in both directions.** No flank; no rank computed anywhere |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as TCOL's through GBAL's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos)
(AC-9)), and the only sampler draws a **graph**, not a placement.

### What would change this (Steps G86–G91)

*(i)* **A per-matching gap of 4** refutes (b′). By (GR-67) Cor. 1 that is
now the *only* per-matching shape a counterexample can take — no gap 3 —
which is a real narrowing of the search: hunt at `n_hub ≥ 8`, `2k ∈ {4, 6}`,
at shapes where the ceiling permits `|δ| = 4` and where the optimal
stratum is small. *(ii)* **A doubly-blocked parity-optimal configuration
whose every balancing legal move has price ≥ 4** refutes Clause A′ and,
with (GR-70)(i), refutes per-matching (b′). This is the single sharpest
target the pass leaves, and it is exactly (GR-48)'s kill family evaluated
*at optimality* — the `n = 30` level-0 probe found none, but it is a
capped sample. *(iii)* **A proof that the second chain's endpoint is
forced onto `S` at a parity-optimal configuration** closes Clause A′ and
with it (b′); (GR-68)'s minimality corollary is the natural input.
*(iv)* **A min-cost-flow exchange argument** between the pattern-free and
pattern-fixed orientation problems ((GR-50)) would prove (b′) without any
availability clause at all — untried, and the pass's own recommendation.
*(v)* **The `Λ ≠ ∅` or `D > 0` analogue.** (GR-67) uses cubicity twice
(the two non-`M` branches per hub, and `M` being a *perfect* matching)
and (GR-69) uses it in `d_v = 3 − q_v` and `Σ d_v = 2|H|`; a `D > 0` lift
must redo all four, and a shape with more than 6 odd branches falls
outside (GR-53)'s exhaustion, on which (GR-54) — and hence the
non-vacuity of every gap statement here — depends. **Both strata stay
unswept by standing rider.** *(vi)* **A `d_fg` claim**: none is made, so
nothing here touches (a′), (GR-15) or the `g`-flank question in either
direction.


---

### Steps G92–G97 (2026-08-19, direction AGLU) — ledger attack (c), AA-glue realizability, is SETTLED NEGATIVE at `n_hub = 8` **as a non-vacuous theorem, not the dispatch's predicted binding-laminarity theorem**: **(GR-73)** shows `slack = 0` ⟺ no X-hub, pinning the crossing interface to a rigid `{2,3}`-degree subgraph with two disjoint `≥ 2`-member attachment families, and extends the J-charge from chunks to arbitrary branch sets; **(GR-74)** proves the AA-glue configuration at `n_hub = 8` has exactly **one** combinatorial template — `T` covers all 8 hubs at 10 branches (`n_2 = n_3 = 4`), `R` and `R′` are single branches, `S ∪ S′ = E(G°)` — certified EXHAUSTIVELY at all 44 premise-satisfying pairs of all 20 classes, and explains the `n_hub ≤ 6` vacuity combinatorially, before any colouring is chosen; **(GR-75)** proves the AA-glue configuration and its whole kill residual are **NOT realizable** at `n_hub = 8` — independently certified by an EXHAUSTIVE, uncapped scan of the complete stratum (39 689 shapes, 9 617 854 admissible colourings, 0 instances) that also reproduces (GR-38)'s own `n_hub ≤ 6` headline exactly — so the (GR-38) intersection kill is a **THEOREM** at `n_hub = 8`, **non-vacuously**, and the **maximal** binding family of each block is laminar; **(GR-76)** derives a general-`n` charge `|W| ≥ |F₂| + q_T` that alone forces `|X| ≥ 2` and hence **`n_hub ≥ 10`** — so the AA-glue configuration is impossible at **every** `n_hub ≤ 8`, an `n`-free proof that does not need the pinning — and narrows `n_hub = 10` to exactly **three** counting-satisfiable templates; **(GR-77) REFUTES the dispatch's predicted consequence, plainly**: outright binding laminarity is **FALSE** at `n_hub = 8` (**3 774** crossing same-block binding pairs, measured EXHAUSTIVELY over the complete stratum, against **0** at `n_hub ≤ 6`) — what (GR-75) buys is only the **uncrossing** of the **maximal** binding family, not laminarity of the family itself; **(GR-78)** delivers the (GR-15) counting-side target EXHAUSTIVELY over the whole `n_hub = 8` stratum with no cap (39 689/39 689 shapes carry a fully-good colouring, 86.9% of 9 833 022 colourings, every shape ≥ 10) — no g-flank, E1's own control firing on nothing. **(GR-15) stays OPEN, unchanged in both directions; no gap-map status move on `hK` itself; class uniformity untouched.**

**Notation** (on top of *Steps G43–G47*'s (GR-38), the slack identity and attachment lemma). Write `T := S ∩ S′`, `R := S ∖ S′`, `R′ := S′ ∖ S` for a crossing pair of chunks `S, S′`. (GR-36)(i)'s charge form is used throughout:

> `defect_A(S) = w45(S) + #{A-majority odd branches of S} + #{non-AA interiors of S}`.

---

### Step G92 — (GR-73): the slack-0 degree lemma — at `slack = 0` the intersection is itself a `{2,3}`-degree subgraph

> **(GR-73)** *(proven; asserted at every crossing chunk pair of every
> hub-multigraph class at `n_hub = 4, 6, 8` — 92 / 2 675 / 82 201 pairs,
> `--pin`)* Let `S, S′` be crossing chunks.
>
> **(i)** `slack(S, S′) = 0` **iff** the pair has no X-hub. *(Immediate from
> (GR-38)(i): `slack ≥ #X-hubs`, because at an X-hub the two pairs share a
> dart and cannot both be AA — three A-darts would be a monochromatic hub.)*
>
> **(ii)** At `slack = 0`, **every** hub touched by `T` has `deg_T ∈ {2, 3}`.
>
> **(iii)** Consequently, at `slack = 0`, every attachment hub of a component
> of `R′` is an **interior of `S`**, a **corner of `S′`**, and has
> `deg_T = 2` with `T`-pair `=` its `S`-pair; dually for `R`. The two
> attachment families are **disjoint** (`S`-degree 2 versus 3), and by the
> attachment lemma (GR-38)(ii) each has **≥ 2** members per component.

*Proof.* (ii): `deg_T(v) = 0` for a hub in both `S` and `S′` would need
`deg_S(v) + deg_{S′}(v) ≥ 4` darts at a cubic hub. `deg_T(v) = 1` puts one
dart in `T`; since `deg_S(v) ∈ {2, 3}` and `deg_{S′}(v) ∈ {2, 3}` and
`R ∩ R′ = ∅`, `deg_S(v) = 3` would force `deg_{S′}(v) = 1`, impossible for a
chunk — so `deg_S(v) = deg_{S′}(v) = 2` with one dart each in `R` and `R′`,
i.e. **different pairs**: an X-hub, excluded. (iii): (GR-38)(ii) puts every
attachment at an interior of `S` via its free dart; if that hub had
`deg_{S′} = 2` it would be an X-hub, so `deg_{S′} = 3` and both `S`-darts lie
in `S′`, i.e. in `T`. ∎

**Why it is the load-bearing first step.** (GR-38)(ii) classifies attachment
hubs into two types and (GR-38)(iii) then has to reason about both. (GR-73)
says the **`slack = 0` branch of the dichotomy kills the X type outright**, so
the residual case has a *rigid* interface: `T` is a `{2,3}`-degree subgraph,
`R` and `R′` hang off `T`-interiors' free darts only, and `S`, `S′` each carry
**≥ 2 corners**. Everything in *Step G93* is arithmetic on that interface.
The measured X-hub histograms show how thin the branch is: of 82 201 crossing
chunk pairs at `n_hub = 8`, **9 263** have no X-hub (11 %), and **0** of the
82 201 has a `deg_T = 1` hub at `slack = 0` — the lemma, asserted rather than
assumed.

**The J-charge on an arbitrary branch set (used constantly below), also part
of (GR-73).** (GR-36)(iii) is stated for chunks; its bound holds verbatim on
**any** branch set `P` of a cubic host:

> `defect_X(P) ≥ w45(P) + Σ_{J-components} ⌈m_i/2⌉ =: jbound(P)`, `X ∈ {A, B}`.

*Proof.* `J(P)` (vertices = degree-2-in-`P` hubs, edges = the `P`-branches
joining two of them) has max degree ≤ 2 as in (GR-36)(iii). A `J`-cycle forces
that cycle to be a whole **component** of `P` — for a chunk this forced
`k = 1`, but componentwise the same run count applies: on a cycle of `j`
hubs, `a` of them AA in `b` maximal runs, the AA-AA adjacencies (`≥ a − b`,
each an A-majority odd branch by (GR-36)(ii)) and the non-AA hubs
(`≥ b`, one gap per run) sum to `≥ j − b ≥ ⌈j/2⌉ = ⌈m/2⌉`. Paths are
(GR-36)(iii) unchanged. ∎ *(Asserted equal to `gorient.jdata`'s `bound` at
229 411 chunk sets, and `jbound(T) ≤ min(defect_A(T), defect_B(T))` at 48 675
crossing-pair instances, `--val`.)*

---

### Step G93 — (GR-74): the `n_hub = 8` pinning — the AA-glue configuration has exactly one combinatorial template

> **(GR-74)** *(proven; the conclusion asserted EXHAUSTIVELY at all 44
> slack-0 J-free-intersection crossing pairs of all 20 `n_hub = 8`
> hub-multigraph classes, and the premise's emptiness at `n_hub ≤ 6`
> likewise, `--pin`)* Let `S, S′` be crossing chunks of an `n_hub = 8`
> habitat shape with `slack = 0` and `defect_A(T) = 0` at an admissible
> colouring. Write `n_2, n_3` for the numbers of `T`-hubs of `T`-degree 2, 3.
> Then
>
> **(i)** the `T`-interiors are pairwise **non-adjacent in `T`**;
> **(ii)** `n_2 ≥ 4`; **(iii)** `n_2 = n_3 = 4`, so `T` covers **all 8 hubs**
> and has exactly **10 branches**; **(iv)** `R` and `R′` are **single
> branches**, each joining one of the two `T`-interior pairs, and
> **`S ∪ S′ = E(G°)`**.

*Proof.* (i): `defect_A(T) = 0` makes every `T`-interior AA, so a `T`-branch
joining two of them has an A-dart at both ends, hence is odd and A-majority
((GR-36)(ii)) and charges `defect_A(T) ≥ 1`. (ii): (GR-73)(iii) — `≥ 2`
`R′`-attachment hubs and `≥ 2` `R`-attachment hubs, all of `T`-degree 2, the
two families disjoint. (iii): by (i) all `2n_2` `T`-darts at interiors land at
`T`-corners, which absorb at most `3n_3` of them, so `2n_2 ≤ 3n_3`; and
`2n_2 + 3n_3 = 2|T|` forces `n_3` **even**. With `n_2 ≥ 4` that gives
`n_3 ≥ 4`, and `n_2 + n_3 ≤ 8` closes it at `(4, 4)`, `|T| = (8 + 12)/2 = 10`.
(iv): every hub is now in `T`; a `T`-corner has no free dart, so every branch
off `T` joins two `T`-interiors' free darts. There are exactly 4 such darts,
`M(8) = 12 = 10 + 2`, and the two remaining branches are one `R` and one `R′`
by (GR-73)(iii). ∎

**The machine half, and why it is not decoration.** "Exactly one template" is
an *exhaustiveness* claim, which F11 treats as its own class. `--pin`
enumerates **every** chunk of **every** one of the 20 `n_hub = 8`
hub-multigraph iso classes (the class list itself cross-certified against
`gridcol.multigraphs` at `n = 2, 4, 6`: 1 / 2 / 6) and **every** crossing
pair, then asserts the four clauses at every pair passing the *length-free*
surrogate of the premise (`#X-hub = 0` and `Σ⌈m_i/2⌉ = 0` on `J(T)`, both
implied by `slack = 0 ∧ defect(T) = 0` via the J-charge). Result: **44** such
pairs, **all 44** with profile `(|T-hubs|, n_2, n_3, |T|, |R|, |R′|,
union = E(G°)) = (8, 4, 4, 10, 1, 1, True)` and nothing else.

**A by-product worth recording: the `n ≤ 6` vacuity has a purely
combinatorial explanation.** At `n_hub = 4` and `n_hub = 6` the same
enumeration finds **7** and **285** slack-0 crossing pairs respectively, and
**0** of them has a J-free intersection. So at `n_hub ≤ 6` the
AA-glue configuration is impossible **before any colouring is chosen**, by
(GR-74)(i)+(iii)'s counting alone (`n_2 ≥ 4` with `n_3 ≥ 4` needs 8 hubs).
(GR-38)(iii)'s exhaustive `0 / 53 740` is thereby *explained*, not merely
reproduced: the reason binding is laminar at `n ≤ 6` is that the stratum is
too small to host the interface, and the smallest stratum that can host it is
exactly `n_hub = 8`.

---

### Step G94 — (GR-75): the kill at `n_hub = 8` — the AA-glue configuration is NOT realizable, and the intersection kill is a theorem there

> **(GR-75)** *(proven; and independently certified by an EXHAUSTIVE scan of
> the complete `n_hub = 8` stratum — 39 689 shapes, 9 617 854 admissible
> colourings, 1 424 realized crossing same-block binding candidate pairs, 0
> AA-glue, 0 residual, 0 kill failures, `--kill8`)*
>
> **(i) The theorem.** At `n_hub = 8` there is **no** admissible colouring of
> any habitat shape carrying a crossing pair of same-block binding chunks with
> `slack = 0` and `defect(T) = 0`.
>
> **(ii) The residual is empty, not just its named case.** The same holds for
> the whole kill residual `slack + defect(T) ≤ 1`.
>
> **(iii) Hence the (GR-38) kill is a THEOREM at `n_hub = 8`:** every crossing
> pair of same-block binding chunks has `slack + defect(T) ≥ 2` and therefore
> a **proper** binding union `S ∪ S′`. Consequently the **maximal** binding
> chunks of each block are pairwise **non-crossing**.

*Proof of (i).* Take the (GR-74) template. `defect_A(T) = 0` forces
`w45(T) = 0` (all `T`-branches `ℓ ∈ {2, 3}`), no A-majority odd branch in `T`
(so the `ℓ = 3` ones are B-majority), and all four `T`-interiors AA. At an AA
interior the two `T`-darts are A, so the third dart is B (mono-hub ban) and is
the hub's **minority** dart. `R` joins two `T`-interiors through exactly those
two darts, so `R` has **B at both ends**; end darts of a branch agree iff its
length is odd, so `R` is **odd and B-majority**, and likewise `R′`. Now
`E(G°)` has no interiors, so

  `defect_A(E(G°)) = w45(E(G°)) + #{A-majority odd branches}
                   = ([ℓ_R = 5] + [ℓ_{R′} = 5]) + 0 ≤ 2`,

while (GR-32)(iii) makes `defect_A(E(G°)) = 3` **identically** at every
balanced colouring. Contradiction. ∎

*Proof of (iii).* If `slack + defect(T) ≥ 2` then by (GR-38)(i)
`defect(S ∪ S′) = defect(S) + defect(S′) − defect(T) − slack ≤ 2 + 2 − 2 = 2`,
and `S ∪ S′` is a chunk ((GR-35)(ii)); it is **proper** because `E(G°)` has
defect 3. If instead `slack + defect(T) ≤ 1` we are in the residual, which
(ii) empties. For the maximality statement: two maximal binding chunks that
crossed would have a binding union strictly containing each. ∎

*Proof of (ii) — the completeness argument, stated because this is where a
"capped search" would hide.* A residual instance is a crossing pair, both
chunks binding in one block, with `slack + defect(T) ≤ 1`. Three **necessary**
conditions cut the search, each an inequality proven above or landed:

- **(F-a)** the pair crosses and both chunks are binding in the same block —
  the definition;
- **(F-b)** binding ⟹ `w45(S) + Σ⌈m_i/2⌉ ≤ 2` on `J(S)` (the J-charge, valid
  in **both** blocks), so a chunk failing it is **never** binding at **any**
  colouring;
- **(F-c)** `slack ≥ #X-hubs` ((GR-38)(i)) and `defect(T) ≥ jbound(T)`, so
  `#X-hubs + w45(T) + Σ⌈m_i/2⌉_{J(T)} ≤ 1`.

`--kill8` applies the length-free part of (F-b)/(F-c) per hub-multigraph class
— leaving **932** candidate crossing pairs over the 11 habitat-carrying
classes out of 82 201 — then the length-dependent part per shape, then visits
**every** admissible colouring of **every** shape that still keeps a
candidate (**39 097** of 39 689; the other **592** are *proven* residual-free,
not skipped), computing exact defects for `S`, `S′`, `T` and `S ∪ S′`. So the
`0` is a **complete** answer, and the only "cap" in the pass is the
pinned `n_hub = 8` itself. ∎

**The scan is non-vacuous, and the numbers say how sharply.** Of the 932
candidate pairs, **1 424 (shape, colouring, block) instances are realized with
both chunks binding** — so the detector fires, repeatedly, and lands on
exactly the configuration the residual asks about. Their measured
`(slack, defect(T))` distribution is **`{(0, 2): 912, (1, 1): 512}`** — every
single one at **`slack + defect(T) = 2` exactly**, i.e. at the kill's
threshold, never below. And `1 424 / 1 424` have a **binding union**. The
picture is that the habitat is *tight against* the kill at `n_hub = 8` and
never crosses it.

**Three falsification controls, because "0 instances" is worthless without a
detector that fires** (`--adv`):

1. **`K4`** (`n_hub = 4`): 14 chunks, 60 crossing pairs, **3** with no X-hub —
   the slack-0 detector fires at the smallest possible shape. Its first
   witness is the classical one: `S` and `S′` are the two thetas of `K4`
   sharing the 4-circuit `T`, and `jfree(T) = 2` because **every** hub of a
   4-circuit is an interior — the J-charge is precisely what stops this
   slack-0 pair from being an AA-glue.
2. **`n_hub = 8`, all 20 classes**: **9 263** slack-0 crossing pairs, **44**
   of them J-free. Both detectors fire at `n_hub = 8`, so the `0` in
   `--kill8` is a **colouring** fact, not an empty search.
3. **(GR-30)'s `W3M`** — the landed **minimal** `n_hub = 8` witness, reused as
   the dispatch directed: habitat-gated by `cflank.cubic_habitat`, colouring
   accepted by `cflank.admissible`, and this driver's own devices find **3**
   binding (chunk, block) instances at it. The **binding** detector fires at
   `n_hub = 8` too.

---

### Step G95 — (GR-76): the W-charge — what an AA-glue witness costs at any `n_hub`, and the `n_hub ≥ 10` bound it forces

> **(GR-76)** *(proven; the six-row length/majority case table asserted by
> enumeration (`--val` item 8), and the three dart-count identities of (ii)
> asserted at EVERY slack-0 crossing chunk pair at `n_hub = 4, 6, 8` —
> 7 / 285 / 9 263 pairs, `--pin`)* In **any** AA-glue configuration (any
> `n_hub`), partition the branches **off** `T` by how many of their end darts
> are free darts of `T`-interiors: `F₂` (two), `F₁` (one), `W` (none) — these
> are all the cases, since by (GR-73)(ii) a `T`-hub has `deg_T ∈ {2, 3}` and
> a `T`-corner has no free dart, so an off-`T` branch's remaining ends lie at
> hubs **off `T`** (write `X` for that hub set). Let
> `q_T = #{ℓ = 3 branches of T}`. Then
>
> **(i) The charge.** **`|W| ≥ |F₂| + q_T`.**
>
> **(ii) Three dart-count identities.**
> `n_2 = |F₁| + 2|F₂|`,  `3|X| = |F₁| + 2|W|`,  `|T| + |F₁| + |F₂| + |W| = M`.
>
> **(iii) Hence `|X| ≥ 2`, and `n_hub ≥ 10`.** A `W` branch has both ends in
> `X` at **distinct** hubs (no loops in habitat), so `|X| ≤ 1 ⟹ W = ∅ ⟹`
> (by (i)) `|F₂| = q_T = 0 ⟹` (by (ii)) `n_2 = |F₁| = 3|X| ≤ 3`, contradicting
> `n_2 ≥ 4` ((GR-74)(ii)). With `n_2 ≥ 4`, `2n_2 ≤ 3n_3` and `n_3` even
> ((GR-74)(iii)'s `n`-free part, so `n_3 ≥ 4`),
> `n_hub = n_2 + n_3 + |X| ≥ 4 + 4 + 2 = 10`. **The AA-glue configuration is
> therefore impossible at every `n_hub ≤ 8`.**
>
> **(iv) The `n_hub = 10` template list.** At `n_hub = 10`, (iii) forces
> `(n_2, n_3, |X|) = (4, 4, 2)` and `|T| = 10`; then (ii) gives
> `|W| = |F₂| + 1` and `|F₁| = 4 − 2|F₂|`, so
> `(|F₁|, |F₂|, |W|) ∈ {(4,0,1), (2,1,2), (0,2,3)}` and (i) gives `q_T ≤ 1`
> (so `exc(T) ≤ 1` and the five off-`T` branches carry `Σe = 6 − q_T ≥ 5`
> against `Σc = 3`).

*Proof.* Put `c(β) = [ℓ_β ≥ 4] + [ℓ_β odd and A-majority] = A(β) − 1` and
`e(β) = ℓ_β − 2`. Since `E(G°)` has no interiors, (GR-32)(iii) reads
`Σ_β c(β) = 3`; and `defect_A(T) = 0` gives `c ≡ 0` on `T`, so
`Σ_{β ∉ T} c(β) = 3`. The excess law (GR-21) gives
`Σ_{β ∉ T} e(β) = 6 − q_T`. The six cases are

| `ℓ` | odd majority | `c` | `e` | `e − c` |
|---|---|---|---|---|
| 2 | — | 0 | 0 | 0 |
| 3 | B | 0 | 1 | 1 |
| 3 | A | 1 | 1 | 0 |
| 4 | — | 1 | 2 | 1 |
| 5 | B | 1 | 3 | 2 |
| 5 | A | 2 | 3 | 1 |

Every `T`-interior's free dart carries **B** (*Step G94*'s proof). So an `F₂`
branch has B at both ends, hence is odd B-majority: rows 2 and 5, where
`e − c = c + 1`. An `F₁` branch has B at one end, so it is not an
A-majority odd branch: rows 1, 2, 4, 5, where `e − c ≥ c`. A `W` branch is
unconstrained: all six rows satisfy `e − c ≥ c − 1`. Summing,
`3 − q_T = Σ_{β∉T}(e − c) ≥ 3 + |F₂| − |W|`. ∎

**Two independent proofs of the `n_hub = 8` case, and that is deliberate.**
*Step G94* argues from the (GR-74) pinning plus the balance identity;
(GR-76)(iii) argues from the charge plus the dart counts and never mentions
`n_hub = 8` — it lands the stronger *"impossible at every `n_hub ≤ 8`"*, which
also re-explains (GR-38)(iii)'s `n ≤ 6` vacuity as one more instance of the
same bound. The two are recorded separately because they fail differently at
`n_hub ≥ 10`: the pinning's last step (`n_2 + n_3 ≤ 8`) is what breaks, while
the charge survives verbatim and merely stops being tight.

**Where it stops, precisely.** At `n_hub = 10` the arithmetic of (iv) is
*satisfiable*: e.g. `(|F₁|, |F₂|, |W|) = (4, 0, 1)` with `q_T = 1`, the `W`
branch an `ℓ = 3` A-majority (`c = 1`, `e − c = 0`), two `F₁` branches at
`ℓ = 4` (`c = 1`, `e − c = 1`) and two at `ℓ = 2` gives `Σc = 3`,
`Σ(e − c) = 2 = 3 − q_T`, `Σe = 5 = 6 − q_T` — every counting constraint of
(GR-76) met. So the charge alone does **not** close `n_hub = 10`; what is not
yet imposed there is the alternation consistency at the `X` hubs (each needs a
non-monochromatic 2-1 dart pattern), the mono-hub ban, and the (GR-25) cut
criterion. **The general question is OPEN**, and it is now a *three-template*
question at `n_hub = 10`, cheap for a successor to settle either way — see
*Step G97* hand-off item 1.

> **SETTLED by direction GTMPL (*Steps G98–G103*), and this bound is
> SUPERSEDED — not refuted.** (GR-76)(iii)'s `n_hub ≥ 10` stands as proven,
> from an independent argument; **(GR-82)** derives the strictly stronger
> `n_hub ≥ 4(n_2 + q_T) ≥ 16` from two further charges, so the three templates
> above are **NOT realizable** and this section's "cheap for a successor to
> settle either way" was right. (GR-76)(i) turns out to be the `≥ 0` instance
> of an **exact** count, `#{B-darts at X} = (3|X| − n_2 − 2q_T)/2`
> ((GR-81)(iii)) — which is why the dart pattern at the `X` hubs, named in this
> section's own *What would change this* as the unexploited candidate, was the
> ingredient that closed it.

---

### Step G96 — (GR-77): binding is NOT laminar at `n_hub = 8` — the census, and the corrected reading of (GR-38)(iii)

> **(GR-77)** *(measured, EXHAUSTIVE over the complete `n_hub = 8` habitat
> stratum, no cap; three graph slices of `--lam8` covering all 11
> habitat-carrying classes)* Over all **39 689** `n_hub = 8` habitat shapes
> and all **9 833 022** admissible colourings, the binding-capable chunk
> family carries **2 120 444** binding (chunk, block) instances, and the
> same-block binding pairs sharing a hub split as
>
> > **nested 457 244, CROSSING 3 774.**
>
> So **outright binding laminarity is FALSE at `n_hub = 8`**: (GR-38)(iii)'s
> `0 / 53 740` is an `n_hub ≤ 6` phenomenon, explained by (GR-74)'s counting
> and **not** a general theorem. What survives is (GR-75)(iii): all 3 774
> crossing pairs have a proper binding union, so the **maximal** binding
> family is laminar per block.

**How the two counts fit together.** Of the 3 774 crossing same-block binding
pairs, **1 424** lie in the `--kill8` candidate family and are measured to have
`slack + defect(T) = 2` exactly; the remaining **2 350** fail (F-c), i.e. have
`#X-hubs + jbound(T) ≥ 2`, hence `slack + defect(T) ≥ 2` **by proof** with no
computation. So the sentence *"every crossing same-block binding pair at
`n_hub = 8` has `slack + defect(T) ≥ 2`"* is established for the whole 3 774:
part by exhaustive measurement, part by the charge bound. **What is not
measured** is the `(slack, defect(T))` distribution over those 2 350 — the
laminarity census mode does not compute slack — and no claim is made about it
beyond the `≥ 2` bound.

**Why this correction matters to the arc, not just to this pass.**
(GR-35)(ii)'s *"What (ii) is for"* paragraph reads the uncrossing as
manufacturing (GR-24)'s privacy hypothesis *"on any stratum where defect-≤ 1
sets are excluded"*, and (GR-38)(iii) delivered that stratum at `n ≤ 6` by
**emptiness of the crossing phenomenon itself**. From `n_hub = 8` on, the
crossing phenomenon is **real and common** (3 774 instances), and the
uncrossing organization survives only through the **kill**, i.e. through the
residual being empty. A successor that wants laminar targets at `n_hub ≥ 10`
therefore needs (GR-76)-style work, not a repeat of the `n ≤ 6`
emptiness observation. This is the one place where a landed reading needed
sharpening, and it is sharpened here without contradicting any landed figure.

---

### Step G97 — (GR-78): the E1 control — the target holds EXHAUSTIVELY over the whole `n_hub = 8` stratum, at abundance — and the hand-off

> **(GR-78)** *(measured, EXHAUSTIVE over the complete `n_hub = 8` habitat
> stratum, no cap, `--lam8`)* **Every one of the 39 689 `n_hub = 8` habitat
> shapes carries an admissible colouring with no binding chunk in either
> block** — i.e. `a = 0 ∧ max_P g(P) ≤ 0` in both blocks, the target's own
> statement by (GR-27) block additivity and (GR-28)(ii). The abundance:
> **8 543 304 of 9 833 022** admissible colourings are fully good (**86.9 %**),
> and **every** shape has **≥ 10** of them (per-shape histogram capped at 10:
> `{≥10: 39 689}`). **No g-flank exists at `n_hub = 8`.**

**Scope, stated because it is easy to over-read.** This is the
**counting-side** target (`max_P g(P) ≤ 0` via (GR-28)(i)'s formula, valid at
`Λ = ∅` with no length-1 branch), computed exactly over the *binding-capable*
family — an **exact** family by (F-b), so nothing is missed. It is **not**
rank-certified: **no `dim Z` was computed in this pass**, and per-shape
(GR-15) follows only **modulo (GR-4′)**, exactly as everywhere else in the
arc. What it does deliver is the first **exhaustive** stratum-wide
verification of the target beyond `n_hub ≤ 6`, on a stratum **8.07×** larger
in shapes and **34.6×** larger in admissible colourings than the `n ≤ 6` one
(39 689 vs 4 920; 9 833 022 vs 284 512).

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, and **modulo (GR-4′)**
wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None of
this closes (GR-15)**: no rank was computed anywhere in this pass, and it is
not an `hK`-status move. Every obstruction figure carries its **family
qualifier** — (GR-36)'s **binding-capable** family strictly contains the
capacity-tight one, and (GR-40)'s 815 → 573 is a **prune**, not a zero.

**Hand-off — the five things a successor should take, in order.**

1. **`n_hub = 10` AA-glue realizability**, and it is now a **three-template**
   question, not a search: by (GR-76)(iv) the only possible profiles are
   `(|F₁|, |F₂|, |W|) ∈ {(4,0,1), (2,1,2), (0,2,3)}` with
   `(n_2, n_3, |X|) = (4,4,2)`, `|T| = 10`, `q_T ≤ 1`. The counting is
   satisfiable, so what must be added is the colouring side — the 2-1 dart
   pattern at each of the two `X` hubs, the mono-hub ban, and the (GR-25) cut
   criterion. `aglu.py` is `n`-generic apart from the pool: replacing
   `cubic_iso_classes(8)` by `(10)` and `excess_profiles(12,6)` by `(15,6)`
   runs the same three modes there. **Estimated cost is the one thing to check
   first** — the `n_hub = 10` labelled enumeration is ~50× the `n_hub = 8` one,
   so the canonicalizer, not the scan, is the bottleneck. A `--pin`-style
   colouring-free pass restricted to the three templates avoids the pool
   entirely and is the cheap route.
2. **The `(slack, defect(T)) = (0,2) / (1,1)` tightness** (*Step G94*). Every
   realized candidate pair at `n_hub = 8` sits at the threshold, **never
   above** — `slack + defect(T) ≥ 3` was not observed once in 1 424 instances.
   If that is a theorem, the kill has an exact form (`= 2`, not `≥ 2`) on the
   candidate family, and the union's defect is then *pinned*, not bounded.
   Cheap to test at `n_hub = 10` on one graph class.
3. **(GR-78) at `n_hub = 10`.** The `--lam8` machinery is `n`-generic; the
   only obstruction is pool size (the `n_hub = 10` stratum needs a complete
   iso-class list at 10 hubs and `excess_profiles(15, 6)`). A partial run must
   disclose its slice, per the §(K-grid) cap-exhaustion gate.
4. **Rank-certifying a sample of (GR-78)'s fully-good colourings**, which this
   pass deliberately did not do (no rank anywhere). One `n_hub = 8` shape
   rank-certified in both blocks through both matrices would upgrade
   *per-shape* (GR-15) at `n_hub = 8` from counting to the arc's usual
   standard, exactly as (GR-31) did at the four (GR-30) witnesses.
5. **The `n_hub = 8` pool itself is now a reusable object** — 20 hub-multigraph
   iso classes, 11 carrying habitat lengths, 39 689 shapes, 9 833 022
   admissible colourings, all enumerable in ~200 s from
   `aglu.cubic_iso_classes(8)` + `cflank.cubic_habitat`. Several arc questions
   currently pinned at `n_hub ≤ 6` for pool reasons ((GR-39)'s hot-dart
   census, (GR-58)'s `d_fg = d_adm` exhaustion, (GR-44)'s per-matching
   figures) become answerable one stratum higher with it. **This is probably
   the most reusable thing the pass produced.**

---

### Verification (Steps G92–G97)

`notes/scripts/w4/aglu.py` (**new with this pass**; imports — all read-only —
`kbare_common` (`verts_of`), `closure` (`colourings`), `gridcol`
(`multigraphs`, `subdivide`), `cflank` (`admissible`, `cubic_habitat`,
`excess_profiles`, `hub_model`), `gcap` (`branch_stats`, `two_ec_subsets`),
`gexist` (`defect_direct`, `incidence`), `gorient` (`attachment_check`,
`jdata`, `pair_slack`), `gunif` (`WITNESSES`, `wit_colouring`)). **Rank-free**:
`gexist.fully_good_rank` is never imported or called and no `dim Z` claim is
made anywhere. Two local devices replace a canonical one for **performance
only** and are asserted equal to it in `--val`: the graph generator
`cubic_iso_classes` (canonicalized by a pruned minimum-adjacency-matrix search
refined by Weisfeiler–Leman, asserted to match `gridcol.multigraphs`'s class
count at `n = 2, 4, 6`: 1/2/6) and the (GR-76) case table; the rest —
`chunks_of`, `crossing_pairs`, `xhubs`, `jfree`, `slack_direct`, `set_defects`,
`admissible_bits` — are new, none shadowing a §1 primitive. Exact integers
throughout (`GF(2)` and small integer arithmetic; nothing here samples a
placement, so `repin.star_generic` gates nothing — §(K-clos) (AC-9)'s
discipline, as for `gorient.py` / `cflank.py`). Rngs seeded per mode (seed
printed); every printed collection is sorted. Wall-clock `[Ns]` annotations
are inherently non-deterministic; every other byte is seed-stable. Every
invocation below was re-run by the coordinator at landing, in the foreground
with an explicit timeout, and reproduced the quoted figures exactly.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pool             # 149 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --pin              # 120 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --kill8            # 233 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 0/3 # 184 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 1/3 # 200 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --lam8 --slice 2/3 # 279 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --adv              # 145 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/aglu.py --val              # 240 s (dispatch's own run)
```

**What each invocation produced (coordinator-reproduced figures).**
`--pool`: the `n_hub = 8` stratum — 20 hub-multigraph classes (matching
`gridcol.multigraphs` at `n = 2, 4, 6`: 1/2/6), **39 689** habitat shapes over
11 habitat-carrying classes. `--pin`: **92 / 2 675 / 82 201** crossing chunk
pairs at `n_hub = 4/6/8`; slack-0 pairs **7 / 285 / 9 263**; at `n_hub = 8`,
**44** J-free-intersection slack-0 pairs, all with profile
`(8, 4, 4, 10, 1, 1, True)` and nothing else; `|X| ≤ 1` pairs split
**5 327** (`|X| = 0`) / **1 942** (`|X| = 1`), every one asserted `W = ∅`.
`--kill8`: **39 689** shapes, **39 097** live after the length filter (the
other **592** proven residual-free, not skipped), **9 617 854** admissible
colourings visited, **1 424** realized crossing same-block binding candidate
pairs, slack histogram `{0: 912, 1: 512}`, `defect(T)` histogram
`{1: 512, 2: 912}` — **residual 0, AA-glue 0, kill failures 0**, union
binding 1 424/1 424. `--lam8` (three slices, exhaustive partition of the 11
habitat-carrying classes): shapes `7 044 + 9 709 + 22 936 = 39 689`;
colourings `1 687 924 + 2 361 578 + 5 783 520 = 9 833 022`; binding instances
`526 144 + 608 028 + 986 272 = 2 120 444`; nested `84 068 + 114 088 +
259 088 = 457 244`; **crossing `532 + 586 + 2 656 = 3 774`**; the E1 control
fires on **0** of 39 689 shapes (every shape carries a fully-good colouring);
fully-good colourings `1 384 952 + 1 996 304 + 5 162 048 = 8 543 304`
(**86.9 %**), every shape's per-shape count capped-histogrammed at `{≥10:
39 689}`. `--adv`: the K4 slack-0 pair with `jfree(T) = 2` (the detector
fires at `n_hub = 4`); 9 263 slack-0 / 44 J-free at `n_hub = 8` (both
detectors fire there); (GR-30)'s **W3M** carries 3 binding (chunk, block)
instances (the binding detector fires at `n_hub = 8`). `--val` (run by the
dispatch, not re-run at landing — see *Cap disclosure*): all eight device
cross-certifications, including item 7's reproduction of (GR-38)'s own
`n ≤ 6` headline **exactly**: 4 920 / 284 512 / 53 740 / **0** crossing.

**CAP DISCLOSURE — mandatory, per the §(K-grid) cap-exhaustion gate
(`731b3e33`) and LTWO's *"4 of 8 patterns"* precedent.**

- **No cap is taken inside any `n_hub = 8` claim.** The shape pool is the
  **complete** stratum (every iso class of connected loopless cubic multigraph
  on 8 hubs × every excess profile, gated by the landed (GR-25) criterion);
  every admissible colouring of every relevant shape is visited; the chunk
  enumeration is the full `two_ec_subsets(kmin=1)` family (asserted equal).
  The three filters that reduce the work are **inequalities proven above**
  ((F-a)/(F-b)/(F-c)), each asserted against the canonical evaluator, so a
  dropped instance is *proven* absent, never *budgeted* away. `--lam8`'s three
  slices are a **partition**, not a sample.
- **`n_hub ≥ 10` was NOT searched at all.** No cap was exhausted there because
  no search was run there. Nothing here says the AA-glue configuration does
  not exist at `n_hub ≥ 10`; it says the question is **open** and names the
  instrument.
- **The `--val` internal cross-checks are seeded subsamples** (0.6 % of
  `n ≤ 6` colourings, 2 % at `n = 8`, ≤ 25 crossing pairs per sampled
  colouring) — those are *device* checks, and their sampling is disclosed
  rather than carried into any headline figure. The **exhaustive** device
  checks are the chunk enumeration and admissibility set-equality (all 4 920
  `n ≤ 6` pool shapes) and the `n ≤ 6` census reproduction (item 7).
- **One approximation in `--pin`, disclosed:** the *premise* it filters on is
  the length-free surrogate (`#X-hub = 0` and `jfree(T) = 0`) of
  `slack = 0 ∧ defect(T) = 0`. The surrogate is **implied** by the premise
  (via the J-charge), so filtering on it is a **superset** — (GR-74) is
  therefore asserted on more pairs than it claims, never fewer.
- **`gunif.WITNESSES` reuse:** only (GR-30)'s W3M is used, and only as a
  control. **(GR-28)(iv)'s `g ≤ 1` cap was not re-opened**; **the
  (GR-39)/(GR-40) fully-hot census was not re-run**; **(d′) was not
  attempted.**
- **`--val` was not re-run at landing.** The coordinator ran it in the
  foreground before this landing (`PYTHONHASHSEED=0`, exit 0, 240 s), and item
  7's reproduction of (GR-38)'s exact `n ≤ 6` figures is what licenses this
  pass's new `n_hub = 8` numbers; `--pool`/`--pin`/`--kill8`/`--lam8`
  (all three slices)/`--adv` were all independently re-run at landing and
  reproduced every quoted figure above.

**The F11 table — which driver mode tests which sentence.** ("Exhaustive",
"the only" and "forced" are their own claim class and get their own modes.)

| sentence | mode | what is asserted |
|---|---|---|
| the `n_hub = 8` habitat stratum is **exactly** 39 689 shapes over 20 classes | `--pool` | the class count against `gridcol.multigraphs` at `n = 2, 4, 6` (1/2/6); the shape count as an `assert` on 39 689; per-class breakdown printed |
| (GR-73)(i) `slack = 0` ⟺ no X-hub | `--kill8`, `--val` | `slack == slack_direct(...)` at every realized pair (the identity **tested**, not used as a definition), plus `slack ≥ #X-hubs` and `(slack == 0) == (#X == 0)`; and `nd == #X-hubs` against `gorient.pair_slack` at 48 675 instances |
| (GR-73)(ii) at `slack = 0`, `deg_T ∈ {2,3}` — **exhaustiveness claim** | `--pin` | `all(d in (2,3))` at **every** slack-0 crossing pair of **every** class at `n_hub = 4, 6, 8`; the `deg_T = 1` counter printed (0 at all three) |
| (GR-73)(iii) / (GR-38)(ii) the attachment interface | `--pin` | `gorient.attachment_check` (the **landed** checker) re-run on a seeded subsample at all three `n`; 1 102 X-type + 852 (2,3)-type hubs at `n_hub = 8` — a stratum (GR-38) had never asserted on |
| (GR-74) **the only** template — "forced", so its own mode | `--pin` | the 7-tuple profile asserted equal to `(8,4,4,10,1,1,True)` at **all 44** premise-satisfying pairs, and the profile histogram printed so a second profile would show as a second row |
| (GR-75)(i) AA-glue **not realizable** at `n_hub = 8` | `--kill8` | `assert aa_glue == 0` after visiting every admissible colouring of every candidate-bearing shape; the count of *realized* candidate pairs (1 424) printed so the 0 cannot be vacuous |
| (GR-75)(ii) the **whole residual** is empty | `--kill8` | `assert resid == 0`, with the `(slack, defect(T))` histograms printed |
| (GR-75)(iii) the kill holds — union binding | `--kill8` | `assert kill_fail == 0` and the union-binding count 1 424; the non-candidate half is proof, not computation (*Step G94*) |
| the scan's **completeness** (F-b)/(F-c) | `--val` | `jfree + w45 == gorient.jdata['bound']` at 229 411 chunk sets; `jbound(T) ≤ min(defect_A(T), defect_B(T))` at 48 675 instances — the two inequalities the filters rest on |
| the detector **fires** (non-vacuity) | `--adv` | three controls, each an `assert` on a **positive** count: K4 slack-0 pairs ≥ 1; `n_hub = 8` slack-0 and J-free counts ≥ 1; binding instances at (GR-30)'s W3M ≥ 1 |
| (GR-76)(i) the six-row charge table | `--val` (8) | `e − c` enumerated over all six length/majority cases; the three row-class bounds (`≥ c+1` on F₂, `≥ c` on F₁, `≥ c−1` on W) asserted |
| (GR-76)(ii) the three dart-count identities | `--pin` | `n_2 = \|F₁\|+2\|F₂\|`, `3\|X\| = \|F₁\|+2\|W\|`, `\|T\|+\|F₁\|+\|F₂\|+\|W\| = M` asserted at **every** slack-0 crossing pair at `n_hub = 4, 6, 8` (7 / 285 / 9 263); the `(\|X\|, n_2, \|F₁\|, \|F₂\|, \|W\|)` profile histogram printed |
| (GR-76)(iii) `W = ∅` whenever `\|X\| ≤ 1` — the step the `n_hub ≥ 10` bound turns on | `--pin` | asserted at every slack-0 pair with `\|X\| ≤ 1` (5 327 at `\|X\| = 0` and 1 942 at `\|X\| = 1`, `n_hub = 8`); the rest of (iii) is arithmetic on (i)+(ii), which have their own rows |
| (GR-77) laminarity **fails** at `n_hub = 8` | `--lam8` | the crossing count (3 774) over the complete stratum, with the nested count alongside; the first crossing pair printed per slice |
| (GR-78) every shape is fully good — **exhaustiveness claim** | `--lam8` | `assert flank == 0` per slice, i.e. every shape has ≥ 1 colouring with **both** binding lists empty; the per-shape count histogram and the 86.9 % rate printed |
| the whole census **pipeline** is the landed one | `--val` (7) | (GR-38)'s `n ≤ 6` headline reproduced through this driver's own devices: **4 920 / 284 512 / 53 740 / 0** — an `assert` on the exact 4-tuple |
| admissibility device ≡ `cflank.admissible` | `--val` | **set** equality of bit vectors at **every one of the 4 920** `n ≤ 6` pool shapes (299 420 colourings) + 60 seeded `n = 8` shapes |
| defect device ≡ `gexist.defect_direct` | `--val` | both blocks at 123 369 (colouring, chunk) pairs; `set_defects` (the arbitrary-set evaluator used for `T` and `S ∪ S′`) asserted equal at the same instances |

---

### Confidence verdict (Steps G92–G97)

| | claim | standing |
|---|---|---|
| **(GR-73)** | the slack-0 degree lemma (`slack = 0` ⟺ no X-hub; then `deg_T ∈ {2,3}`; the attachment interface) and the J-charge extended from chunks to arbitrary branch sets | **proven** (three-line proofs on top of landed (GR-38)(i)/(ii), and the (GR-36)(iii) count made componentwise); machine-asserted at **every** crossing chunk pair at `n_hub = 4, 6, 8`, and equal to `gorient.jdata` at 229 411 chunk sets |
| **(GR-74)** | the `n_hub = 8` pinning, all four clauses — **exactly one template** | **proven**, and the conclusion **exhaustively certified**: all 44 premise-satisfying pairs of all 20 classes have the single template, nothing else does. The counting step is elementary; the exhaustiveness is machine, per F11's treatment of "the only" |
| **(GR-75)(i)–(ii)** | the AA-glue configuration and the whole kill residual are **NOT realizable** at `n_hub = 8` | **proven**, *and* independently **exhaustive with no cap** over the complete stratum — two independent arguments (the direct dart-pattern contradiction; (GR-76)) plus the scan |
| **(GR-75)(iii)** | the (GR-38) kill is a theorem at `n_hub = 8`; the **maximal** binding family is laminar | **proven** (submodularity + (ii) + (GR-32)(iii)); the non-residual half needs no computation |
| **(GR-76)(i)–(ii)** | the W-charge `\|W\| ≥ \|F₂\| + q_T` and the three dart-count identities | **proven** (a six-row case table plus two landed identities); the table asserted by enumeration, the identities asserted at **every** slack-0 crossing pair at `n_hub = 4, 6, 8`. **General-`n`**, not `n_hub = 8`-specific |
| **(GR-76)(iii)** | `\|X\| ≥ 2`, hence **`n_hub ≥ 10`** — impossible at **every `n_hub ≤ 8`** | **proven**, and the *stronger* form of (GR-75)(i): `n`-free, does not use the (GR-74) pinning, subsumes (GR-38)(iii)'s `n ≤ 6` vacuity. Its combinatorial skeleton is machine-asserted; the two inputs it borrows are (GR-74)(ii) and the `n`-free half of (GR-74)(iii) |
| **(GR-76)(iv)** | the `n_hub = 10` three-template list | **proven** (arithmetic on (ii)+(iii)); **not** machine-certified — no `n_hub = 10` enumeration was run, and the list is a *pinning*, not a search result |
| AA-glue realizability at `n_hub ≥ 10` | — | **OPEN.** Not attacked by search (none run there, none claimed); (GR-76)(iv) narrows it to three templates. The counting constraints are **satisfiable** there (a worked profile in *Step G95*), so closure needs the colouring side, not more counting |
| **(GR-77)** | binding is **NOT laminar** at `n_hub = 8` — 3 774 crossing same-block binding pairs | **measured, exhaustive over the complete stratum**, no cap. The **negative** statement is therefore **proven by witness**; the count is a measurement |
| **(GR-77)** | every one of the 3 774 has `slack + defect(T) ≥ 2` | **proven** — 1 424 by exhaustive measurement (all `= 2`), 2 350 by the (F-c) charge bound. The `(slack, defect(T))` *distribution* over the 2 350 is **not measured**, and nothing is claimed about it |
| **(GR-78)** | every `n_hub = 8` habitat shape carries a fully-good admissible colouring; 86.9 % rate; every shape `≥ 10` | **measured, exhaustive over the complete stratum**, no cap — **counting-side only**, *not* rank-certified. Per-shape (GR-15) at `n_hub = 8` follows **modulo (GR-4′)** |
| **(GR-15)** | | **OPEN**, unchanged in both directions; **no gap-map status move** |
| **(GR-38)(i)/(ii)/(iii)** | | **untouched as mathematics.** (i)/(ii) are re-certified at `n_hub = 8` (a stratum never asserted on before); (iii)'s `n ≤ 6` clause stands verbatim. Only the *reading* of what (iii) buys past `n ≤ 6` is corrected, by (GR-77) |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as TCOL's through GBAL's: exact GF(2) / integer combinatorics on constructed
hub multigraphs, never `PencilNondegFeasible G`; no rank is computed
anywhere; no σ-fixed witness is read as generic (§(K-clos) (AC-9)); the only
sampler draws a **graph**, not a placement.

### What would change this (Steps G92–G97)

- **(GR-75) overturned** would need an AA-glue instance at `n_hub = 8`, which
  by (GR-74) must sit on the single 10-branch template — and the scan visits
  every colouring of every shape carrying such a pair. So overturning it needs
  a **defect** in one of the three landed inputs the proof leans on:
  (GR-32)(iii)'s `defect_A(E(G°)) = 3`, (GR-36)(i)'s charge form, or
  (GR-38)(ii)'s attachment lemma. All three are re-asserted in `--val` /
  `--pin` against the landed evaluators, and the whole census pipeline
  reproduces (GR-38)'s own `n ≤ 6` figures **exactly** (4920 / 284 512 /
  53 740 / 0), which is the strongest single check available.
- **(GR-74) overturned** at `n_hub = 8` would need a slack-0 crossing pair
  with a J-free intersection off the template — `--pin` asserts against
  exactly that at all 82 201 crossing pairs. At `n_hub ≥ 10` the pinning is
  **expected** to fail (clause (iii)'s `n_2 + n_3 ≤ 8` step is the only place
  `n_hub = 8` enters), and that is not a refutation but the open case.
- **(GR-76) strengthened** by tightening the `W`-row bound. `e − c ≥ c − 1`
  is attained only at `ℓ = 3` A-majority (`c = 1`, `e − c = 0`) and `ℓ = 5`
  A-majority (`c = 2`, `e − c = 1`), both of which need **A at both ends** —
  so any constraint forcing a B-dart onto a `W` branch's end would raise the
  bound and, by (iv)'s arithmetic, plausibly close `n_hub = 10` outright. The
  obvious candidate is the dart pattern at the `X` hubs, which this pass did
  **not** exploit and does not claim.
- **(GR-77) sharpened** by measuring `(slack, defect(T))` over all 3 774
  crossing pairs rather than the 1 424 candidates. Cheap (add a slack
  computation to `--lam8`); it would test whether the observed threshold
  tightness `slack + defect(T) = 2` is a *law* or an artifact of the candidate
  family. **Do not read the 1 424 histogram as a distribution over the
  3 774** — it is conditioned on (F-c).
- **(GR-78) overturned** by a single `n_hub = 8` habitat shape whose every
  admissible colouring has a binding chunk. That is a **g-flank** and fires
  **E1**; `--lam8` asserts against it per shape and prints the witness. The
  claim is exhaustive at `n_hub = 8` and says **nothing** about `n_hub ≥ 10`
  — where no scan was run.
- **The one systematic risk this pass carries** is that its speed comes from
  local devices replacing canonical ones (the graph generator, the chunk
  enumerator, the admissibility test, the defect evaluator). Each is asserted
  equal to its canonical counterpart in `--val`; the admissibility device in
  particular is asserted **set-equal** to `cflank.admissible` at **every one
  of the 4 920** `n ≤ 6` pool shapes, reproducing **284 512** exactly. A drift
  in any of them would move `--kill8`'s and `--lam8`'s figures, so `--val` is
  the mode to re-run first if anything looks wrong.

---

### Steps G98–G103 (2026-08-19, direction GTMPL) — ledger attack (c) closes at an **EXACT BOUNDARY**, and the second half of the boundary is a **HIT**: **(GR-79)** reads the whole `slack = 0`, `defect_A(T) = 0` frame off `gexist.defect_direct` — every `T`-branch has `A(β) = 1`, so `ℓ ∈ {2,3}` with the `ℓ = 3` ones B-majority, every interior is AA, there is **no** interior-interior `T`-branch ((GR-74)(i) re-derived with no extra input), every interior-incident `T`-branch is `ℓ = 2` and delivers a **B** dart at its corner, and the corner ledger `2p = 3n_3 − 2n_2 − 2q_T` follows before any colouring is chosen; **(GR-80)** is the **CORNER CHARGE** `n_3 ≥ 2n_2 + 2q_T` — the mono-hub 2-1 pattern at a `T`-corner, whose only A-dart supply is the `p` A-ends of the `ℓ = 2` corner-corner branches — a factor-3 strengthening of (GR-74)(iii)'s `2n_2 ≤ 3n_3` that kills the `n_hub = 8` template a **third** independent way; **(GR-81)** is the **X CHARGE** `|X| ≥ n_2 + 2q_T`, from the universal dart identity `bend(β) = e(β) − 2c(β) + 1` (proved for every branch, asserted at **2 545 902** (colouring, branch) instances of the complete `n_hub ≤ 6` stratum) which pins `#(B-darts at X) = (3|X| − n_2 − 2q_T)/2` **exactly** — (GR-76)(i) is the `≥ 0` instance of that count and this is the per-hub instance; **(GR-82)** chains them into the `n`-free bound **`n_hub ≥ 4(n_2 + q_T) ≥ 16`**, so the AA-glue configuration is impossible at **every `n_hub ≤ 14`** — all three (GR-76)(iv) templates are **DEAD**, each killed independently by *either* charge alone and again by an X-hub dart enumeration run with both charges switched off; and **(GR-83)** shows the bound is **TIGHT** by an explicit **`n_hub = 16` WITNESS** — habitat-gated by the landed (GR-25) criterion, admissible by `cflank.admissible`, with two crossing same-block binding chunks at `slack = 0`, `defect_A(T) = 0` and a **proper non-binding union of defect 4**, so the **(GR-38) intersection kill FAILS at `n_hub = 16`**, rank-certified by `gridwit.subgraph_g` and an exact rational `dim Z = 3 > 0` at generic labels; **(GR-84)** measures what else breaks there — the **whole** kill residual is inhabited (not just its AA-glue case), and **(GR-75)(iii)'s laminarity corollary FAILS**: three crossing pairs of **maximal** binding chunks per block at the witness colouring — while the witness shape still carries a fully-good colouring, so **E1 does not fire**. **(GR-15) stays OPEN, unchanged in both directions; no gap-map status move on `hK` itself; class uniformity untouched.**

**Notation** (on top of *Steps G43–G47*'s (GR-38) and *Steps G92–G97*'s AA-glue frame, whose `T := S ∩ S′`, `R := S ∖ S′`, `R′ := S′ ∖ S`, `n_2`/`n_3` and `q_T` are used verbatim). Write `X` for the hub set **off** `T`, and add two counters for the `T`-frame's corner-corner branches: `p` for those of length 2 and `q_T` for those of length 3 (*Step G98* shows there are no others). For a branch `β` write `c(β) = A(β) − 1`, `e(β) = ℓ_β − 2`, and — new here —

> `bend(β) := #{end darts of β carrying B} ∈ {0, 1, 2}`.

Throughout, "AA" at a degree-2-in-`P` hub means both `P`-darts are A, exactly as `gexist.defect_direct` computes it, and "binding in A" is `defect_A ≤ 2` (`g = 3 − defect ≥ 1`).

---

### Step G98 — (GR-79): the B-flooded frame — what `defect_A(T) = 0` forces, read straight off the defect formula, before any length is chosen

> **(GR-79)** *(proven; the corner ledger asserted EXHAUSTIVELY at every
> slack-0 crossing chunk pair with a J-free intersection of every
> hub-multigraph class at `n_hub = 4, 6, 8` — 7 / 285 / 9 263 slack-0 pairs,
> 0 / 0 / 44 J-free, `--frame`)* Let `S, S′` be crossing chunks of a habitat
> shape with `slack = 0` and `defect_A(T) = 0` at an admissible colouring
> (the AA-glue configuration, any `n_hub`). Then
>
> **(i)** every `T`-branch has `A(β) = 1`, i.e. `ℓ ∈ {2, 3}` with the
> `ℓ = 3` ones **B-majority** (pattern B A B), and every `T`-interior is
> **AA** with its free dart carrying **B**;
>
> **(ii)** there is **no interior-interior `T`-branch** — which is
> (GR-74)(i), re-derived here with no input beyond (i);
>
> **(iii)** every interior-incident `T`-branch has `ℓ = 2` and delivers a
> **B** dart at its corner end. Hence the `q_T` branches of length 3 in `T`
> all join two corners, and with `p := #{ℓ = 2 corner-corner branches}`,
>
> > `|T| = 2n_2 + p + q_T`  and  `2|T| = 2n_2 + 3n_3`,  so
> > **`2p = 3n_3 − 2n_2 − 2q_T`**  (the **corner ledger**);
>
> **(iv)** the **A**-darts at corners are exactly the `p` A-ends of the
> `ℓ = 2` corner-corner branches, **one apiece** — so there are `p` of them,
> and the corners carry `2n_2 + p + 2q_T` B-darts.

*Proof.* (i): (GR-28)(i) is `defect_A(P) = Σ_{β∈P}(A(β) − 1) + #{non-AA degree-2-in-`P` hubs}`, and at `Λ = ∅` every branch has `ℓ ≥ 2`, hence at least one A-edge and one B-edge under alternation, so **every term is `≥ 0`**. `defect_A(T) = 0` therefore forces each term to vanish: `A(β) = 1` on every `T`-branch, and no non-AA interior. `A(β) = 1` allows only `ℓ = 2` (pattern A B or B A) and `ℓ = 3` with pattern B A B; `ℓ ≥ 4` has `A(β) ≥ 2`. At an AA interior the two `T`-darts are A, so the third dart is B by the mono-hub ban ((GR-33): every hub of an admissible colouring carries a 2-1 dart pattern). (ii): a `T`-branch joining two interiors has A at both ends; at `ℓ = 2` the two end darts differ, and at `ℓ = 3` they agree but then the branch is A-majority, i.e. `A(β) = 2`, excluded by (i). (iii): by (GR-73)(ii) every `T`-hub has `deg_T ∈ {2, 3}` and by (ii) an interior's `T`-branches all reach corners; such a branch has A at the interior end, so by (i) it is not the B A B pattern, hence `ℓ = 2` and its far dart is B. The two displayed identities are the branch count and the degree sum; subtracting gives the ledger. (iv): a corner has `deg_T = 3`, so **all three** of its darts are `T`-darts. Of the branch types available by (i)+(iii) — interior-corner (`ℓ = 2`, B at the corner), corner-corner `ℓ = 3` (B at both ends), corner-corner `ℓ = 2` (one A end, one B end) — only the last supplies an A-dart, and exactly one. ∎

**Why this is the load-bearing step, and why it was available all along.** (GR-74) extracted the `n_hub = 8` template from `defect_A(T) = 0` by counting *hubs*; (GR-76) extracted a charge from counting *branch excess*. Neither looked at what the same hypothesis does to the **corner darts**, and that is where the whole `T`-frame is pinned: `defect_A(T) = 0` floods the corners with B. The frame is then so rigid that the mono-hub ban — which the arc has used since (GR-33) and which costs nothing — becomes a hard inequality (*Step G99*). Everything in *Steps G99–G101* is bookkeeping on (GR-79).

**The machine half.** "Every slack-0 J-free pair satisfies the ledger" is an *exhaustiveness* claim, so it gets its own mode. `--frame` walks **every** crossing chunk pair of **every** hub-multigraph iso class at `n_hub = 4, 6, 8` (92 / 2 675 / 82 201 pairs — reproducing AGLU's `--pin` counts exactly), asserts (GR-73)(ii) at each of the 7 / 285 / 9 263 slack-0 pairs, and then asserts (ii)+(iii)'s branch classification and the ledger at each pair whose intersection is J-free. The premise's surrogate is AGLU's own — `#X-hubs = 0` and `jfree(T) = 0`, both *implied* by `slack = 0 ∧ defect_A(T) = 0` — so the ledger is asserted on a **superset** of the pairs it claims, never a subset. At `n_hub = 8` the 44 J-free pairs all carry `(n_2, n_3, |T|, #corner-corner) = (4, 4, 10, 2)` and nothing else, which is (GR-74)(iii) reproduced through a second driver.

---

### Step G99 — (GR-80): the corner charge `n_3 ≥ 2n_2 + 2q_T` — the mono-hub ban at a `T`-corner, and a third independent proof of the `n_hub = 8` kill

> **(GR-80)** *(proven; the kill of AGLU's 44-pair `n_hub = 8` template
> asserted at all 44, `--frame`)* In any AA-glue configuration,
>
> > **`p ≥ n_3`**,  equivalently  **`n_3 ≥ 2n_2 + 2q_T`**.

*Proof.* By (GR-33) every hub carries a 2-1 dart pattern, so every corner has **at least one A-dart** among its three `T`-darts. By (GR-79)(iv) the A-darts at corners are the `p` A-ends of the `ℓ = 2` corner-corner branches, one per branch, so `p ≥ n_3`. Substituting the corner ledger `2p = 3n_3 − 2n_2 − 2q_T` gives `3n_3 − 2n_2 − 2q_T ≥ 2n_3`. ∎

**How much stronger this is than what was available.** (GR-74)(iii)'s `n`-free half gives `2n_2 ≤ 3n_3`, i.e. `n_3 ≥ ⅔ n_2`; (GR-80) gives `n_3 ≥ 2n_2` — a **factor 3**. The reason is that (GR-74)(iii) counts only *how many* darts interiors send to corners, while (GR-80) also knows *what colour they are*: all B, by (GR-79)(iii), and each one crowds out the corner's A-quota.

**A third independent proof of (GR-75)(i), and the falsification control it doubles as.** At `n_hub = 8` the (GR-74) template has `n_2 = n_3 = 4` and `p + q_T = 2`, so `p ≤ 2 < 4 = n_3`: some corner receives three B-darts and is **monochromatic**. `--frame` asserts exactly that at all 44 premise-satisfying pairs. AGLU already had two proofs of (GR-75)(i) — the (GR-74)-pinning-plus-balance argument of *Step G94* and (GR-76)(iii)'s charge — and this is a third, from a third ingredient. That it reproduces a landed theorem is the control that the new charge is not an artifact: **a charge that did not kill `n_hub = 8` would be wrong, not new.**

---

### Step G100 — (GR-81): the X charge `|X| ≥ n_2 + 2q_T` — the universal dart identity, and the exact B-dart count at the hubs off `T`

> **(GR-81)** *(proven; the identity asserted at EVERY branch of EVERY
> admissible colouring of the complete `n_hub ≤ 6` stratum — 2 545 902
> (colouring, branch) instances over 284 512 colourings of 4920 shapes,
> `--charge` — and the B-dart counts asserted at the witness, `--wit`)*
>
> **(i) The universal dart identity.** For **every** branch of **every**
> admissible colouring,
>
> > **`bend(β) = e(β) − 2c(β) + 1`.**
>
> **(ii) Two global corollaries.** `#{B-darts} = #{A-darts} = M`, and
> exactly `n_hub / 2` hubs are A-majority.
>
> **(iii) The exact count off `T`.** In any AA-glue configuration,
>
> > **`#{B-darts at X hubs} = (3|X| − n_2 − 2q_T) / 2`**  exactly.
>
> **(iv) The charge.** Hence, by the mono-hub ban at each X hub,
>
> > **`|X| ≥ n_2 + 2q_T`.**

*Proof.* (i): if `ℓ` is even the two end darts differ, so `bend = 1`, and `A(β) = ℓ/2`, so `e − 2c + 1 = (ℓ − 2) − (ℓ − 2) + 1 = 1`. If `ℓ` is odd the end darts agree; when they are A, `A(β) = (ℓ+1)/2` and `bend = 0 = (ℓ − 2) − (ℓ − 1) + 1`; when they are B, `A(β) = (ℓ−1)/2` and `bend = 2 = (ℓ − 2) − (ℓ − 3) + 1`. (ii): sum (i) over all `M` branches — `Σe = 6` by the excess law (GR-21) at `D = 0` and `Σc = 3` by (GR-32)(iii) at balance, so `Σ bend = 6 − 6 + M = M`; then `#{A-darts} = 3n_hub − M = M` too, and since each hub contributes 2 or 1 A-darts, `#{A-darts} = n_hub + #{A-majority hubs}` forces `#{A-majority hubs} = M − n_hub = n_hub/2`. (iii): B-darts split over the three hub classes. Interiors: one each, their free darts, by (GR-79)(i) — `n_2`. Corners: `2n_2 + p + 2q_T` by (GR-79)(iv). So

  `#{B-darts at X} = M − n_2 − (2n_2 + p + 2q_T) = M − 3n_2 − p − 2q_T`,

and substituting `M = 3(n_2 + n_3 + |X|)/2` and `2p = 3n_3 − 2n_2 − 2q_T` gives `(3|X| − n_2 − 2q_T)/2`. (iv): by (GR-33) each X hub — all three of whose darts lie off `T` — has at least one B-dart, so the count in (iii) is `≥ |X|`, i.e. `3|X| − n_2 − 2q_T ≥ 2|X|`. ∎

**What this does to (GR-76)(i), stated precisely.** (GR-76)(i) reads `|W| ≥ |F₂| + q_T`. Its right-hand side is not an accident: with `n_2 = |F₁| + 2|F₂|` and `3|X| = |F₁| + 2|W|` ((GR-76)(ii)),

> `|W| − |F₂| − q_T = (3|X| − n_2 − 2q_T)/2 = #{B-darts at X hubs}`,

so **(GR-76)(i) is exactly the statement that this count is `≥ 0`** — the aggregate instance — while (GR-81)(iv) is the **per-hub** instance, `≥ 1` at each of the `|X|` hubs. The two are the same identity read against two different lower bounds, and the second is free: the mono-hub ban is already in `cflank.admissible`. AGLU's own *"What would change this"* named the missing ingredient correctly — *"the obvious candidate is the dart pattern at the `X` hubs, which this pass did not exploit"* — and this is that candidate, cashed.

**The machine half.** (i) and (ii) are asserted at **every** branch of **every** admissible colouring of the **complete** `n_hub ≤ 6` stratum (`--charge`): 4 920 shapes, 284 512 admissible colourings — AGLU's and (GR-38)'s own stratum figures, reproduced exactly through this driver's pool builder, which is the check that licenses the rest. The same mode asserts the 2-1 pattern at every hub of every one of those colourings (`{1, 2}` A-darts, never `{0, 3}`), `Σe = 6`, `Σc = 3`, `Σ bend = M`, and `#{A-majority hubs} = n_hub/2`. (iii) is asserted at the witness in `--wit` (`4 = (12 − 4 − 0)/2` at the X hubs, `16 = 2·4 + 8 + 0` at the corners, `8 = p` A-darts at the corners).

---

### Step G101 — (GR-82): the bound `n_hub ≥ 16` — the (GR-76)(iv) three-template question settled NEGATIVE, and `n_hub = 12, 14` with it

> **(GR-82)** *(proven; the three templates ENUMERATED empty down to
> per-X-hub dart colours and per-corner A-dart assignments, and the whole
> aggregate system searched exhaustively over `n_hub ≤ 40`, `--tpl` /
> `--min`)* In any AA-glue configuration,
>
> > **`n_hub = n_2 + n_3 + |X| ≥ n_2 + (2n_2 + 2q_T) + (n_2 + 2q_T)
> >  = 4(n_2 + q_T) ≥ 16`**,
>
> using `n_2 ≥ 4` ((GR-74)(ii), i.e. (GR-38)(ii) via (GR-73)(iii)). Hence
>
> **(i)** the AA-glue configuration is impossible at **every `n_hub ≤ 14`**;
> **(ii)** in particular all three (GR-76)(iv) templates —
> `(|F₁|, |F₂|, |W|) ∈ {(4,0,1), (2,1,2), (0,2,3)}` on
> `(n_2, n_3, |X|) = (4,4,2)` — are **NOT realizable**, and each is killed
> **independently** by (GR-80) alone and by (GR-81) alone;
> **(iii)** `n_hub = 12` and `n_hub = 14` are dead too, so the bound is not
> a `n_hub = 10` statement;
> **(iv)** at `n_hub = 16` the system forces `(n_2, n_3, |X|, q_T, p) =
> (4, 8, 4, 0, 8)` — all three charges tight — with
> `(|F₁|, |F₂|, |W|) ∈ {(0,2,6), (2,1,5), (4,0,4)}`.

*Proof.* The displayed chain is (GR-80) and (GR-81)(iv) substituted into `n_hub = n_2 + n_3 + |X|`; `n_2 ≥ 4` and `q_T ≥ 0` close it. (ii): at `(4,4,2)`, (GR-80) needs `n_3 ≥ 8` and (GR-81) needs `|X| ≥ 4`; both fail at every `q_T`. (iii): `n_2 ≥ 4` alone forces `n_3 ≥ 8` and `|X| ≥ 4`, so `n_hub ≥ 16`. (iv): equality throughout forces `n_2 = 4`, `q_T = 0`, `n_3 = 8`, `|X| = 4`, then `p = 8` from the ledger, and `(|F₁|, |F₂|, |W|)` from (GR-76)(ii). ∎

**Three independent kills of the dispatched question, because "the only" is its own claim class.** `--tpl` reports, per template and per `q_T ∈ {0,1,2}`: the corner charge's verdict, the X charge's verdict, the number of `(c, e)`-consistent off-`T` type multisets, and the number of survivors of a **raw enumeration with both charges switched off** — every branch's `(ℓ, majority)` type, every split of the `Σc = 3` / `Σe = 6 − q_T` budget across the three roles, every orientation of the even `W` branches, and every assignment of the `F₁` X-ends to the two X hubs, tested against the mono-hub ban at both. The result is `0` survivors at all nine (template, `q_T`) cells, with **6 / 2 / 0**, **11 / 3 / 0** and **3 / 1 / 0** type multisets examined respectively — so the zeros are **not vacuous**, and the `q_T = 2` column's zeros are the counting side's own kill, which is why (GR-76)(iv) says `q_T ≤ 1`.

**The bound is exhaustively searched, not just derived.** `--min` walks the whole aggregate system — `(n_2, n_3, |X|, q_T, p, |F₁|, |F₂|, |W|)` under the ledger, the (GR-76)(ii) dart identities, the branch total, and both charges in their *enumerated* per-hub forms — at every even `n_hub ≤ 40`, and reports the feasible list `[(16, 3), (18, 6), (20, 15), (22, 24), (24, 43), (26, 62), (28, 95), (30, 128), …]`. **The least feasible `n_hub` is 16**, and `--val` item 3 asserts that no enumerated frame anywhere in `n_hub ≤ 32` violates the closed-form charges — the derivation and the enumeration agree in the direction that matters.

**The falsification control the enumerator needs.** A search that returns `0` at `n_hub = 10, 12, 14` is worthless if it returns `0` everywhere. It does not: at `n_hub = 16` it returns **3** aggregate frames and **59** full solutions, at 18 six and 121, at 20 fifteen and 269. And the `n_hub = 16` frames are *exactly* the tight profile of (iv) — which is where *Step G102* goes looking.

**What (GR-82) is and is not.** It is a statement about **necessary** conditions: the aggregate system's *emptiness* below 16 is a genuine kill, but its *non-emptiness* at 16 proves nothing on its own — a solution of the counting system need not be a graph, a habitat shape, an admissible colouring, or a crossing pair of binding chunks. That gap is closed by exhibiting all four at once.

---

### Step G102 — (GR-83): the bound is TIGHT — an explicit `n_hub = 16` witness, and the (GR-38) kill FAILS there

> **(GR-83)** *(a WITNESS, constructed and verified through the canonical
> layer; rank-certified; `--wit` / `--e1`)* There is a habitat shape at
> `n_hub = 16` with an admissible colouring carrying a crossing pair of
> same-block binding chunks with `slack = 0` and `defect_A(T) = 0`. So
>
> **(i)** the AA-glue configuration **IS realizable**, at `n_hub = 16`;
> **(ii)** the **(GR-38) intersection kill FAILS there**: `S ∪ S′` is a
> **proper** chunk of `defect_A = 4`, hence **not binding**;
> **(iii)** (GR-82)'s bound is **EXACT** — a theorem at `n_hub ≤ 14`, false
> from `n_hub = 16`, with all three charges tight at the witness;
> **(iv)** the witness shape still carries a **fully-good** admissible
> colouring, so it is **not** a g-flank and **E1 does not fire**.

**The shape.** 16 hubs: eight **corners** `c_0 … c_7` forming an 8-cycle of `ℓ = 2` branches; four **interiors** `u_0 … u_3`, with `u_j` joined by `ℓ = 2` branches to two corners under the perfect assignment `u_0 ↦ \{c_0, c_2\}`, `u_1 ↦ \{c_1, c_3\}`, `u_2 ↦ \{c_4, c_6\}`, `u_3 ↦ \{c_5, c_7\}` (each corner hit exactly once, and each interior's two corners at cycle-distance 2, so the shortest circuit through an interior has `Σℓ = 8 ≥ 7`); four **X hubs** `x_0 … x_3` forming a 4-cycle of branches of lengths `(3, 5, 4, 2)` in cycle order; and four `ℓ = 2` branches `u_t – x_t`. That is `M = 24` branches, total excess `1 + 3 + 2 + 0 = 6` ✓, `|V| = 46` in the subdivision, `5|E| = 270 = 6(|V| − 1)` ✓. **`cflank.cubic_habitat(16, …) = True`** — the landed (GR-25) cut criterion, the same `D = 0` membership oracle AGLU's exhaustive `n_hub = 8` scan is gated by. Independently, `nogood_subdiv.deficiency = 0` (the polynomial Lee–Streinu pebble game), `hcard_ok = True`, and no two-hub triangle: three of the four conjuncts of the canonical certificate `gridcol.class_shape`, re-run directly. *(The fourth, `kslide.no_rigid_branch_union`, is a `2^M` scan with a matroid rank inside — out of reach at `M = 24`, which is exactly why (GR-25) is the arc's oracle past `n_hub = 6`.)*

**The colouring.** All 16 `T`-branches (the 8-cycle plus the eight interior-corner branches) are `ℓ = 2`; the interiors are AA, so their interior-corner branches carry A at the interior and **B** at the corner, and the 8-cycle is **consistently oriented** so that each corner receives exactly one A-dart and one B-dart from it — every corner is therefore `(A, B, B)`, B-majority. Each interior's free dart is its `u_t – x_t` branch, carrying **B** at `u_t` and A at `x_t`. The four `W` branches are `x_0x_1` at `ℓ = 3` **B-majority**, `x_1x_2` at `ℓ = 5` **A-majority**, `x_2x_3` at `ℓ = 4` with **B at `x_2`**, and `x_3x_0` at `ℓ = 2` with **B at `x_3`** — giving each X hub exactly one B-dart. **`cflank.admissible(…) = True`**, and every one of the 16 hubs carries a 2-1 pattern.

**The pair.** `T` = the 16 `T`-branches; `R = \{u_0x_0, u_1x_1, x_0x_1\}`; `R′ = \{u_2x_2, u_3x_3, x_2x_3\}`; `S = T ∪ R`, `S′ = T ∪ R′`. Through the canonical evaluators (`gexist.defect_direct`, `gorient.pair_slack`, `gorient.attachment_check`):

| set | branches | `defect_A` | `g` | chunk | binding |
|---|---|---|---|---|---|
| `T = S ∩ S′` | 16 | **0** | 3 | yes | yes |
| `S` | 19 | **2** | 1 | yes | **yes** |
| `S′` | 19 | **2** | 1 | yes | **yes** |
| `S ∪ S′` | 22 (**proper**) | **4** | −1 | yes | **NO** |

`slack = 0` both ways — `gorient.pair_slack` returns `#X-hubs = 0`, and the (GR-38)(i) identity closes as `2 + 2 = 4 + 0 + 0`. `gorient.attachment_check` reports one component per side, each attached at exactly **2** hubs, all of type `'23'`: `R′` at `\{u_2, u_3\}`, `R` at `\{u_0, u_1\}` — two disjoint 2-member AA `(2,3)`-families, which is (GR-38)(iii)'s own description of the AA-glue configuration, met literally.

**The charges, all tight.** `n_2 = 4`, `n_3 = 8`, `|X| = 4`, `q_T = 0`, `p = 8`, `|T| = 16`; `2p = 16 = 3·8 − 2·4 − 0` ✓; B-darts at the X hubs `4 = (3·4 − 4 − 0)/2` ✓; B-darts at the corners `16 = 2·4 + 8 + 0` ✓; A-darts at the corners `8 = p` ✓. So `n_3 = 2n_2 + 2q_T`, `|X| = n_2 + 2q_T`, `n_hub = 4(n_2 + q_T) = 16` — **every inequality of (GR-80)/(GR-81)/(GR-82) is an equality**, which is what makes the boundary exact rather than merely bracketed. The witness realizes the `(|F₁|, |F₂|, |W|) = (4, 0, 4)` member of (GR-82)(iv)'s three profiles.

**Rank certification.** The binding verdicts above come from the (GR-28)(i) *formula*; they are re-derived here **without** it. `gridwit.subgraph_g` computes `g` by pure cycle-rank arithmetic on the contracted multigraph of block A (`|E_A| = 27`, cycle rank `h = 9`, `n_c = 19`) and returns `g(T) = 3`, `g(S) = g(S′) = 1`, `g(S ∪ S′) = −1` — the formula's four predictions, exactly. And the obstruction is real, not a formula artifact: the exact rational `grid.dim_Z` in block A is **3**, and `grid.dim_Z_generic` — the **minimum** over seeded random label draws, so no σ-fixed special value is read as generic (§(K-clos) (AC-9)) — is **3** as well. `dim Z = 3 > 0` in block A at generic labels.

**Which of the three templates it realizes: none of them.** The three (GR-76)(iv) templates live at `n_hub = 10` and are dead by (GR-82). The witness realizes the `n_hub = 16` analogue `(4, 0, 4)`. This is worth saying plainly because the dispatch's two branches were posed as alternatives: **both fired**, on different strata, and that is the result — not a hedge between them.

**"Is it fully good?" — the question as posed has an empty answer, and the meaningful version is E1.** A binding chunk *is* a `g ≥ 1` obstruction, and "fully good" is `a = 0 ∧ max_P g(P) ≤ 0`; so a realized AA-glue configuration can **never** sit at a fully-good colouring. The dispatch's *"a realized AA-glue that is still fully-good is a much weaker event"* names an **empty** case, not a weaker one. What is *not* empty, and is the E1 question, is whether the witness **shape** still carries a fully-good colouring somewhere. It does: over the shape's **123 740** admissible colourings and its **22 086** chunks (**1 541** in the (GR-36)/(F-b) binding-capable family, an exact family), the **first** colouring the enumerator emits is already fully good in both blocks. One fully-good colouring settles E1 for a shape, so this is a complete answer with no cap attached.

**Not a knife edge.** Over a family of 5 interior-corner assignments × 6 `W`-length rotations (30 members), **8** give a habitat-gated, admissible AA-glue configuration with the kill failing — 6 fail the habitat gate and 16 fail admissibility (the `first`-dart pattern is not re-tuned per rotation, so those are construction misses, not obstructions). Their `(defect_A(S), defect_A(S′), defect_A(T), defect_A(S ∪ S′))` split as `(2,2,0,4)` and `(2,1,0,3)`. The phenomenon survives perturbation of both free parameters.

---

### Step G103 — (GR-84): what else breaks at `n_hub = 16` — the whole residual, and the laminarity corollary — and the hand-off

> **(GR-84)** *(measured, EXHAUSTIVE over all 22 086 chunks of the witness
> graph in BOTH blocks, at **ONE** colouring — the witness colouring; not a
> stratum scan, `--lam`)* At the witness colouring, in **each** block:
> **19** binding chunks, **3** of them **maximal**; **66** crossing binding
> pairs, of which **11** lie in the kill residual `slack + defect(T) ≤ 1`,
> **2** are **AA-glue** (`slack = 0 ∧ defect(T) = 0`), and **9** are **kill
> failures** (proper union, not binding). All **3** pairs of **maximal**
> binding chunks **CROSS**, with `(slack, defect(T), defect(union))`
> histogram `{(0,1,3): 1, (1,0,3): 2}`. Hence
>
> **(i)** the **whole** kill residual is inhabited at `n_hub = 16`, not only
> its AA-glue case — the `n_hub = 16` analogue of (GR-75)(ii) is **false**;
> **(ii)** **(GR-75)(iii)'s corollary fails to extend**: the **maximal**
> binding family of a block is **not** laminar at `n_hub = 16`.

**Reading (ii) precisely, because it is a corollary that fails and not a theorem that is refuted.** (GR-75)(iii) is an `n_hub = 8` statement and stands verbatim: there, the residual is empty, so every crossing binding pair has a binding union, so two *maximal* binding chunks cannot cross. (GR-77) already corrected the reading of what that buys — outright binding laminarity is false at `n_hub = 8` (3 774 crossing pairs), and what survives is the **uncrossing** of the maximal family. (GR-84)(ii) says that survivor does **not** reach `n_hub = 16`. So the sequence of readings is: laminar outright at `n_hub ≤ 6` (by emptiness of crossing, (GR-38)(iii)); maximal-laminar at `n_hub = 8` (by emptiness of the residual, (GR-75)(iii)); **neither**, from `n_hub = 16`. A successor that wants laminar targets past `n_hub = 14` cannot get them from the kill, and (GR-35)(ii)'s reading of the uncrossing as manufacturing (GR-24)'s privacy hypothesis loses its supply there.

**What this does and does not do to the arc's target.** Nothing about it is a (GR-15) move. A binding chunk is a property of a *colouring*, and the witness shape carries fully-good colourings in abundance (*Step G102*); the target is *existence* of a fully-good colouring per shape, and no shape has been shown to lack one. What dies is an **organizational** tool — the uncrossing — which (GR-35)(ii)/(GR-38)(iii)/(GR-75)(iii) had been supplying to the charge apparatus. That is a real loss for the (a′)/(b′) machinery's *bookkeeping*, and it is not a loss for `hK`.

**Hand-off — the four things a successor should take, in order.**

1. **The `n_hub` boundary is exact for the AA-glue case; the residual's other two cases are NOT bounded.** (GR-82) bounds `slack = 0 ∧ defect(T) = 0`. The residual `slack + defect(T) = 1` — cases `(0,1)` and `(1,0)` — is bounded **only at `n_hub = 8`**, and only by (GR-75)(ii)'s exhaustive scan; nothing in this pass or in (GR-76) touches it at `n_hub ≥ 10`, and (GR-84) shows both cases are **realized** at `n_hub = 16`. Redoing *Steps G98–G101* with a one-unit defect budget `δ = defect_A(T) ≤ 1` is the natural next pass: (GR-79)'s per-term vanishing becomes "at most one term is 1", each charge loosens by a bounded amount (each A-dart at a corner beyond the `p` supply, and each interior-interior `T`-branch, has to be paid for out of `δ`), and the question is whether the resulting bound is still finite. Cheap, self-contained, and the honest completion of attack (c).
2. **Is `n_hub = 16` the true first realization, or only the first that the counting system permits?** (GR-82)(iv) leaves three profiles at `n_hub = 16` and *Step G102* realizes one of them. Whether the other two — `(0,2,6)` and `(2,1,5)` — are realizable, and whether the `n_hub = 16` AA-glue instances form one family or several, is an `n_hub = 16` census question. The pool is out of reach as a whole (the `n_hub = 16` labelled stratum is far past the `n_hub = 10` one that already costs ~50× `n_hub = 8`), but a **template-restricted** pass in this direction's idiom — build the frame, vary the free parameters, gate through `cubic_habitat` — is affordable and is how *Step G102*'s witness family was produced.
3. **What the charge apparatus should do now that the uncrossing is gone.** (GR-84)(ii) removes the laminar-targets supply that (GR-35)(ii) was providing to the (GR-24) privacy route past `n_hub = 14`. The two visible options are (a) find a *different* sufficient condition for simultaneous guided repair that does not need laminarity, or (b) re-derive laminarity for a **smaller** family than "maximal binding" — the `--lam` census says the 3 maximal chunks per block pairwise cross at *this* colouring, but says nothing about, e.g., the capacity-tight family. Option (b) is measurable with `--lam`'s machinery at one extra filter.
4. **The witness is a reusable object, and the first `n_hub = 16` habitat shape the arc has built.** `gtmpl.witness_specs()` / `build_witness()` produce a habitat-gated 16-hub shape with 24 branches, 46 subdivision vertices, 123 740 admissible colourings and 22 086 chunks, all enumerable in seconds, with an exact `dim Z` computation that runs. Several arc questions currently pinned at `n_hub ≤ 8` for pool reasons are testable *at a shape* here even where they are not testable *over a stratum* — the same role (GR-30)'s `W3M` has played at `n_hub = 8`.

---

### Verification (Steps G98–G103)

`notes/scripts/w4/gtmpl.py` (**new with this pass**; imports — all read-only — `kbare_common` (`verts_of`), `gridcol` (`subdivide`), `cflank` (`admissible`, `cubic_habitat`, `excess_profiles`, `hub_model`), `gcap` (`branch_stats`, `subset_eidx`), `gexist` (`defect_direct`, `incidence`), `gorient` (`attachment_check`, `pair_slack`), `gridwit` (`subgraph_g`), `grid` (`block_data`, `dim_Z`, `dim_Z_generic`), `gunif` (`wit_colouring`), `nogood_subdiv` (`deficiency`, `hcard_ok`, `hub_set`, `triangles`), and `aglu` (`admissible_bits`, `chunks_of`, `crossing_pairs`, `cubic_iso_classes`, `dartmask`, `degmap`, `jfree`) — the last group being the direction immediately below this one in the (K-grid) chain, whose devices are the landed ones for this exact question and each cross-certified against the canonical layer in `aglu --val`; reimplementing them would have been a divergence). **Two local devices**, both with a stated rationale and both cross-certified in `--val`: `chunks_via_complement` (a performance replacement for `aglu.chunks_of` at `M = 24`, where the latter's `2^M` prefix table is 16.7 M entries — a chunk is exactly a set of `deg_S = 0` hubs plus a matching of the rest, so this is a `2^n` scan; asserted **set-equal** to `aglu.chunks_of` at every class at `n_hub = 4, 6` and at seeded classes at `n_hub = 8`) and the `TYPES` table (the `(ℓ, majority) → (c, e, bend)` dictionary, asserted against `gexist.defect_direct` + `gcap.branch_stats` on constructed single-branch instances covering all six rows). Exact integers throughout; nothing samples a placement, so `repin.star_generic` gates nothing (§(K-clos) (AC-9)'s discipline, as for `aglu.py` / `gorient.py` / `cflank.py`); the one rank computation is `grid.dim_Z_generic`, which takes the **minimum** over seeded random label draws precisely so no σ-fixed special value is read as generic. Rngs seeded per mode (seed printed); every printed collection is sorted. Wall-clock `[Ns]` annotations are inherently non-deterministic; every other byte is seed-stable.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --charge   #   5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --frame    # 176 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --tpl      #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --min      #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --wit      #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --e1       #   9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --lam      #   2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/gtmpl.py --val      # 160 s
```

Every invocation was run **in the foreground, one at a time, with an explicit timeout**; each fits the 600 s budget alone, so no mode needed splitting, and the eight together total ~352 s.

**What each invocation produced.** `--charge`: the six-row table's identity; then, over the complete `n_hub ≤ 6` stratum — **4 920** habitat shapes (10 / 312 / 4 598 at `n_hub = 2 / 4 / 6`) and **284 512** admissible colourings (42 / 4 818 / 279 652), reproducing (GR-38)'s own stratum figures exactly — the per-branch identity and the 2-1 pattern at **2 545 902** (colouring, branch) instances, plus `Σe = 6`, `Σc = 3`, `Σ bend = M` and `#{A-maj hubs} = n_hub/2` at every colouring. `--frame`: **92 / 2 675 / 82 201** crossing chunk pairs at `n_hub = 4 / 6 / 8`, **7 / 285 / 9 263** at slack 0 (both matching AGLU's `--pin`), **0 / 0 / 44** with a J-free intersection, all 44 with `(n_2, n_3, |T|, #cc) = (4, 4, 10, 2)` and nothing else, and (GR-80)'s kill asserted at all 44. `--tpl`: the nine (template, `q_T`) cells, each with both charges FAILING, **6/2/0**, **11/3/0**, **3/1/0** `(c, e)`-consistent type multisets examined and **0** survivors; then **0** aggregate frames and **0** full solutions at `n_hub = 10, 12, 14`, **3** frames / **59** solutions at 16, **6/121** at 18, **15/269** at 20. `--min`: the feasible list from `n_hub = 16` up, and the three `n_hub = 16` frames all on `(4, 8, 4, 0, 8)`. `--wit`: the witness's habitat gate, tightness `270 = 270`, `deficiency = 0`, `hcard_ok`, 0 two-hub triangles, admissibility, `{1,2}` A-darts at all 16 hubs, the four-row defect table, the slack identity `2+2 = 4+0+0`, `#X-hubs = 0`, the attachment classification, all three charges tight, the four exact `subgraph_g` values, and `dim Z = 3` at both label choices. `--e1`: 22 086 chunks / 1 541 binding-capable / 123 740 admissible colourings, a fully-good colouring at the first one tried, and 8 of 30 family members realizing the configuration. `--lam`: the per-block census of *Step G103*. `--val`: the four cross-certifications.

**CAP DISCLOSURE — mandatory, per the §(K-grid) cap-exhaustion gate (`731b3e33`) and LTWO's *"4 of 8 patterns"* precedent. An exhausted cap is not a proof of nonexistence, and none of the negatives below rests on one.**

- **(GR-82)'s negative takes NO cap.** It is a **proof** (an inequality chain on (GR-79)/(GR-80)/(GR-81)), and the machine side is a walk of a **finite** parameter box, not a sample: `--tpl`'s per-template enumeration is complete over the `(c, e)` budget splits, the type multisets, the even-`W` orientations and the `F₁` X-end splits; `--min`'s search is complete over every even `n_hub ≤ 40` and, at each, over the full `(n_2, n_3, |X|, q_T, p, |F₁|, |F₂|, |W|)` range the identities allow. **`n_hub ≤ 14` is settled by proof, and separately by exhaustion of a finite box — not by a budget.**
- **`--min`'s `n_hub ≤ 40` window is a WINDOW, and it is not load-bearing.** The bound `n_hub ≥ 16` is proven for all `n_hub`; the window only exhibits where the system first becomes feasible. Nothing is claimed about `n_hub > 40`.
- **No `n_hub = 10` or `n_hub = 16` labelled stratum was enumerated, and none is claimed.** The dispatch's cost check came first and the answer was the one AGLU predicted: the `n_hub = 10` pool is ~50× the `n_hub = 8` one with the canonicalizer as the bottleneck, and `n_hub = 16` is far past that. **The template-restricted route was taken instead, exactly as directed, and it turned out to need no pool at all.** So: (GR-82) is pool-free; (GR-83) is a **single constructed witness** plus a 30-member parametrized family, **not** a census; (GR-84) is exhaustive over the witness graph's chunks but at **ONE colouring** of **ONE shape**.
- **What (GR-84) does NOT say.** It makes no claim about the witness shape's other **123 739** admissible colourings, none about other `n_hub = 16` shapes, and none about the distribution of `(slack, defect(T))` beyond the 66 crossing pairs it measures. In particular *"11 residual / 2 AA-glue / 9 kill failures"* is a count **at one colouring**, and must never be quoted as an `n_hub = 16` rate.
- **The E1 answer is a POSITIVE and therefore cap-free**: one fully-good colouring exists, exhibited. The complementary negative — *"every colouring of every `n_hub = 16` habitat shape is …"* — is neither claimed nor attempted.
- **`--val`'s `n_hub = 8` chunk-enumerator check is a seeded 6-of-20 subsample** (the `n_hub = 4, 6` checks are complete over all classes). Disclosed here rather than carried into a headline.
- **The one habitat conjunct not re-run at the witness** is `kslide.no_rigid_branch_union` (`2^M` with a matroid rank inside, out of reach at `M = 24`). The (GR-25) criterion `cflank.cubic_habitat` is the arc's oracle in its place — the same one AGLU's exhaustive `n_hub = 8` scan is gated by, proven equivalent to `gridcol.class_shape` on the entire `n_hub ≤ 6` pool by `cflank --law` — and three of `class_shape`'s four conjuncts (tightness, `deficiency = 0`, `hcard` + no two-hub triangle) are re-run directly at the witness as an independent cross-check.
- **No rank claim beyond the witness.** `dim Z` was computed at **one** colouring of **one** shape. Per-shape (GR-15) is not claimed anywhere in this pass, at any `n_hub`.
- **Not re-opened, not re-run, not attempted:** (GR-28)(iv)'s `g ≤ 1` cap; the (GR-39)/(GR-40) fully-hot census; the `n_hub = 8` (GR-75) scan (AGLU's is exhaustive and uncapped, and *Step G99* reproduces its verdict by a third route without re-running it); **(d′)**. AGLU's hand-off item 2 (the `(slack, defect(T)) = (0,2)/(1,1)` tightness) was **NOT** attacked — it needs a stratum, and the primary's route deliberately avoided one; it stays open exactly as AGLU left it, with the added datum that at `n_hub = 16` the values `(0,1)` and `(1,0)` occur, so a `= 2` law would be `n_hub = 8`-specific.

**The F11 table — which driver mode tests which sentence.** ("Exhaustive", "the only", "forced" and "not realizable" are their own claim class and get their own modes.)

| sentence | mode | what is asserted |
|---|---|---|
| (GR-81)(i) `bend = e − 2c + 1` at **every** branch — universal claim | `--charge` | the identity per branch at **all 2 545 902** (colouring, branch) instances of the complete `n_hub ≤ 6` stratum, together with `bend == (end darts that are B)` read off `aglu.dartmask`, and the alternation fact `du == dw ⟺ ℓ odd` |
| (GR-33)'s 2-1 pattern (the hypothesis both charges use) | `--charge` | `A-dart count ∈ {1, 2}` at **every hub** of **every** admissible colouring of the stratum; `{0, 3}` would abort |
| (GR-81)(ii) the two global corollaries | `--charge` | `Σ bend == M` and `#{A-majority hubs} == n_hub/2` at every colouring, alongside `Σe == 6` ((GR-21)) and `Σc == 3` ((GR-32)(iii)) |
| the pool is the landed one | `--charge` | `assert shapes == 4920 and ncol == 284512` — (GR-38)'s own stratum figures, reproduced through this driver's own pool builder |
| (GR-79)(ii) no interior-interior `T`-branch — **exhaustiveness claim** | `--frame` | asserted at **every** slack-0 J-free crossing pair of **every** class at `n_hub = 4, 6, 8` |
| (GR-79)(iii) the corner ledger `2p = 3n_3 − 2n_2 − 2q_T` | `--frame` | `len(ic) == 2n_2`, `len(T) == 2n_2 + len(cc)`, `2 len(T) == 2n_2 + 3n_3`, `2 len(cc) == 3n_3 − 2n_2` asserted at every such pair |
| (GR-73)(ii) `deg_T ∈ {2,3}` at slack 0 (re-asserted, borrowed) | `--frame` | at all 7 / 285 / 9 263 slack-0 pairs |
| (GR-74)(iii)'s `n_hub = 8` pinning reproduced through a second driver | `--frame` | the profile histogram `{(4,4,10,2): 44}` asserted exactly — a second row would print |
| (GR-80) kills `n_hub = 8` — the third proof of (GR-75)(i) | `--frame` | `assert pq < n3` at all 44 premise-satisfying pairs |
| (GR-82)(ii) the three templates are **NOT realizable** | `--tpl` | per (template, `q_T`): both charges asserted to FAIL, **and** a raw enumeration with both charges switched off asserted to return **0** survivors |
| the `0` survivors are **not vacuous** | `--tpl` | the number of `(c, e)`-consistent type multisets is printed per cell and asserted `> 0` in aggregate over `q_T ≤ 1`; `q_T = 2` asserted to have **none**, which is (GR-76)(iv)'s own `q_T ≤ 1` |
| (GR-82)(i)/(iii) `n_hub ≤ 14` all dead | `--tpl`, `--min` | `assert not frames and not solutions` at `n_hub = 10, 12, 14`; the full search over every even `n_hub ≤ 40` reports 16 as the least feasible |
| the enumerator **fires** (non-vacuity) | `--tpl` | `assert frames and solutions` at `n_hub = 16` — 3 frames / 59 solutions, printed |
| (GR-82)(iv) the `n_hub = 16` profile is **forced** | `--min` | every enumerated `n_hub = 16` frame asserted equal to `(n_2, n_3, |X|, q_T, p) = (4, 8, 4, 0, 8)` |
| derivation ≡ enumeration | `--val` (3) | no enumerated frame at `n_hub ≤ 32` violates the closed-form (GR-80)/(GR-81)/(GR-82) charges |
| (GR-83) the witness is in the **habitat** | `--wit` | `cflank.cubic_habitat` (the landed (GR-25) oracle) plus three of `gridcol.class_shape`'s four conjuncts run directly (`5\|E\| = 6(\|V\|−1)`, `nogood_subdiv.deficiency == 0`, `hcard_ok`, 0 two-hub triangles) |
| (GR-83) the colouring is **admissible** | `--wit` | `cflank.admissible` on the subdivision — the canonical predicate, not a local device |
| (GR-83)(i) it **IS** the AA-glue configuration | `--wit` | `gexist.defect_direct`: `defect_A(T) == 0`, `defect_A(S) ≤ 2`, `defect_A(S′) ≤ 2`; `gorient.pair_slack` `== (0, 0)`; the (GR-38)(i) identity asserted; `gorient.attachment_check` asserted to give two disjoint 2-member `'23'` families |
| (GR-83)(ii) the **kill FAILS** | `--wit` | `assert len(union) < M` and `assert defect_A(union) > 2` — proper and not binding |
| (GR-83)(iii) the bound is **TIGHT** | `--wit` | `n_3 == 2n_2 + 2q_T`, `\|X\| == n_2 + 2q_T`, `n_hub == 4(n_2 + q_T) == 16` asserted, plus the two B-dart counts of (GR-81)(iii) |
| the binding verdict is **rank-certified**, not a formula artifact | `--wit` | `gridwit.subgraph_g` (pure cycle-rank arithmetic on the contracted multigraph, **independent** of (GR-28)(i)) asserted equal to `3 − defect` at all four sets; and `grid.dim_Z_generic > 0` — an exact rational rank at generic labels |
| (GR-83)(iv) **E1 does not fire** | `--e1` | a fully-good admissible colouring of the witness shape exhibited (no binding chunk in either block over the exact binding-capable family) |
| the witness is a **family**, not a coincidence | `--e1` | `assert ok >= 2` over 30 parametrized members; 8 realize it |
| (GR-84)(i)/(ii) the residual is inhabited and maximal laminarity **fails** | `--lam` | exhaustive over all 22 086 chunks in both blocks at the witness colouring: `assert aaglue >= 1 and killfail >= 1` and `assert crossmax >= 1`, with the `(slack, defect(T), defect(union))` histogram printed |
| chunk enumerator ≡ `aglu.chunks_of` | `--val` (1) | **set** equality at every class at `n_hub = 4, 6`; seeded 6-of-20 at `n_hub = 8` |
| the `(c, e, bend)` table ≡ the canonical evaluators | `--val` (2) | `gcap.branch_stats` + `gexist.defect_direct` on constructed single-branch instances, all six rows |
| the witness figures have not drifted | `--val` (4) | the headline 5-tuple `(0, 2, 2, 4, 0)` recomputed from scratch |

---

### Confidence verdict (Steps G98–G103)

| | claim | standing |
|---|---|---|
| **(GR-79)** | the B-flooded frame: `A(β) = 1` on `T`, interiors AA with B free darts, no interior-interior `T`-branch, interior-incident branches `ℓ = 2` with B at the corner, the corner ledger, and the `p` corner A-darts | **proven** — a per-term non-negativity argument on the landed (GR-28)(i) formula plus one dart case check; the ledger machine-asserted at **every** slack-0 J-free crossing pair at `n_hub = 4, 6, 8`. Clause (ii) is (GR-74)(i) **re-derived**, not re-cited |
| **(GR-80)** | the corner charge `n_3 ≥ 2n_2 + 2q_T` | **proven** (one pigeonhole on (GR-79)(iv) plus (GR-33)); its `n_hub = 8` kill machine-asserted at all 44 premise-satisfying pairs. **General-`n`**, `n_hub`-free |
| **(GR-81)(i)–(ii)** | the universal dart identity and its two global corollaries | **proven** (three length/majority cases); asserted at **2 545 902** (colouring, branch) instances over the **complete** `n_hub ≤ 6` stratum, with the pool reproducing (GR-38)'s own figures exactly |
| **(GR-81)(iii)–(iv)** | the exact B-dart count at the X hubs, hence `\|X\| ≥ n_2 + 2q_T` | **proven** (bookkeeping on (i)+(GR-79)); **strictly stronger than (GR-76)(i)**, which is the same count's `≥ 0` instance. **General-`n`** |
| **(GR-82)(i)–(iii)** | `n_hub ≥ 4(n_2 + q_T) ≥ 16`; the AA-glue configuration is impossible at **every `n_hub ≤ 14`**; the three (GR-76)(iv) templates are **NOT realizable** | **proven**, and **`n`-free**; independently certified by an exhaustive walk of a **finite** parameter box (no cap, no sample), and by a raw per-X-hub dart enumeration run with both charges switched off. Subsumes (GR-76)(iii) and, through *Step G99*, (GR-75)(i) |
| **(GR-82)(iv)** | the `n_hub = 16` profile is forced to `(4, 8, 4, 0, 8)` with three `(\|F₁\|, \|F₂\|, \|W\|)` options | **proven** (equality analysis) and machine-asserted over the enumerated frames |
| **(GR-83)(i)–(ii)** | the AA-glue configuration **IS realizable** at `n_hub = 16`, and the **(GR-38) kill FAILS** there | **proven by witness** — the strongest kind of positive: an explicit habitat-gated shape, an explicit admissible colouring, both verified by the **canonical** predicates (`cflank.cubic_habitat`, `cflank.admissible`), and the defects/slack/attachment by the **canonical** evaluators (`gexist.defect_direct`, `gorient.pair_slack`, `gorient.attachment_check`) |
| **(GR-83)(iii)** | the bound is **EXACT**: theorem at `n_hub ≤ 14`, false from `n_hub = 16` | **proven** — both halves; all three charges hold with **equality** at the witness |
| the binding verdict at the witness | | **rank-certified**: `gridwit.subgraph_g` reproduces all four `g` values by cycle-rank arithmetic independent of (GR-28)(i), and `grid.dim_Z_generic` gives an exact rational `dim Z = 3 > 0` in block A at generic labels |
| **(GR-83)(iv)** | the witness shape is **not** a g-flank; **E1 does not fire** | **proven by witness** (a fully-good colouring exhibited). Cap-free, being a positive |
| "a realized AA-glue that is still fully good" | | **an EMPTY case, not a weaker one** — a binding chunk *is* a `g ≥ 1` obstruction. The dispatch's dichotomy is corrected here, plainly |
| **(GR-84)(i)** | the **whole** kill residual is inhabited at `n_hub = 16` | **measured**, exhaustive over all 22 086 chunks of the witness graph in both blocks, at **ONE** colouring. The **existence** statement is therefore proven by witness; the **counts** are one-colouring measurements and must not be read as rates |
| **(GR-84)(ii)** | (GR-75)(iii)'s laminarity corollary **fails** at `n_hub = 16` | **proven by witness** (three crossing pairs of maximal binding chunks per block). Note the crossing maximal pairs sit at `(slack, defect(T)) ∈ {(0,1), (1,0)}`, **not** at the AA-glue's `(0,0)` |
| the `slack + defect(T) = 1` residual at `n_hub ≥ 10` | — | **OPEN, and untouched by this pass** — (GR-82) bounds only the AA-glue case. Named as hand-off item 1 with the exact modification the charges need |
| AGLU's hand-off item 2 (the `(0,2)/(1,1)` tightness) | — | **NOT attempted.** Datum added: at `n_hub = 16` the crossing maximal pairs realize `slack + defect(T) = 1`, so any `= 2` law is `n_hub = 8`-specific |
| **(GR-15)** | | **OPEN**, unchanged in both directions; **no gap-map status move on `hK`**. No rank claim beyond the witness's own `dim Z`; class uniformity untouched |
| **(GR-38)(i)/(ii)/(iii)** | | **untouched as mathematics.** (i) and (ii) are re-asserted at the witness (a stratum never asserted on before); (iii)'s dichotomy is *satisfied* by the witness, on its residual branch. What is corrected is the **reading** of what (iii)'s kill buys past `n_hub = 8` — by (GR-84), not by contradicting any landed figure |
| **(GR-75)/(GR-76)/(GR-77)** | | **untouched as mathematics**, and (GR-75)(i) gains a third proof. (GR-76)(iii)'s `n_hub ≥ 10` is **superseded** by the stronger `n_hub ≥ 16`, not refuted; (GR-76)(iv)'s three-template list is **confirmed as a pinning** and then **emptied** |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side as TCOL's through AGLU's: exact GF(2) / integer combinatorics on constructed hub multigraphs, never `PencilNondegFeasible G`. The one departure from AGLU is that this pass **does** compute a rank — `grid.dim_Z` / `dim_Z_generic` at the witness — and it is a **grid**-model rank on the σ-fixed configuration's contracted multigraph, taken at **generic** labels via the min-over-draws device, so no σ-fixed special value is read as generic (§(K-clos) (AC-9)). No sampler draws a placement anywhere.

### What would change this (Steps G98–G103)

- **(GR-80) or (GR-81) overturned** would need a defect in the one landed input each leans on beyond (GR-79): (GR-33)'s mono-hub 2-1 pattern for both, plus (GR-21)'s excess law and (GR-32)(iii)'s balance identity for (GR-81)(ii). All three are re-asserted at **every** admissible colouring of the complete `n_hub ≤ 6` stratum in `--charge`, whose pool reproduces (GR-38)'s own figures exactly — the strongest single check available. A subtler failure mode is a **frame** claim: if some AA-glue configuration had a `T`-hub of `deg_T ∉ {2,3}` (refuting (GR-73)(ii)) or an interior-interior `T`-branch (refuting (GR-79)(ii)), the corner ledger would change. `--frame` asserts against both at every slack-0 pair at `n_hub = 4, 6, 8`; at larger `n_hub` they are proven, not measured.
- **(GR-82) sharpened.** Both charges use only the *existence* of one A-dart (resp. one B-dart) per hub. The 2-1 pattern says more — a hub has **exactly** one minority dart — and the `save`/weakness frame of (GR-33) prices exactly which darts those are. Pushing the bound past 16 therefore needs a constraint that couples the corner side to the X side; the visible candidate is that (GR-83)'s witness forces **every** corner B-majority and **every** X hub A-majority, i.e. the `n_hub/2` A-majority budget of (GR-81)(ii) is *also* tight there. Whether that is forced or accidental is one `--min` filter away.
- **(GR-83) overturned** would need the witness to fail a gate. The four that matter are `cflank.cubic_habitat` (the (GR-25) criterion — cross-checked by three of `gridcol.class_shape`'s four conjuncts, the fourth being the `2^M` scan (GR-25) exists to replace), `cflank.admissible` (the canonical predicate, run on the subdivision), `gexist.defect_direct` (the canonical evaluator, cross-checked by `gridwit.subgraph_g`'s independent cycle-rank computation), and the chunk-ness of `S`, `S′` (connected, bridgeless, degrees in `{2,3}` — the `aglu.chunks_of` family, whose enumerator is `--val`-certified). A **fifth** possibility, and the honest one to name: if the arc's habitat notion at `n_hub ≥ 10` were ever found to need a conjunct that `cubic_habitat` does not express, this witness and AGLU's `n_hub = 8` scan would both need re-gating — they rest on the same oracle.
- **(GR-84)(ii) sharpened** by asking the same question of a **smaller** family than "maximal binding" (capacity-tight, or the `(GR-36)` binding-capable family intersected with a size bound), and over **more than one colouring** of the witness shape. `--lam` does both at one extra filter and one extra loop; the cost is that the second is a 123 740-colouring scan, which needs slicing.
- **The residual `slack + defect(T) = 1` is where this could all still be `n_hub ≤ 14`-shaped and turn out to matter less than it looks.** (GR-82) is a clean exact boundary for the AA-glue *case*; if the residual's other two cases are realizable well **below** `n_hub = 16` — and nothing rules that out at `n_hub = 10, 12, 14` — then the (GR-38) kill already fails there for a reason this pass did not look at, and the "attack (c) closes at `n_hub ≤ 14`" headline would need the qualifier *"for the AA-glue case"* doing more work than it looks like it is doing. **That qualifier is carried explicitly in every statement above, and hand-off item 1 is exactly this.**

---

### TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator re-runs it

**E1 does NOT fire.** E1 needs a **g-flank** — a `D = 0` shape whose *every* admissible colouring is binding. This pass exhibits the opposite at the one new shape it built: the `n_hub = 16` witness shape carries a fully-good admissible colouring (the *first* one its enumerator emits), so it is not a g-flank. Nothing else in the pass is a flank candidate: the witness colouring's 19 binding chunks per block, its 2 AA-glue instances and its 9 kill failures are all properties of **one particular colouring** at a shape that has 123 740 of them, and a binding chunk at one colouring is not a flank. (This is exactly (GR-77)'s distinction, carried forward.)

**E2 does NOT fire.** E2 needs the direction's target refuted-or-unprovable-as-posed **and** no ledger entry left in state open-with-a-named-dispatchable-attack. Neither half holds. The target — AA-glue realizability at `n_hub ≥ 10` — is **settled**, not unprovable: negative at `n_hub ≤ 14` by an `n`-free proof, positive at `n_hub = 16` by witness. Attack (c) therefore moves from *"open at `n_hub ≥ 10`, three templates"* to *"the AA-glue case is settled with an exact boundary; the `slack + defect(T) = 1` residual is open at `n_hub ≥ 10` with a named, cheap, self-contained successor"* — a **narrowing with a successor named**, which the E2 carve-out explicitly does not fire on. Attacks (a′), (b′) and (d′) are untouched and remain dispatchable.

**E3 stays ARMED and is NOT fired.** E3 is armed by GBAL's entry-5 HIT and fires only when the target is **proven** with every remaining ledger entry adjudication-gated. GTMPL is on the §(GR-38)/attack-(c) path, not the (a′) path; it proves nothing about (GR-15), computes no uniformity claim, and leaves (a′)/(b′) dispatchable. The arming state is **unchanged**. **Firing is a coordinator action; this direction does not fire it.**

**So: no escalation from this direction.** The one thing worth surfacing to the coordinator as a *reading* rather than a trigger: (GR-84)(ii) removes an **organizational** tool the charge apparatus had been using (the uncrossing / laminar targets) at every `n_hub ≥ 16`. That is not an E-clause event — it costs no ledger entry its dispatchable state — but it does change what a successor on the (a′)/(b′) path can assume, and hand-off item 3 names the two visible replacements.

**Riders, verbatim.** Everything at `Λ = ∅`, `D = 0`, and **modulo (GR-4′)** wherever (GR-15) is mentioned; `Λ ≠ ∅` and `D > 0` stay **unswept**. **None of this closes (GR-15)**, and a counting-side result is not an `hK` status move; the one rank computed here is a single witness's `dim Z`, not a per-shape (GR-15) claim. Every obstruction figure carries its **family qualifier** — (GR-36)'s **binding-capable** family strictly contains the capacity-tight one, and (GR-40)'s 815 → 573 is a **prune, not a zero**. **(GR-77) stands:** outright binding laminarity is FALSE at `n_hub = 8` (3 774 crossing pairs), so (GR-75) is never quoted here as laminarity — it buys the **uncrossing** of the **maximal** binding family per block, and (GR-84)(ii) shows even that does not reach `n_hub = 16`.

---

---

### Steps G104–G109 (2026-08-19, direction GFLOW) — (b′)'s availability half is **RESHAPED, and (b′) gains its first proven `n`-free constant**: **(GR-85)** turns `dist(·, M)` at a fixed odd pattern into a **changeover count** `#{v : A(v) = 1}` over the even-branch orientations *inside the 2-factor*, with `M` entering only as three local conditions per matching branch — and reads off the correction that route 3's own instrument is wrong (the objective is a **parity** count, not a flow cost, so "min-cost degree-constrained orientation, hence polynomial" does not apply to the *cost* side); **(GR-86)** is the exchange instrument that does work — the **repair-chain theorem**: flipping one odd branch leaves the configuration inadmissible exactly at that branch's blocked ends, each is repaired by a chain of even-branch flips, a chain exists **iff** the flipped pattern is (GR-50)-feasible (0 disagreements at 6 459 208 pairs), and the chain's price telescopes so that it is **independent of the chain's length** and equals (start contributions) + (terminus contributions) — giving `Δdist ≤ 2` in **five of the six** blocking cases and `≤ 4` in the sixth; **(GR-87)** therefore **PROVES sub-clause 1** with **no** far-end side condition — BALB's residual `m(w_β) ≠ β` is not needed, and in its own scope it is **exhaustively TRUE at `n_hub ≤ 6` and FALSE from `n_hub = 8`**; **(GR-88) REFUTES sub-clause 2 as posed** by an exact witness — a doubly-blocked **matching** branch whose one-flip price is **exactly 4**, named at `n_hub = 8`, and never 6 — and corrects two readings of the landed prose (the (1,2,2) price is `|W| − 2|W ∩ S|`, so **one** deviating extra endpoint already gives `≤ 2`, and route 1's named input runs the **wrong way**: optimality *caps* `|W ∩ S| ≤ |W|/2`); **(GR-89)** iterates (GR-86) into the arc's **first proven `n`-free bound of (b′)'s own shape**, `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, modulo one named clause (GR-R1), and **reshapes the residual from a repair statement into a SELECTION statement** — some majority-side odd branch is not a doubly-blocked matching branch — which a **counting bound proves outright whenever `n_hub < 3k + 5|δ|/2`, in particular on the WHOLE `n_hub ≤ 6` stratum**, and which measures with **zero** failures at 96 930 exhaustive stratum configurations and everywhere beyond; **(GR-90)** the status. **(b′) is a HIT of the third kind — a different constant with the exact boundary named — and is NOT proven at the constant 2; (GR-15) stays OPEN, no gap-map status move on `hK` itself; E3 stays ARMED and does NOT fire.** **[Update 2026-08-25: (GR-89)'s one named clause (GR-R1) is PROVEN at *Steps G116–G119* (direction GFLIP), so the `n`-free `≤ 12` bound is now a THEOREM; the standing tables below carry the updated rows.]**

Answering `notes/Pencil-fanout.md` §"GFLOW — twenty-sixth direction
(eighth fan-out)": **Clause A′ sub-clause 2, the doubly-blocked case**, and
sub-clause 1 separately as the spec requires. Rank-free throughout: nothing
imports or calls `gexist.fully_good_rank` and **no `d_fg` claim is made
anywhere** — (a′) / input (Y) is untouched, and **(GR-64)(R2) is GCOLL's
target this wave**, so the one (Y)-adjacent by-product below is *reported*,
not developed. Read against *Steps G86–G91* ((GR-67)–(GR-72)), *Steps
G68–G73* ((GR-49)–(GR-54)), *Steps G58–G62* ((GR-44), (GR-45)) and *Step
G65* ((GR-48)).

***Notation, inherited unchanged, with one deliberate rename.*** `δ = a − b`
is the odd-branch imbalance and nothing else; `O` the odd branches,
`2k = |O| ≤ 6` and even (*Step G53*(ii)); `H` the even branches;
`τ_β = [ℓ_β even]`; `z ∈ GF(2)^E` is (GR-49)'s one bit per branch and
`ζ(v, β)` its dart colour, colour **0 = A**; `n = n_hub`; `M = |E| = 3n/2`.
A perfect matching is fixed and written `M`, its complementary **2-factor**
`F := G° ∖ M`; `S` the hubs where the minority map deviates from `M`; `W(·)`
is (GR-68)'s endpoint set. **The rename:** (GR-68) as landed overloads `F`
for *both* the 2-factor and the flip set. Here the 2-factor keeps `F` and
every **flip set is written `J`**; (GR-68) read in this notation is
`Δdist = |W(J) ∖ S| − |W(J) ∩ S|`. Layers as landed: `d_par(M)`,
`d_adm(M)`, `d_fg(M)`, `d_• = min_M d_•(M)`. **New here:** for an admissible
`z` and a hub `v`, `A(v)` is the number of **A**-coloured darts at `v` among
`v`'s **two `F`-branches**, and `m_v := [ζ(v, M(v)) = A]`; a majority-side
odd branch is **blocked at an end `v`** iff `m(v) = γ`, and **dart-free /
one-end-blocked / doubly blocked** counts 0 / 1 / 2 blocked ends. `f(p)`
denotes the minimum of `dist(·, M)` over admissible configurations with odd
pattern `p`, so `d_par(M) = min_p f(p)` and
`d_adm(M) = min_{p balanced} f(p)`.

**Step 0 pin (mandatory, discharged before any derivation).** (GR-44) in
full (`d_par(M) = w_M` exact, Hall automatic) — consumed, not re-derived.
(GR-45) (legal-move calculus, T1/T2) and (GR-46) (one-move transitivity).
(GR-48) (the reduction criterion, K1/K2/K3, the doubly-blocked kill and its
`n = 30` witnesses). (GR-49)–(GR-54) in full — in particular (GR-49)'s
**flip-set legality test** (`J` carries admissible `z` to admissible
`z + χ_J` iff at every hub `[m(v) ∈ J] = [|J ∩ star(v)| ≥ 2]`), (GR-50)'s
`o_v`/`q_v`/`d_v`/`l_v`/`u_v` and its polynomial decision, (GR-51)(i)(a)/(b)
with its weight table, (GR-52)/(GR-53), and (GR-54)'s theorem. (GR-67) in
full (the anchored identity, the parity law, the changeover
parametrization, Cor. 1's *every per-matching gap is even*). (GR-68) in full
(the closed price formula, `|Δdist| ≤ 2·t(J)`, the free companions, the
minimality corollary). (GR-69) (`|δ| ≤ 2 min(k, ⌊n/4⌋)`; a theorem at
`n ≤ 6`, FALSE from `n = 8` at **V8**). (GR-70) (the reduction to Clause A′;
the stratum verification EXHAUSTIVE at 4780 shapes / 23 939 pairs / 96 930
unbalanced parity-optimal configurations; the T1 instance refuted from
`n = 8`; the mixed-pair successor priced 0 at 48/48 `n = 8` witnesses).
The measured (b′) record with its qualifiers: shape gaps `{0, 1, 2}`; the
necklace shift layer **UNBOUNDED** ((GR-43)); (GR-4′) covers no habitat
block. **Bars honoured:** entry 5 is PROVEN and not re-attacked; (GR-70)(ii)
is not re-run *as a stratum verification* (it is, however, **independently
reproduced** as a by-product — see *Step G109*); (GR-68)'s pricing and
(GR-67)'s parity law are consumed, not re-derived; the bounded-deviation
**selection** form ((GR-41)+(GR-42)) is not re-opened; the `|δ| ≤ 2` half is
not attempted ((GR-69) settled it).

---

### Step G104 — (GR-85): the changeover-cost model — `dist(·, M)` at a fixed odd pattern is a **parity count** over even-branch orientations inside the 2-factor, and `M` enters only as three local conditions

**Why the pass starts here.** BALB's route 3 says: *minimizing `dist(·, M)`
over admissible `z` at a fixed balanced pattern is, by (GR-50), a min-cost
degree-constrained orientation — a min-cost flow, hence polynomial.* Before
using that instrument one has to write the objective down in the orientation
variables. Doing so both supplies the model the rest of this pass runs on
**and refutes the instrument**.

> **(GR-85)** *(proven; certified in BOTH directions — the forward direction
> EXHAUSTIVELY at 2 088 924 (shape, matching, admissible `z`) triples over
> all 23 939 (shape, matching) pairs of the whole `Λ = ∅`, `D = 0` stratum
> (4780 odd-carrying habitat shapes, full `2^{|E|}` `z`-cube, no cap), plus
> V8 and seeded `n = 8/10`; the converse at 11 828 + 8704 + 300 288 + 714 752
> (odd pattern, even-`F` orientation) assignments — the converse enumerates
> `2^{|O|} · 2^{|H ∩ F|}` per pair and is **capped at the first 120 shapes
> per leg**, disclosed; `--model`)*
>
> Let `G°` be cubic and loop-free, `M` a perfect matching, `F = G° ∖ M` its
> 2-factor. For admissible `z` put `A(v) := #{A-darts at v among v's two
> F-branches} ∈ {0, 1, 2}` and `m_v := [ζ(v, M(v)) = A]`.
>
> **(i) The objective.** `v ∈ S ⟺ A(v) = 1`, hence
> > `dist(m, M) = #{v : A(v) = 1} = #{v : A(v) is ODD}`.
>
> **(ii) Admissibility, per hub.** `#A-darts at v = A(v) + m_v ∈ {1, 2}`, so
> `A(v) = 0 ⟹ m_v = 1`, `A(v) = 2 ⟹ m_v = 0`, and at `A(v) = 1` the bit
> `m_v` is **free**.
>
> **(iii) Admissibility, globally — three local conditions.** Fix the odd
> pattern `p` and an orientation of the **even branches inside `F`** (each
> delivers its single A-dart to one end); this determines `(A(v))_v`. An
> admissible `z` realizing those data exists **iff** for every matching
> branch `μ = uw`
> > `μ ∈ O`, A-coloured : `A(u) ≤ 1` and `A(w) ≤ 1`
> > `μ ∈ O`, B-coloured : `A(u) ≥ 1` and `A(w) ≥ 1`
> > `μ` even : `¬(A(u) = A(w) = 0)` and `¬(A(u) = A(w) = 2)`.
>
> So the **only free variables are the even-`F`-branch orientations**: the
> even-`M`-branch orientations are forced except at a matching branch both of
> whose ends have `A = 1`.
>
> **(iv) The `T`-identity.** With `T(p) := 2|O_A ∩ F| + |H ∩ F|`,
> > `Σ_v A(v) = T(p)` — a function of `(p, M)` alone — and
> > `dist = T(p) − 2·#{v : A(v) = 2}`.
>
> Minimizing `dist` at fixed `p` is therefore **maximizing the number of
> hubs whose two `F`-darts are both A**; and `T(p) ≡ |H ∩ F| (mod 2)`
> re-derives **(GR-67)(ii)**'s parity law in one line.

*Proof.* (i) is (GR-67)(i) restated: `m(v) = M(v)` iff `v`'s two non-`M`
darts agree, i.e. iff `A(v) ∈ {0, 2}`. (ii) is (GR-49)'s "not all three
equal" rewritten as `1 ≤ A(v) + m_v ≤ 2`. (iii): a matching branch ties its
two `m`-bits — `ζ(u, μ) ⊕ ζ(w, μ) = τ_μ`, so `m_u + m_w = 1` when `μ` is
even and `m_u = m_w = [p(μ) = A]` when `μ` is odd — and the displayed
conditions are exactly the non-contradiction of that tie against (ii)'s
forcings (`A = 0` forces `m = 1`, `A = 2` forces `m = 0`, `A = 1` forces
nothing). (iv): an A-coloured odd `F`-branch has `τ = 0`, so both its darts
are A and it contributes 2; a B-coloured odd `F`-branch contributes 0; an
even `F`-branch has `τ = 1`, so exactly one dart is A and it contributes 1 —
at whichever end the orientation selects. Summing gives `Σ_v A(v) = T(p)`,
independent of the orientation. With `n_j := #{v : A(v) = j}` we have
`n_1 + 2n_2 = T` and `dist = n_1`, which is the identity; and
`n_1 ≡ T ≡ |H ∩ F| (mod 2)`, which is (GR-67)(ii) since `H ∩ F` is exactly
the even branches outside `M`. ∎

**Reading — route 3's instrument is the wrong one, and this is where it
fails.** (GR-50) makes the **feasibility** side a degree-constrained
orientation, decided in polynomial time (Hakimi 1965, *On the degrees of the
vertices of a directed graph*, J. Franklin Inst. **279**(4), 290–308; the
two-sided form is proved in full at *Step G70*, so nothing rests on the
citation). But by (i) the **objective** is `#{v : A(v) odd}` — a *parity*
count. As a function of a hub's in-degree it takes the values `0, 1, 0`, so
it is **neither linear nor convex**, and min-cost-flow machinery, which needs
convex arc/vertex costs, does not apply to it. The problem in these
coordinates is a `T`-join-flavoured parity minimization *with side
constraints*: minimize `#{v : A(v) odd}` subject to (iii), where the
constraints only bite between two matched hubs both of even `A`-value. On
the even-`F`-branch subgraph alone — which has **maximum degree 2**, hence
paths and cycles — the parity minimization is a linear-time DP; **all of the
difficulty is in the `M`-coupling**, and whether the coupled problem is
polynomial is **left OPEN here** (it is not needed for anything below, and
the (GR-13) caution against assuming tractability applies).

**What replaces it.** The exchange that does work is not a flow-cost
comparison but an **augmenting-chain** argument, and (GR-85) is exactly the
bookkeeping that makes its ledger telescope. That is *Step G105*.

**Corollary (recorded, used at *Step G108*).** `dist` is even-valued modulo a
constant that depends on `(M)` and not on the configuration, so
`f(p) ≡ f(p′) (mod 2)` for **every** pair of feasible patterns. Every price
computed below is therefore even, which is (GR-67) Cor. 1 in the form this
pass uses it.

---

### Step G105 — (GR-86): the repair-chain theorem — the flip of one odd branch is repaired by a chain, the chain exists exactly when (GR-50) says the flipped pattern is feasible, and its price is **independent of the chain's length**

> **(GR-86)** *(proven for chains traversed as simple paths, with the
> degenerate coincidences machine-checked rather than argued — see the
> confidence table; the completeness clause certified at **6 459 208**
> (admissible `z`, odd branch) pairs of the whole stratum with **0**
> disagreements against the (GR-50) oracle and 0 caps hit; the price bound
> asserted on **every** chain repair — the maximum, not only the cheapest —
> at all of those, at V8, and **CAP-FREE at `n = 30/40/50/60`**; the
> length-freedom tested directly by bucketing the price on chain size
> `|J| = 1..8`; `--chain`, `--big`)*
>
> Let `z` be admissible, `γ ∈ O` an odd branch, `p` the pattern of `z` and
> `p′ = p + χ_γ`.
>
> **(i) Deficiency localization.** `z + χ_{\{γ\}}` fails admissibility at
> **exactly the blocked ends of `γ`** (the ends `v` with `m(v) = γ`). In
> particular a dart-free `γ` needs no repair at all.
>
> **(ii) Repair chains, and completeness.** A **repair chain** adds distinct
> **even** branches `b_1, …, b_r`, each incident to a currently-inadmissible
> hub, until the configuration is admissible; the resulting `J = {γ} ∪
> \{b_j\}` satisfies `J ∩ O = {γ}` and is legal by construction. A repair
> chain exists **iff `p′` is (GR-50)-feasible**.
>
> **(iii) The price ledger.** For any repair chain, (GR-68) gives
> `Δdist = Σ_{v ∈ W(J)} (1 − 2[v ∈ S])`, and each summand is determined by
> the chain's local shape:
>
> | hub | contribution |
> |---|---|
> | a **blocked end of `γ ∈ M`** | `+1` |
> | a **blocked end of `γ ∈ F`** | `0` (chain leaves along `F`) or `−1` (chain leaves along `M`) |
> | an **unblocked end of `γ ∈ F`** | `+1` or `−1` |
> | an interior hub, `F` → `F` | `0` (both `F`-branches lie in `J`) |
> | an interior hub, `F` → `M` | `−1` (the hub is in `S`) |
> | an interior hub, `M` → `F` | `+1` (the hub is not in `S`) |
> | the terminus, reached along `M` | `0` |
> | the terminus, reached along `F` | `+1` or `−1` |
>
> Every interior matching branch therefore contributes `−1 + 1 = 0`, and a
> terminal matching branch contributes `−1`: **the matching branches cancel
> in pairs and the price does not see the chain's length.** Consequently
>
> | case | price |
> |---|---|
> | `γ ∈ M`, dart-free | `0` |
> | `γ ∈ M`, one-end-blocked | `0` or `2` |
> | `γ ∈ M`, **doubly blocked** | `0`, `2` or **`4`** |
> | `γ ∈ F`, any blocking | `−2`, `0` or `2` |
>
> **(iv) The bound.** `Δdist ≤ 2` **unless `γ` is a doubly-blocked matching
> branch**, and then `Δdist ≤ 4`. Both bounds are attained.

*Proof.* (i) Flipping `γ` (say A → B) removes `γ`'s A-darts. At an end `v`,
`#A-darts` drops by 1, so admissibility survives iff it was 2 before. By
(GR-85)(ii) `#A-darts at v = A(v) + m_v`, and it equals 1 exactly when `γ`'s
dart is the lone A-dart at `v`, i.e. exactly when `γ` carries the minority
dart at `v`. ∎

(ii) *Necessity* is immediate: a repair chain produces an admissible `z + χ_J`
whose pattern is `p′`, so `p′` is feasible. *Sufficiency* is the flow
exchange. Read admissible configurations at a fixed pattern as orientations
of the even branches with `l_v ≤ indeg(v) ≤ u_v` ((GR-50)). Let `D` be the
orientation of `z` and `D″` any orientation feasible for `p′`. At every hub
`v` outside `γ`'s ends the bounds are unchanged, and `indeg_D(v) ≤ 2 − o_v`
while `indeg_{D″}(v) ≥ 1 − o_v`, so
`|indeg_{D″}(v) − indeg_D(v)| ≤ 1`: **every hub's excess lies in
`{−1, 0, +1}`**. Orient the edges on which `D` and `D″` differ as in `D″`;
the resulting digraph has in-minus-out degree equal to the excess, so it
decomposes into directed paths and cycles. Discard the cycles (they change no
in-degree) and keep one path terminating at each deficient end of `γ`; the
excess bound makes the paths' *sources* distinct and each source a hub with
slack. Reversing those paths in `D` raises `indeg` by 1 at each deficient
end, lowers it by 1 at each source, and leaves every interior in-degree
fixed — a feasible orientation for `p′`. Reversing a path *is* a repair
chain: after each single reversal the unique inadmissible hub is the path's
next vertex, which is exactly the chain rule. ∎

(iii) By (GR-68), `v` contributes iff **exactly one** of `v`'s two
`F`-branches lies in `J`, with sign `+1` off `S` and `−1` on `S`. Walk the
chain. At a **blocked end `u` of `γ ∈ M`**: `M(u) = γ`, so the only branches
that can raise `A(u)` are `u`'s two `F`-branches, whence `b_1 ∈ F` and
exactly one `F`-branch of `u` lies in `J`; and `A(u) = 0` (both `F`-darts are
B, since `γ`'s dart was the lone A-dart), so `u ∉ S` and the contribution is
`+1`. At a **blocked end `u` of `γ ∈ F`**: `A(u) = 1` (`γ`'s dart is the lone
A one), so `u ∈ S`; if `b_1` is `u`'s other `F`-branch then both `F`-branches
of `u` lie in `J` and `u ∉ W(J)`, contribution `0`; if `b_1 = M(u)` then
exactly one does, contribution `−1`. At an **unblocked end `w` of `γ ∈ F`**
not visited by a chain, exactly one `F`-branch of `w` (namely `γ`) lies in
`J`, contribution `±1`. At an **interior hub `y`** the two `J`-branches are
the arrival and departure branches; if both are `F`-branches then `y ∉ W(J)`;
if one is `M(y)` then exactly one is, so `y ∈ W(J)`. Its `S`-membership is
forced by *why the chain is there*: arriving along an `F`-branch and needing
to continue means the arrival branch carried the lone A-dart at `y`, i.e.
`A(y) = 1` and `y ∈ S`, giving `−1` on an `F → M` step; arriving along
`M(y)` and needing to continue means `A(y) = 0`, i.e. `y ∉ S`, giving `+1` on
an `M → F` step. At the **terminus** the single `J`-branch is `F` (`y ∈ W(J)`,
contribution `±1`) or `M` (`y ∉ W(J)`, contribution `0`). ∎

(iv) Add up. Each chain contributes (its start) + (`0` per interior matching
branch) + (its terminus `≤ +1`), and the *only* `+1` start is a blocked end
of a `γ ∈ M`. So: `γ ∈ M` dart-free has no chain and `W(J) = ∅`, price `0`;
one blocked end gives `≤ 1 + 1 = 2`; two blocked ends give `≤ 2 + 2 = 4`. For
`γ ∈ F` the two ends of `γ` contribute at most `+1` **in total across the
cases** (dart-free: two ends at `±1` and no chain, `≤ 2`; one-end-blocked:
blocked end `≤ 0`, unblocked end `≤ +1`, one terminus `≤ +1`, so `≤ 2`;
doubly blocked: both ends `≤ 0`, two termini `≤ +1` each, so `≤ 2`). ∎

**Two facts the ledger explains, and they are the point.** *First*, the price
is **length-free** because matching branches cancel in pairs — the same
phenomenon (GR-68)(iii) found for a single `F`-path, now for a chain that may
cross between `M` and `F` any number of times. Measured directly: over the
whole stratum the price set is `{−2, 0, 2, 4}` at **every** chain size
`|J| = 1, …, 5` (and `1, …, 8` at V8), with `4` appearing only from `|J| = 3`
on — exactly when a doubly-blocked branch needs two chains. *Second*, the
exceptional case is exceptional for a **structural** reason: a doubly-blocked
matching branch is the unique configuration with **two `+1` starts**. Nothing
about `n` enters anywhere: **(GR-86) is `n`-free by construction**, which is
what route 3 promised and route 1 could not deliver.

**Chain-price invariance is FALSE, and the bound is stronger than that.** An
early reading of a 120-shape sample suggested every repair chain of a given
`(z, γ, M)` has the same price; the exhaustive run **refutes** it — 891 360
instances of the stratum carry two chain repairs of different price. What
holds instead, and is asserted, is that **every** chain repair — not merely
the cheapest — respects the case bound. Recorded because the false reading is
the natural one to form from a small sample.

---

### Step G106 — (GR-87): sub-clause 1 is **PROVEN**, and BALB's far-end side condition **dissolves** — it is not needed, and in its own scope it is exhaustively true at `n_hub ≤ 6` and FALSE from `n_hub = 8`

> **(GR-87)** *(proven, as the `≤ 2` cases of (GR-86); the side-condition
> figures measured by full `2^{|E|}` `z`-cube over the whole stratum and
> seeded `n = 8/10/12`; `--exact`)*
>
> **(i) Dart-free.** `γ ∈ M` dart-free ⟹ price **0**; `γ ∈ F` dart-free ⟹
> price in `{−2, 0, 2}`. *(This is (GR-68)(iv)/(v), re-derived inside the
> model: no repair is needed, so the same orientation stays feasible, and
> `#{A(v) = 2}` drops by at most one per end of `γ`.)*
>
> **(ii) One-end-blocked.** Price in `{0, 2}` (`γ ∈ M`) or `{−2, 0, 2}`
> (`γ ∈ F`) — **`≤ 2` with no side condition on the far end, at any chain
> length.**
>
> **(iii) Doubly blocked in the 2-factor.** `γ ∈ F` doubly blocked ⟹ price
> in `{−2, 0, 2}` — also `≤ 2`. **The doubly-blocked case is only hard when
> the branch lies in `M`.**
>
> **(iv) BALB's side condition, evaluated in its own scope.** The landed
> residual was *"the far-end side condition `m(w_β) ≠ β` for at least one of
> the two available `β`, a short bounded derivation"*. It is **not needed**
> — (ii) holds without it — and taken as a statement it is
> **exhaustively TRUE at `n_hub ≤ 6`** (0 failures of 37 424 one-end-blocked
> majority-side instances at parity-optimal configurations, over the whole
> stratum) and **FALSE from `n_hub = 8`**: 28 of 2932 at `n = 8`, 40 of 3512
> at `n = 10`, 6 of 2746 at `n = 12`. Outside that scope it fails already on
> the stratum (269 248 of 2 498 448 one-end-blocked instances over all
> configurations).

*Proof of (i)–(iii).* Each is a line of (GR-86)(iii)/(iv): (i) has no chain,
(ii) one chain with a `≤ +1` start, (iii) two chains with `≤ 0` starts. ∎

**What this settles, said plainly as the spec asks.** Sub-clause 1 of Clause
A′ is **a theorem**, and it is a *stronger* theorem than the one BALB
projected: it needs neither the two-branch mixed pair nor any far-end
condition, and it covers `γ ∈ F` doubly-blocked as well. The reason the
projected derivation was "short and bounded" but also not the right one is
visible in (iv): the two-branch move can be illegal at **both** available
`β`, and then the *only* repair is a longer chain — which the ledger prices
at the same `≤ 2`. **Sub-clause 1 does not fail at `n_hub = 8`; BALB's
proposed *proof* of it does.**

---

### Step G107 — (GR-88): sub-clause 2 is **REFUTED as posed**, at an exact witness — and two readings of the landed prose are corrected

> **(GR-88)** *(the refutation by explicit, independently re-verified
> witness; the `W`-arithmetic asserted at 290 900 + 1104 + 57 778 + 188 562
> + 366 312 legal (1,2,2) mixed pairs; the optimality-direction control at
> all 84 368 legal flip sets of a 200-shape stratum sub-pool; `--exact`,
> `--adv` (2)/(4))*
>
> **(i) The kill is real.** There are habitat shapes, perfect matchings and
> **parity-optimal** configurations with `|δ| = 2` at which a majority-side
> odd branch is a doubly-blocked matching branch whose one-flip price is
> **exactly 4** — so *"flip that branch"* does **not** discharge Clause A′.
> Named witness (`--exact`, seed 20260822, shape `r8#9`), gated by
> `cflank.cubic_habitat` and re-verified independently: `n_hub = 8`,
> > `specs = [(0,1,2), (6,4,2), (4,7,2), (5,2,2), (0,2,3), (3,7,3), (5,6,3), (4,1,3), (0,3,3), (3,6,2), (7,5,3), (2,1,2)]`,
>
> matching branches `{2, 6, 8, 11}`, `2k = 6`, `d_par(M) = d_adm(M) = 2`
> (per-matching gap **0**, so (b′) itself survives here), pattern bits 15
> (`δ = −2`). At the parity-optimal configuration
> `z = [1,0,0,0,1,1,1,1,0,1,0,0]` (`S = {1, 7}`) the majority-side branch
> `γ = 6 = (5,6,3)` lies in `M` and is blocked at **both** ends, and
> `f(p + χ_γ) = 6 = d_par(M) + 4`. The three other majority-side branches —
> `4, 5, 7`, all in `F`, all dart-free — price `2, 0, 0`.
>
> **(ii) `4` is the ceiling, never 6.** Over 5 782 508 stratum
> (configuration, odd branch) pairs and 10 856 522 more at V8 and seeded
> `n = 8/10/12`, the exact one-flip price of a doubly-blocked matching branch
> reaches `4` (7472 + 128 + 2008 + 2470 + 1952 instances) and **never
> exceeds it**; every other case caps at `2`. A tightened uniform bound
> `≤ 2` is violated **only** in the `M`-doubly-blocked class (`--adv` (2)),
> so the case split of (GR-86) is exact and not vacuous.
>
> **(iii) The landed `W`-arithmetic, corrected.** BALB reads the
> doubly-blocked mixed pair as *"(GR-68) prices it at `≤ 4` unless **both**
> extra endpoints land on deviating hubs"*. In fact `|W(J)| = 4` there with
> the two ends of `γ` **off** `S`, so
> > `Δdist = |W(J)| − 2|W(J) ∩ S| = 4 − 2·#{deviating extra endpoints}`,
>
> and **one** deviating extra endpoint already gives `Δdist = 2`. "Both" is
> the condition for price **0**, not for price `≤ 2`. Measured: of 290 900
> legal (1,2,2) pairs on the stratum, 225 864 have price `≤ 2` and 152 336 of
> those have **exactly one** deviating extra endpoint.
>
> **(iv) Route 1's named input runs the WRONG WAY.** BALB's first route was
> *"a proof that at a parity-optimal configuration the second chain's
> endpoint is forced onto `S`"*, with (GR-68)'s minimality corollary as the
> named input. That corollary says no legal `J` has `Δdist < 0`, i.e.
> **`2|W(J) ∩ S| ≤ |W(J)|` for every legal `J`** — verified at all 84 368
> legal flip sets of a stratum sub-pool, 0 violations. So optimality **caps**
> the number of deviating endpoints at half of `W(J)`; it pushes *against*
> the conclusion route 1 wanted, not toward it. Route 1's stated mechanism
> is therefore **refuted as an implication**, independently of whether its
> conclusion happens to be true.
>
> **(v) Where the case first appears.** At **parity-optimal** configurations
> with `|δ| = 2`, a majority-side doubly-blocked matching branch does **not
> occur anywhere on the `n_hub ≤ 6` stratum** — the majority-side classes
> there are exactly `{F-free: 192 688, F-one: 9048, M-free: 18 476,
> M-one: 28 808}` — and first occurs at **`n_hub = 8`**: 546 majority-side
> instances at parity-optimal configurations in `--exact`'s seeded pool, and
> `--big`'s independently seeded pool prices that class
> `{0: 100, 2: 56, 4: 2, None: 2}`, so price **4** is realized at a
> parity-optimal `|δ| = 2` configuration there too. *Step G108*(iii) proves
> that boundary rather than measuring it.

**Reading.** Sub-clause 2, *as the spec poses it* — the doubly-blocked branch
is repairable at price `≤ 2` — is **FALSE**, with an exact witness and an
exact ceiling. What is *not* false is Clause A′, and the reason is visible in
(i): at the witness three **other** majority-side branches price `≤ 2`. The
residual is therefore not a repair statement about a branch but a
**selection** statement about the set of majority-side branches. That is
*Step G108*.

---

### Step G108 — (GR-89): the descent — (b′) gains its **first proven `n`-free constant**, and the residual is RESHAPED into a selection clause that counting proves on the whole stratum

> **(GR-89)** *(the descent bound proven modulo the named clause (GR-R1); the
> counting bound (iii) proven and asserted as a live guard; the censuses
> EXHAUSTIVE on the stratum — 701 382 unbalanced admissible configurations,
> 96 930 of them parity-optimal — plus V8 and seeded `n = 8/10`; `--desc`)*
>
> **(i) The descent.** Let `z` be admissible and unbalanced with imbalance
> `δ`. Pick a majority-side odd branch whose flip is (GR-50)-feasible, apply
> (GR-86), and repeat. Each step lowers `|δ|` by exactly 2 and raises `dist`
> by at most 4, so after `|δ|/2` steps a **balanced** admissible
> configuration is reached and
> > `d_adm(M) ≤ dist(z) + 4·|δ(z)|/2 = dist(z) + 2|δ(z)|`.
>
> **(ii) The `n`-free constant.** Starting from a parity-optimal `z` and
> using (GR-69) (`|δ| ≤ 2·min(k, ⌊n_hub/4⌋)`),
> > `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`,
>
> and by (GR-67) Cor. 1 the gap is even, so it lies in `{0, 2, …, 12}`. This
> is **the arc's first proven bound of (b′)'s own shape** — a bound on the
> *difference*, uniform in `n`. It needs **one named clause**:
> > **(GR-R1)** at every unbalanced admissible configuration, some
> > majority-side odd branch has a (GR-50)-feasible flip.
>
> (GR-R1) is **measured with 0 failures** at all 701 382 unbalanced stratum
> configurations, at V8, and at 47 628 + 21 204 configurations of seeded
> `n = 8/10` habitat shapes. ~~It is **not proven.**~~ **[PROVEN at *Steps
> G116–G119* (direction GFLIP, 2026-08-25), with `≥ |δ|` feasible majority
> flips — so this bound is now a THEOREM.]**
>
> **(iii) The counting bound — a proof, not a measurement.** Suppose at some
> admissible configuration **every** majority-side odd branch is a
> doubly-blocked **matching** branch. Then
> > `n_hub ≥ 3k + 5|δ|/2`.
>
> *Proof.* Let `A` be the majority side, `a = k + |δ|/2`, `b = k − |δ|/2`.
> The hypothesis gives `O_A ⊆ M`, so `O_A ∩ F = ∅` and, by (GR-85)(iv),
> `T = |H ∩ F| = |F| − |O_B ∩ F| ≥ n − b` (the 2-factor covers every hub, so
> `|F| = n`). Each doubly-blocked `γ ∈ O_A` has `A(u) = A(w) = 0` at both
> ends (*Step G105*, proof of (iii)), and the `2a` ends are pairwise distinct
> because `O_A ⊆ M` and `M` is a matching, so at least `2a` hubs carry
> `A = 0` and `T = Σ_v A(v) ≤ 2(n − 2a)`. Chaining,
> `n − b ≤ 2n − 4a`, i.e. `n ≥ 4a − b = 4(k + |δ|/2) − (k − |δ|/2) =
> 3k + 5|δ|/2`. ∎
>
> **Consequence.** At `|δ| = 2` the bound reads `n_hub ≥ 3k + 5`, i.e.
> `n ≥ 8` at `2k = 2`, `n ≥ 12` at `2k = 4` and `n ≥ 14` at `2k = 6`. Since
> `3k + 5 ≥ 8 > 6` for every `k ≥ 1`, **on the whole `n_hub ≤ 6` stratum some
> majority-side odd branch is not a doubly-blocked matching branch** — which
> *proves* the observation of *Step G107*(v) instead of measuring it, and
> explains why `n_hub = 8` is where the case first appears.
>
> **(iv) The reshaped residual.** Call a majority-side odd branch **cheap**
> if its flip is feasible and it is not a doubly-blocked matching branch. By
> (GR-86) a cheap branch prices `≤ 2`. Then
> > **per-matching (b′) ⟸ (GR-C1) some parity-optimal configuration has
> > `|δ| ≤ 2`, and (GR-C2) at it, a cheap majority-side branch exists.**
>
> (GR-C1) is GPSA's landed first clause — **a theorem at `n_hub ≤ 6`** by
> (GR-69), open beyond. **(GR-C2) is the whole residual**, and it is a
> *selection* statement, not a repair statement. Censused: **0 failures** at
> all **96 930** unbalanced parity-optimal `|δ| = 2` configurations of the
> stratum (exhaustive), 0 at 2114 at `n = 8` and 0 at 371 at `n = 10`. And
> the **greedy** descent — take the cheapest available majority-side branch
> at each step — has **worst single step 2** and **total price `≤ 2`** at
> every one of the 701 382 + 1316 + 47 628 + 21 204 unbalanced configurations
> swept, with **0** stalls. **[Censuses → theorems at *Steps G120–G124*
> (2026-08-25, direction GCHEAP): the every-step form of (GR-C2) is PROVEN
> for `n_hub < 6|δ|` ((GR-101)(ii)), covering every configuration counted
> here.]**
>
> **(v) The sharpest hunt, and it comes up empty under its cap.** By (iii)
> the first possible total failure of (GR-C2) sits at `n_hub = 8`, `2k = 2`, with
> **both** odd branches matching branches and both doubly blocked. Swept
> directly: 46 seeded habitat shapes with exactly two odd branches, 132
> unbalanced parity-optimal configurations at an all-odd-in-`M` matching,
> **0** with both majority branches doubly blocked. **Not found under this
> cap — which is not a proof of nonexistence.**
> **[Corrected and settled at *Steps G120–G124* (2026-08-25, direction
> GCHEAP; the *Step G56*/*G60*/*G118* marker precedent): the inference
> "(iii) proves (GR-C2) below `3k + 5|δ|/2`" is INCOMPLETE as stated —
> (iii)'s hypothesis is every-majority-DBM while a (GR-C2) failure gives
> only every-*feasible*-majority-DBM; the readings coincide only at
> `b = 0`, this cell. (GR-101) re-proves every conclusion with the correct
> feasible-only hypothesis and the LARGER boundary `n = 6|δ|`: this hunt
> cell is provably EMPTY, and the true first failure is `n_hub = 12`,
> realized by (GR-103)'s explicit witness.]**

**The constants, laid out, because the difference between them is the whole
state of (b′).**

| statement | constant | standing |
|---|---|---|
| (b′) as posed | `2` | **OPEN** |
| (b′) with (GR-C1) + (GR-C2) | `2` | reduced to the **selection** clause (GR-C2); (GR-C1) proven at `n ≤ 6` — **(GR-C2) PROVEN at `n ≤ 10` (*Steps G120–G124*), so a full THEOREM on the `n ≤ 6` stratum, theorem modulo (GR-C1) alone at `n = 8, 10`** |
| (b′) with (GR-C1) + (GR-R1) | `4` | **PROVEN modulo (GR-C1) alone** ((GR-86) + one descent step; (GR-R1) PROVEN at *Steps G116–G119*) — a full theorem on the `n_hub ≤ 6` stratum |
| (b′) with (GR-R1) alone | `4·min(k, ⌊n/4⌋) ≤ 12` | **PROVEN**, `n`-free ((GR-R1) PROVEN at *Steps G116–G119*) |
| (b′) with (GR-R1) + (GR-C2) at every step | `2·min(k, ⌊n/4⌋) ≤ 6` | **the every-step form is PROVEN for `n < 6|δ|` and REFUTED from `n = 12` (*Steps G120–G124*)**: this row is a THEOREM outright at `n ≤ 10`, OPEN beyond via the successor **(GR-104)(i)** (the price form — since *Steps G125–G129* (GPRICE) a theorem at `2k = 2`, every `n`, modulo the balance law (GR-108) — **(GR-108) since REFUTED, the surviving conditional the half-witness clause (*Steps G135–G139*)**); the interpolation (GR-104)(ii) improves the chain below `n = 12·(δ_M/2)` |

**Why the naive exchange had to be anchored, recorded as the route-3
post-mortem.** The obvious `n`-free form of route 3 is *"`f` is 2-Lipschitz
under a single odd-branch flip"*. That is **REFUTED**, at `n_hub = 4`: at the
habitat shape `[(0,1,5), (0,2,4), (0,3,2), (1,2,2), (1,3,2), (2,3,3)]` with
matching branches `{0, 5}`, `f` jumps `0 → 4` across one flip (`--adv` (3)).
The jump direction is **balanced-optimal → unbalanced**, i.e. exactly the
direction the descent never travels; (GR-86) is the correct one-sided
anchored replacement, and it is anchored at an *arbitrary* admissible
configuration rather than at optimality, which is why it iterates.

---

### Step G109 — (GR-90): where this leaves (b′), the residual, the caps and the hand-off

> **(GR-90)** *(the status statement; no new mathematics)* **(b′) is a HIT of
> the third kind the spec names — a proof of a different constant with the
> exact boundary named — and it is NOT proven at the constant 2.** What moved:
>
> - **sub-clause 1 is PROVEN** ((GR-87)), in a stronger form than projected
>   (no far-end side condition, any chain length, `γ ∈ F` doubly-blocked
>   included), and BALB's proposed derivation of it is **refuted in its own
>   scope with an exact boundary** — exhaustively true at `n_hub ≤ 6`, false
>   from `n_hub = 8`;
> - **sub-clause 2 is REFUTED as posed** ((GR-88)), by a named,
>   independently re-verified `n_hub = 8` witness at price exactly **4**,
>   with `4` the exact ceiling; two readings of the landed prose are
>   corrected (the `W`-arithmetic needs **one** deviating endpoint, not two;
>   route 1's named input is directionally wrong);
> - **route 3's instrument is corrected** ((GR-85)): the objective is a
>   parity count, so min-cost flow is the wrong machinery on the cost side;
>   the working exchange is the **repair chain** ((GR-86)), which is `n`-free
>   by construction and cap-free in practice to `n_hub = 60`;
> - **(b′) acquires a proven `n`-free constant** ((GR-89)):
>   `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, modulo the single named
>   clause (GR-R1);
> - **the residual is reshaped**: from *repair the doubly-blocked branch*
>   (now false) to *(GR-C2), a cheap majority-side branch exists* — with
>   (GR-89)(iii)'s counting bound **proving** it on the whole `n_hub ≤ 6`
>   stratum and naming its first possible failure exactly.

**The residual, named exactly, in the order a successor should take it.**

1. **(GR-C2), the selection clause** — *at some parity-optimal configuration
   with `|δ| ≤ 2`, some majority-side odd branch is feasible-flippable and
   not a doubly-blocked matching branch.* This is now the whole gap between
   the proven constant 4 and (b′)'s 2. Two inputs are ready: (GR-89)(iii)
   proves it below `n_hub = 3k + 5|δ|/2`, and its first possible failure is
   pinned to `n_hub = 8`, `2k = 2`, both odd branches doubly-blocked matching
   branches — a **two-branch** condition, small enough for a proof attempt.
   **[Settled at *Steps G120–G124* (2026-08-25, direction GCHEAP): PROVEN
   at `n ≤ 10` in the every-step form ((GR-101)(ii)); the per-configuration
   form REFUTED from `n_hub = 12` by an explicit witness ((GR-103)), the
   boundary `n = 6|δ|` exact in both directions — the "(iii) proves it" /
   "first failure `n = 8`" clauses above carry *Step G108*(v)'s correction
   marker; the as-posed existential is proven at `n ≤ 10` and OPEN beyond,
   with successor **(GR-104)(i)**, the price form.]**
2. **(GR-R1)** — *at every unbalanced admissible configuration some
   majority-side odd branch has a feasible flip.* **PROVEN at *Steps
   G116–G119* (direction GFLIP, 2026-08-25)** — via the demand form and the
   selection theorem (GR-99), not via (GR-52)/(GR-53), which turned out to be
   a sufficient-condition calculus that cannot see merely-feasible
   hypotheses. **[Gloss corrected at *Step G118*: flipping `γ` A → B can
   create B-side demand of either kind — a new B-monochromatic-pair hub or a
   B-monochromatic **triple** at a `q_v = 3` end, and the triple case is the
   stratum's dominant blocking mechanism.]** (GR-89)(ii) is now a theorem.
3. **(GR-C1) past the stratum** — GPSA's first clause; unchanged by this pass,
   and (GR-69) is its exact `n ≤ 6` boundary.

**Hand-off — the route ledger** (statuses as this landing leaves them).
**Entry 5 — PROVEN, unchanged** ((GR-54); consumed, untouched). **Entry 1 —
unchanged; (a′) not attempted**, and **(GR-64)(R2) / input (Y) untouched**
(GCOLL's target this wave). **(b′) — price half PROVEN ((GR-68)),
availability half now: sub-clause 1 PROVEN, sub-clause 2 REFUTED as posed,
constant 4 (and `n`-free `≤ 12`) PROVEN modulo (GR-R1), constant 2 OPEN with
(GR-C2) as its exact residual.** (c) AA-glue realizability and (d′) untouched.

**One (Y)-adjacent by-product, reported and NOT developed** (the spec's
bar). (GR-85)(i)/(iv) is a statement about `dist(·, M)` alone, so it applies
verbatim inside `d_fg(M)`: at a fixed odd pattern, **full-goodness is a
constraint on the same `(A(v))_v` vector** that carries `dist`, whereas
(GR-62) refuted its being a function of the (GR-50) *degree* data. Those are
compatible — `(A(v))_v` is strictly finer than the degree data, since it
records *which* `F`-darts are A and not merely how many — and the honest
reading is that **(GR-85) supplies the finer coordinate YLOC's (GR-65) fit
identity said an instrument must control.** Nothing is computed here: the
pass is rank-free. Offered to a (Y) successor as a coordinate, not a result.

**Independent corroboration of two landed BALB figures, as a by-product.**
This pass computes `d_par(M)` and `d_adm(M)` from the full `2^{|E|}`
`z`-cube — a construction independent of `gpsa.parity_census` /
`gadm.dp_pref` — and reproduces (GR-70)(ii) exactly: per-matching gaps
`{0: 23 444, 2: 495}` over all 23 939 stratum (shape, matching) pairs, and
**96 930** unbalanced parity-optimal configurations. Two independent
constructions, identical figures.

**Riders, verbatim.** Everything is at **`Λ = ∅`**, **`D = 0`**, and
**modulo (GR-4′)** where a closure chain is concerned; the **`Λ ≠ ∅`
closed-form analogue** and the **`D > 0` lift** stay **unswept**. **None of
this closes (GR-15)**, and no `g`-flank is exhibited: the pass is rank-free,
computes no rank anywhere, and makes **no claim about class uniformity**. The
**shift-metric layer is UNBOUNDED** ((GR-43), `d_par = d_adm = d_fg = m`
exactly at the necklaces) — so every statement here is a bound on the
**difference**, never on `d_adm`, and every necklace figure carries that
qualifier. (GR-85) uses cubicity three times (two `F`-branches per hub, `M`
perfect, `d_v = 3 − q_v`), so a `D > 0` lift must redo it.

**Caps, disclosed in full — an exhausted cap is not a proof of
nonexistence.**

1. **(GR-85)'s converse direction is capped** at the first **120 shapes per
   leg** (it enumerates `2^{|O|}·2^{|H ∩ F|}` assignments per (shape,
   matching) pair); the **forward** direction is uncapped over the whole
   stratum.
2. **The `n = 30/40/50/60` legs are samples, not censuses**: one constructed
   matching per shape (`gadm.complete_matching`), 30 random-walk
   configurations per family per rung, seed printed. They are **cap-free in
   the sense that matters** — no `2^{dim}` table and no `d_par` — which is
   exactly why they reach where BALB's `m = 6` limit stopped: **(GR-86) is a
   relative statement.** **(b′) itself still needs `d_par(M)`, the
   exponential object, and is still capped at `m = 6`; GBAL's `n = 40..60`
   reach does not transfer to it, and this pass does not claim it does.**
3. **The `n = 8/10/12` shape pools are seeded samples** (`--big` prints
   43 / 17 / 7 shapes; `--exact`'s pools are larger, drawn from the same
   seeded sampler with the seed printed);
   **only the `n_hub ≤ 6` stratum is exhaustive.** One `n = 12` shape had its
   perfect-matching list capped at 12; `--desc`'s `n = 10` leg subsamples 400
   configurations per shape and 6 matchings (36 caps hit, reported in-line).
4. **The targeted (GR-C2)-failure hunt of *Step G108*(v) found nothing under a
   46-shape / 132-configuration cap.** That is **not** evidence that (GR-C2)
   holds at `n_hub = 8`.
5. **The chain search has a node cap** (40 000 breadth-first / 200 000
   depth-first states); **0 caps were hit** anywhere, including at
   `n_hub = 60`, and the count is printed per leg.

---

### Verification (Steps G104–G109)

`notes/scripts/w4/gflow.py` (**new with this pass**; imports — all read-only
— `balb` (`dev_set`, `dist_anchored`, `price_pred`, `rand_habitat`,
`stratum_cases`, `v8_specs`, `w_set`), `gadm`
(`complete_matching`, `nko_specs`), `gbal` (`dart_col`, `feasible_at`,
`flip_legal`, `map_to_z`, `odd_idx`, `z_admissible`, `z_pattern`,
`z_to_map`), `gdesc` (`imb_of`, `majority_of`), `gdev` (`habitat_by_lemma`,
`nk_specs`), `gorient` (`m_of_matching`, `perfect_matchings`), `gpsa`
(`branches_at`, `nk55_specs`, `nkp_specs`, `pattern_of`)). **Rank-free**:
`gexist.fully_good_rank` is never imported or called and no `d_fg` claim is
made anywhere. Local devices, none shadowing a §1 primitive (checked against
the README index and the *Divergences* table): `nonmatch_at`/`a_of`/`m_ind`/
`mconstraints`/`t_of` ((GR-85)), `bad_hubs` (the inadmissibility witness
set), `block_ends_at`/`case_of` ((GR-86)'s six cases),
`chain_repairs`/`chain_first` ((GR-86)'s repair chains, depth-first-all and
breadth-first-one), `adm_cube` (the exhaustive `2^{|E|}` enumeration),
`f_layers` (exact `f(p)` and `d_par(M)`), `walk_adm` (the large-`n`
admissible-configuration walk), `seeds_at`/`feas_flip` ((GR-50) wrappers),
`necklaces` (the odd-rich families behind `gdev.habitat_by_lemma` — the
**polynomial** habitat criterion, since `cflank.cubic_habitat`'s `2^{n_hub}`
cut enumeration is out of reach at `n ≥ 20`), `seeded_shapes`, `hist`,
`hist2`. Exact integers over GF(2) throughout; no floating point; rngs seeded
per mode with the seed printed; no `set` printed. **No pool is new**: the
`Λ = ∅`, `D = 0` stratum is `gcap.pool_specs` behind `cflank.cubic_habitat`
via `gbal.pool_cases`/`balb.stratum_cases`, swept **EXHAUSTIVELY**; V8, the
necklaces and `rand_habitat` are BALB's / GDEV's / GADM's constructions
reused read-only.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --model     # ~47 s  (GR-85) both directions: 2611058 forward triples + 1035572 converse assignments
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --chain     # ~237 s (GR-86): 6470912 (z, gamma) pairs, chain-vs-oracle completeness, price by case AND by |J|
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --exact     # ~102 s (GR-87)/(GR-88): exact f(p) by full z-cube, stratum + V8 + seeded n = 8/10/12
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --desc      # ~73 s  (GR-89): (GR-R1), the greedy descent, the (GR-C2) census, the counting bound, the targeted hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --big       # ~33 s  cap-free (GR-86) certificates at n = 30/40/50/60 + the seeded exact legs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --adv       # ~11 s  five F13 falsification controls
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflow.py --validate  # ~471 s all six in one process (inside the 600 s budget)
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-85)(i) `dist = #{A(v) = 1}` | `--model` | `{v : A(v) = 1}` asserted **set-equal** to `dev_set`, and its size equal to `balb.dist_anchored`, at all 2 088 924 stratum triples (plus V8 / `n = 8/10`); the doctored variant (read `A` off the matching dart) must disagree — `--adv` (1), 10 441 of 11 888 |
| (GR-85)(ii) the per-hub forcings | `--model` | `A + m ∈ {1,2}`, `A = 0 ⟹ m = 1`, `A = 2 ⟹ m = 0` asserted per hub at every triple |
| (GR-85)(iii) the three local conditions are **exactly** admissibility | `--model` | **both directions**: every admissible `z` asserted to violate none; and every `(p, even-F orientation)` assignment asserted `ok == realized`, i.e. the conditions hold **iff** the assignment is realized by an admissible `z` (1 035 572 assignments; converse cap disclosed) |
| (GR-85)(iv) the `T`-identity and `dist = T − 2n_2` | `--model` | `T` computed from `(p, M)` alone asserted `== Σ_v A(v)`, and `dist == T − 2 n_2`, at every triple |
| (GR-85) parity-law corollary | `--model` | `dist % 2 == T % 2 == #{even ∉ M} % 2` at every triple |
| (GR-85)'s **reading** (not a flow cost) | — | **not driver-testable** — it is a statement about which machinery applies. The *positive* half (the objective is `#{A(v) odd}`) is (i)+(iv), asserted; the *negative* half is the observation that `0,1,0` is not convex, plus `--adv` (3)'s refutation of the naive Lipschitz law that a convex-cost exchange would give |
| (GR-86)(i) deficiency localization | `--chain` | implicit in the case key: `case_of` computes the blocked ends and the chain search starts exactly there; the six-class price tables are per-key |
| (GR-86)(ii) completeness | `--chain` | `(len(sols) > 0) == feasible_at(p + χ_γ)` asserted at all 6 459 208 stratum pairs and 11 704 at V8: **0 disagreements**, 0 caps |
| (GR-86)(iii) the price ledger | `--chain` | for **every** chain repair: `flip_legal`, `z_admissible`, `z_pattern == p ^ (1 << j)`, and the recomputed `Δdist` asserted `== price_pred(w_set, S)` — i.e. (GR-68) re-derived on each chain |
| (GR-86)(iii) **price independent of length** | `--chain` | the price bucketed by chain size `\|J\|`: the value set is `{−2,0,2,4}` at every `\|J\| = 1..5` (stratum) and `1..8` (V8); `4` appears only from `\|J\| = 3` |
| (GR-86)(iv) the case bound | `--chain`, `--exact`, `--big` | `assert min(prices) <= bound[key]` **and** `assert max(prices) <= bound[key]` per instance (so the claim is about every chain, not the cheapest); and the **exact** `f(p+χ_γ) − dist` checked against the same bound at 5 782 508 + 11 704 + 995 310 + 3 040 888 + 6 808 620 pairs — 0 violations |
| (GR-86) chain-price invariance | `--chain` | **REFUTED and reported**, not asserted: 891 360 stratum instances carry two chain repairs of different price |
| (GR-87)(i)–(iii) sub-clause 1 | `--exact` | the exact price histograms per case: `M-free` maxes at `0`, `F-free`/`F-one`/`F-double`/`M-one` at `2`, over every leg |
| (GR-87)(iv) BALB's side condition | `--exact` | counted **in BALB's own scope** (majority-side, at a parity-optimal configuration): 0/37 424 stratum, 28/2932 at `n = 8`, 40/3512 at `n = 10`, 6/2746 at `n = 12`; and separately over all configurations |
| (GR-88)(i) the price-4 witness | `--exact` | the witness is selected under `opt and \|δ\| == 2 and γ ∈ majority`, smallest `n` kept, and printed with its full `specs`, matching, pattern and `f` values; re-verified independently outside the driver (habitat gate, perfect-matching check, `d_par`/`d_adm` recomputation, the three cheap sibling branches) |
| (GR-88)(ii) `4` is the ceiling | `--chain`, `--exact` | `assert pr <= 4` on `M-double` everywhere; `--adv` (2) tightens the bound to `2` uniformly and reports that it fires **only** on `M-double` (100 instances) |
| (GR-88)(iii) the `W`-arithmetic | `--exact` | `assert price_pred(W, S) == len(W) − 2*len(W & S)` at all 290 900 + 1104 + 57 778 + 188 562 + 366 312 legal (1,2,2) pairs, with the `(\|W\|, \|W ∩ S\|, price)` triples counted so the "exactly one endpoint" class is exhibited, not asserted |
| (GR-88)(iv) route 1's direction | `--adv` (4) | `assert 2*len(W & S) <= len(W)` over **all `2^{\|E\|}`** legal flip sets at every parity-optimal configuration of a 200-shape sub-pool: 84 368 instances, 0 violations |
| (GR-88)(v) the `n_hub = 8` boundary | `--exact` | the majority-side class census at parity-optimal configurations, printed per leg: no `M-double` on the stratum, 546 at `n = 8` |
| (GR-89)(i)/(ii) the descent bound | `--desc` | the descent is **executed**, not argued: each step's chain repair is re-checked by `z_admissible`, the imbalance is asserted to reach 0, and the total and worst-step prices are histogrammed (total `≤ 2`, worst step `≤ 2`, 0 stalls) |
| (GR-89)(ii) clause (GR-R1) | `--desc` | `feasible_at` run on every majority-side flip at every unbalanced configuration; the count with **none** feasible is printed: 0 of 701 382 + 1316 + 47 628 + 21 204 |
| (GR-89)(iii) the counting bound | `--desc` | `assert n >= 3k + 5\|δ\|/2` fires as a **live guard** whenever the all-doubly-blocked-matching hypothesis is detected; it never triggered a failure, and the hypothesis' own frequency is reported by (v) |
| (GR-89)(iv) the (GR-C2) census | `--desc` | 96 930 stratum + 2114 + 371 parity-optimal `\|δ\| = 2` configurations audited for a cheap majority branch: 0 failures |
| (GR-89)(v) the targeted hunt | `--desc` | the `n = 8`, `2k = 2`, all-odd-in-`M` sweep, with the shape/configuration counts printed and the verdict phrased "**NOT FOUND under this cap**" |
| the `n = 30..60` legs are cap-free for (GR-86) | `--big` | no `dp_pref`, no `d_par`, no `z`-cube: `feasible_at` seeds, `walk_adm` samples, `chain_first` repairs, and the recomputed `Δdist` is asserted `== price_pred` and `<= bound[key]`; node caps printed (0) |
| the `n = 30..60` legs are SAMPLES | `--big` | one constructed matching per shape and 30 walks per family, both stated in the printed line |
| (GR-70)(ii) reproduced independently | `--exact` | the per-matching gap histogram `{0: 23 444, 2: 495}` and the 96 930 optimal-configuration count recomputed from the `z`-cube, an independent construction |
| (a′) / `d_fg` / input (Y) / (GR-64)(R2) | — | **not attempted**; no mode computes a rank. The (Y)-adjacent remark is a *coordinate* observation, with no figure attached |
| (GR-15) / class uniformity | — | untouched; not driver-testable and not claimed |

**Determinism.** `--validate` was run at `PYTHONHASHSEED` 0 and 999 (both
exit 0, ≈471 s): the outputs are **byte-identical except for the `[Ns]`
wall-clock annotations**, which are inherently non-deterministic.

**Scratch probes (README's standing rule).** Fifteen exploratory probes
were written during the derivation (the pool survey, the `A(v)`-model check,
the naive-Lipschitz sweep, the blocking-class censuses at `n ≤ 6/8/10`, the
exact-price sweeps, the chain-DFS-vs-oracle check, the descent probe, three
large-`n` attempts of which two were abandoned for cost, and the witness
re-verification). **None is retained** — each became a mode of the committed
driver, and every figure quoted above is produced by `gflow.py`. The one
exception is stated as such: the **independent re-verification of the
(GR-88)(i) witness** was run as a standalone script outside the driver and
is **not retained**; its content is reproduced by `--exact`'s own printed
line plus the habitat gate the shape pool already applies, and its extra
checks (the sibling branches' prices) are recorded here as figures with the
driver's `--exact` price table as their in-driver counterpart.

---

### Confidence verdict (Steps G104–G109)

| | claim | standing |
|---|---|---|
| **(GR-85)(i)/(ii)** | `dist = #{v : A(v) = 1}`; the per-hub forcings | **proven** (two-line proof off (GR-67)(i)/(GR-49); asserted at 2 611 058 triples, with a doctored-model control) |
| **(GR-85)(iii)** | the three local conditions are **exactly** admissibility | **proven** (the matching-branch tie against (ii); certified in **both** directions, converse cap disclosed) |
| **(GR-85)(iv)** | the `T`-identity; `dist = T − 2n_2`; the parity law re-derived | **proven** (asserted at every triple) |
| **(GR-85)** reading | route 3's "min-cost flow, hence polynomial" is the **wrong instrument on the cost side** | **proven as stated** — the objective *is* `#{A(v) odd}`, which is not convex in the degree data. What is **OPEN** is whether the coupled problem is polynomial by other means; the unconstrained (even-`F`-only) version is a linear-time DP |
| **(GR-86)(ii)** | a chain repair exists **iff** the flipped pattern is (GR-50)-feasible | **proven** (the flow-decomposition argument, with the excess-in-`{−1,0,1}` step explicit); 0 disagreements at 6 470 912 pairs |
| **(GR-86)(iii)/(iv)** | the price ledger; the six-case bound; length-freedom | **proven-informally** — the ledger is a complete case analysis for a chain traversed as a **simple path**; the **degenerate coincidences** (a chain revisiting a hub, or the two chains of a doubly-blocked branch meeting) are **machine-checked, not argued**, and that is the one named gap in this step. The bound is asserted on **every** chain repair (max, not min) at 6 470 912 stratum/V8 pairs and **cap-free** at `n = 30/40/50/60` |
| **(GR-86)** invariance | all chain repairs of one instance share a price | **REFUTED** (891 360 stratum counterexamples); recorded because a 120-shape sample suggested it |
| **(GR-87)** | **sub-clause 1 of Clause A′** — the one-end-blocked (and `γ ∈ F` doubly-blocked, and dart-free) cases price `≤ 2`, at any chain length, with no side condition | **PROVEN** (as the `≤ 2` cases of (GR-86)) — *a theorem the arc did not have*, and stronger than the one BALB projected |
| **(GR-87)(iv)** | BALB's far-end side condition | **not needed**, and **refuted with an exact boundary in its own scope**: exhaustively true at `n_hub ≤ 6` (0/37 424), false from `n_hub = 8` (28/2932) |
| **(GR-88)(i)/(ii)** | **sub-clause 2 as posed** | **REFUTED by witness** — a named `n_hub = 8` habitat shape, matching and parity-optimal `\|δ\| = 2` configuration where a doubly-blocked matching branch prices **exactly 4**; `4` is the exact ceiling (never 6) |
| **(GR-88)(iii)** | the (1,2,2) price is `\|W\| − 2\|W ∩ S\|`, so **one** deviating extra endpoint gives `≤ 2` | **proven** (arithmetic) and asserted at 904 656 legal instances — a correction of the landed prose's "both" |
| **(GR-88)(iv)** | route 1's named input is **directionally wrong** | **proven** ((GR-68) minimality gives `2\|W ∩ S\| ≤ \|W\|`); asserted over all `2^{\|E\|}` legal flip sets at 84 368 instances |
| **(GR-88)(v)** | the case first occurs at `n_hub = 8` | **proven** by (GR-89)(iii) below `n_hub = 3k + 5\|δ\|/2`, and **measured**: 546 majority-side instances at `n = 8`, priced `{0: 100, 2: 56, 4: 2, None: 2}` on `--big`'s independent pool |
| **(GR-89)(i)/(ii)** | `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, uniform in `n` | **THEOREM** — the one named gap was exactly **(GR-R1)**, **PROVEN at *Steps G116–G119*** (GFLIP, 2026-08-25); the arc's **first proven `n`-free bound of (b′)'s shape**, residual confidence qualifier now (GR-86)(iii)/(iv)'s own landed status |
| **(GR-89)(iii)** | the counting bound `n_hub ≥ 3k + 5\|δ\|/2` for a total failure | **proven** (a five-line count off (GR-85)(iv)); a live guard in the driver |
| **(GR-89)(iv)** | **(GR-C2)**, the selection clause | **settled per-configuration in both directions at *Steps G120–G124*** (2026-08-25, GCHEAP): every-step form **PROVEN for `n < 6|δ|`** — all `n ≤ 10` at `|δ| = 2`, the censuses now theorems — and **REFUTED from `n_hub = 12`** by witness; as-posed proven `n ≤ 10`, OPEN beyond; successor **(GR-104)(i)**. The "proven by (iii)" clause here was the incomplete inference *Step G108*(v)'s marker corrects |
| **(GR-R1)** | some majority-side flip is always feasible | **PROVEN at *Steps G116–G119*** (GFLIP, 2026-08-25; the selection theorem (GR-99), with `≥ |δ|` feasible majority flips — (GR-52)/(GR-53) turned out not to be the instruments) |
| **(b′)** | `d_adm − d_par ≤ 2` | **a HIT of the third kind — a different constant with the exact boundary named.** Constant `4` **PROVEN modulo (GR-C1)** and `n`-free `≤ 12` **PROVEN outright** ((GR-R1) closed at *Steps G116–G119*); constant `2` **a THEOREM on the whole `n ≤ 6` stratum and modulo (GR-C1) alone at `n = 8, 10`** (*Steps G120–G124*), **OPEN from `n = 12`**, residual **(GR-104)(i)** (the price form, superseding (GR-C2) as the certificate — since *Steps G125–G129* (GPRICE) a theorem at `2k = 2`, every `n`, modulo the balance law (GR-108) alone, and since *Steps G135–G139* (GXESC) **⟺ the gap-2 law, (GR-108) REFUTED, the surviving conditional the half-witness clause**, its `2k ∈ {4, 6}` `O ⊄ M` corner OPEN); sub-clause 1 proven, sub-clause 2 refuted as posed |
| (GR-67)/(GR-68)/(GR-69)/(GR-70) | BALB's chain | **untouched and consumed**; (GR-70)(ii)'s figures **independently reproduced** from the `z`-cube; (GR-68) re-derived once inside the model as a consistency check, never replaced |
| (GR-49)–(GR-54) | the z-form and the balance theorem | **untouched and consumed**; (GR-50)'s decision is *corroborated* at the one-flip level by the chain search's 0 disagreements |
| **(a′)** / **input (Y)** / **(GR-64)(R2)** | | **OPEN — not attempted.** One coordinate observation reported, no figure, no rank |
| **(GR-15)** | | **OPEN — unchanged in both directions.** No flank; no rank computed anywhere; class uniformity untouched |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as TCOL's through BALB's: exact GF(2) / integer combinatorics on constructed
hub multigraphs, never `PencilNondegFeasible G`; no rank is computed
anywhere; no σ-fixed witness is read as generic (§(K-clos) (AC-9)), and the
only sampler draws a **graph**, not a placement.

### What would change this (Steps G104–G109)

*(i)* **A proof of (GR-R1)** upgrades (GR-89)(ii) from *modulo a named clause*
to a theorem, and with it (b′) at the constant `4·min(k, ⌊n/4⌋)`. It is a
(GR-51)-shaped statement about which side flipping `γ` A → B can spoil, so
(GR-52)'s parity contradiction and (GR-53)'s exhaustion over maximal
constraint structures are the named instruments. **This is the cheapest
remaining step in the whole (b′) line.** *(ii)* **A proof of (GR-C2)** closes
(b′) at the constant `2` on the strength of (GR-C1); (GR-89)(iii) already proves
it below `n_hub = 3k + 5|δ|/2` and pins its first possible failure to a
**two-branch** configuration at `n_hub = 8`, `2k = 2`. *(iii)* **A
counterexample to (GR-C2)** — a parity-optimal `|δ| = 2` configuration whose
*every* feasible majority-side branch is a doubly-blocked matching branch —
does **not** refute (b′) by itself (a multi-odd-branch legal move may still
be cheap), but it kills the descent route and is the sharpest search target
this pass leaves; by (GR-89)(iii) it must satisfy `n_hub ≥ 3k + 5`, and the
`n = 8`, `2k = 2` cell was swept and came up empty **under a small cap**.
*(iv)* **A per-matching gap of 4** refutes (b′) outright; by (GR-67) Cor. 1
that is still the only shape a per-matching counterexample can take, and
(GR-89)(ii) now bounds it: a counterexample must live at `n_hub ≥ 8` with
`min(k, ⌊n/4⌋) ≥ 2` — the bound `4·min(k, ⌊n/4⌋)` is `4` at `n_hub ≤ 6`,
which (modulo (GR-R1)) makes a gap-4 refutation **impossible on the stratum for
arithmetic reasons and only barely possible at `n_hub = 8`**. *(v)* **A
polynomial algorithm (or an NP-hardness proof) for `f(p)`** settles the
question (GR-85)'s reading leaves open, and either answer is worth having:
polynomial would revive route 3 in a corrected form, hardness would explain
why every closed-form attempt on this layer has failed. *(vi)* **A `d_fg`
claim**: none is made, so nothing here touches (a′), input (Y), (GR-64)(R2),
(GR-15) or the `g`-flank question in either direction. *(vii)* **The
`Λ ≠ ∅` or `D > 0` analogue.** (GR-85) uses cubicity three times and `M`
being *perfect* once; (GR-86)'s ledger uses "each hub has exactly two
`F`-branches" throughout, and a shape with more than 6 odd branches falls
outside (GR-53)'s exhaustion, on which (GR-54) — and hence the non-vacuity of
every gap statement here — depends. **Both strata stay unswept by standing
rider.**

**TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator
re-runs it.**

- **(E1) NO.** No g-flank. The pass is **rank-free** and computes no rank, so
  clauses (i)–(iv) cannot fire on it. Clause **(v)** is the one it could
  touch, and it fires on nothing: `--exact` asserts `d_adm(M) ≠ ∞` — literally
  `assert dadm is not None` — at **every** (shape, matching) pair of the whole
  stratum and of V8 and of the seeded `n = 8/10/12` legs, so no shape with
  `d_adm = ∞` exists anywhere swept. (GBAL's (GR-54) already makes clause (v)
  provably unfirable at `Λ = ∅`, `D = 0`; this pass is consistent with that
  and adds an independent `z`-cube witness of it.) A finite-but-large `d_adm`
  fires nothing (clause (iii)).
- **(E2) NO.** Entry 5 is **PROVEN** ((GR-54)) and this pass consumes it
  untouched, so E2's premise — entry 5 refuted or unprovable-as-posed — is
  false. Nothing here is a demotion witness for entry 5 either: the
  **route** demoted by this pass is BALB's sub-clause-2 repair route for
  **(b′)**, not anything on entry 5, and it is demoted **with successors
  named** ((GR-C2), (GR-R1)), which is the retained carve-out.
- **(E3) ARMED, DOES NOT FIRE, and this direction does not fire it.** E3
  fires only on a HIT completing **entry 1** — i.e. **(a′)**. This pass does
  not attempt (a′), computes no rank, and makes no `d_fg` claim, so entry 1 is
  untouched and E3 stays exactly as GBAL's entry-5 HIT left it. **Firing is a
  coordinator action.** The HIT this pass does carry is on **(b′)**, which is
  not entry 1 and does not arm or fire anything.
- **The otherwise-clause routing this landing names.** BALB's list has *"(b′)
  refuted (a growing balance gap) → the balance-layer characterization at that
  family"* — **that branch does NOT apply**: (b′) is not refuted, it gained a
  proven constant. The applicable branch is the second one, *"closed only
  under an extra hypothesis → that hypothesis as its own statement, with the
  residual configurations named"*, and the hypothesis is **(GR-R1)** with **(GR-C2)**
  the residual. So the twenty-seventh-or-later dispatch this landing names is
  **(GR-R1) as its own statement**, with (GR-C2) as the follow-on and the
  `n_hub = 8`, `2k = 2` cell as its adversarial control.

---

---

### Steps G110–G115 (2026-08-19, direction GCOLL) — **(GR-64)(R2) is REFUTED by witness**: **(GR-91)** rewrites the collision statistic in *slack* form — `coll_M(S) = z(S) − s_M(S)` with `s_M(S)` **always even**, so a positive (GR-64) term is exactly a **zero-slack** chunk and equals that chunk's *demand* `r(S) = 6 − z(S) − exc(S) ∈ {1,2}`, collapsing (GR-64)(iv)'s two ceiling values into one condition; **(GR-92)** classifies the demand exhaustively (six `(z, exc)` profiles, twelve with the chord/exit refinement of (GR-32)(ii), `r ≤ 2` proven again in one line, and a two-cut normal form); **(GR-93)** is the instrument: a violated chunk's hub set is a **union of cycles of the 2-factor `F = E ∖ M`**, so violation detection at a fixed `M` is a `2^{c(F)}` search with **no chunk scan** — exact against the landed `2^M` ground truth at all 24 671 (shape, matching) pairs; **(GR-94)** turns that into **two PROVEN sufficient conditions** for `B(M) = 0` (a Hamiltonian one, self-contained; a cyclic-edge-connectivity one, on Plesník 1972) which between them cover the **whole 4924-shape inventory** and **39 687 of the 39 689** `n_hub = 8` habitat shapes — so on those strata (R2) is a **theorem**, not a measurement; **(GR-95) REFUTES (R2) in general** — **180 of the Petersen graph's 36 860 habitat length assignments carry `min_M B(M) = 1`**, each certified habitat by the canonical oracle `gridcol.class_shape` and re-verified through the landed `2^M` scan, with exactly **two** mechanisms and a local criterion asserted at all 221 160 (Petersen shape, matching) pairs — so **(GR-64) is a genuine floor on `d_fg`** and the collision mechanism **can** obstruct; **(GR-96)** delivers **(GR-64)(R1)**, extending the sweep from `n_hub ≤ 6` + four named shapes to `n_hub = 8` (**complete**, 39 689 shapes), `n_hub = 10` (the Petersen graph, complete for that graph), W5 (`E = 24`) and the **eight** odd-rich necklaces (`n_hub = 30, 40`), **uncapped on the chunk side throughout**. **(a′) is NOT refuted:** the E1(iv)/E2 detector reports **0** — `d_adm ∈ {2, 3}` against `min_M B = 1` at every witness — and `d_fg = d_adm` at all 180 witnesses, so (a′) *holds* there (new territory, reported as a by-product). **Input (Y) stays OPEN, (a′) stays OPEN and still carries NO bar, E3 (ARMED by GBAL) does NOT fire; (GR-15) OPEN, and the only gap-map status move is (GR-64)(R2) → REFUTED, (GR-64)(R1) → DELIVERED.**

**Notation** (on top of *Steps G74–G79* and *Steps G80–G85*). `G°` cubic,
loop-free, bridgeless, `n = |V(G°)|` even; `M` a perfect matching of `G°`
and `F := E(G°) ∖ M` its complementary **2-factor** (every component a
circuit, since the host is cubic); `c(F)` the number of `F`-cycles. For a
chunk `S`: `W_S` its hub set, `Z2(S)` its interiors (`S`-degree 2),
`z(S) = |Z2(S)|`, `ch(S)` its chords (branches ∉ `S` with both ends in
`W_S`), `∂(W_S)` its exits, `exc(S) = Σ_{β∈S}(ℓ_β − 2)`,
`cap(S) = 2z(S) + exc(S)`; `β₃(v)` the free branch of an interior `v`.
`Φ(S) := ∂(W_S) ⊔ ch(S)` is the **free-branch set**, weighted `w = 1` on
exits and `w = 2` on chords, so `Σ_{Φ(S)} w = z(S)`. A chunk is **proper**
when `S ≠ E(G°)`; `W_S` is **spanning** when `W_S = V(G°)` (then
`∂(W_S) = ∅` and `S` is proper only by omitting chords). Every claim
below is **colouring-free**: no admissible cube is enumerated anywhere in
*Steps G110–G114*, which is exactly why they reach shapes (GR-64)
disclosed as out of reach.

---

### Step G110 — (GR-91): the collision statistic in **slack** form, and the **parity collapse** that merges (GR-64)(iv)'s two ceiling values

(GR-64) reads `coll_M(S)` as a count of collisions and bounds it above by
`z(S)`. Read from the other end — how many interiors *fail* to collide —
the statistic becomes a statement about how much of `Φ(S)` the matching
**avoids**, and that quantity turns out to be constrained mod 2.

> **(GR-91)** *(proven; (i)–(iv) asserted at **1 126 991** (inventory
> shape, matching, proper chunk) triples against the landed
> `yloc.collide` / `coll_terms` / `pack_bound`, **0** failures, **25 368**
> at equality `coll = cap − 6`; `--slack`)*
>
> Let `M` be a perfect matching, `F = E ∖ M`, `S` a proper chunk. Put
> > `s_M(S) := #{v ∈ Z2(S) : M(v) ≠ β₃(v)}`
>
> — the interiors matched **inside** `S` — and
> > `r(S) := 6 − z(S) − exc(S) = z(S) + 6 − cap(S)`,
>
> the chunk's **demand**. Then
>
> **(i) Three forms of the collision count.**
> > `coll_M(S) = |W_S| − 2|M ∩ S| = z(S) − s_M(S)`,
>
> and `s_M(S) = Σ_{β ∈ Φ(S) ∩ F} w(β) = |F ∩ ∂(W_S)| + 2|F ∩ ch(S)|`.
>
> **(ii) The slack is EVEN.** `s_M(S) ≡ 0 (mod 2)` at every `M` and every
> chunk. (Equivalently: (GR-64)(v)'s parity is the special case
> `coll_M(S) ≡ |W_S|`.)
>
> **(iii) The term is the demand minus the slack.** With
> `term_M(S) := coll_M(S) − cap(S) + 6`,
> > `term_M(S) = r(S) − s_M(S)`,
>
> so — since `r(S) ≤ 2` ((GR-92)(ii)) and `s_M(S)` is even —
> > `term_M(S) > 0 ⟺ ( r(S) ≥ 1 and s_M(S) = 0 )`, and then
> > `term_M(S) = r(S)`.
>
> **A chunk's (GR-64) term is therefore two-valued at each chunk:
> either `0`-or-less, or exactly its demand.** (GR-64)(iv)'s distinction
> between ceiling `1` and ceiling `2` is a property of the **chunk**,
> not of the matching.
>
> **(iv) The collision set of a positive term is the whole interior
> set.** `term_M(S) > 0 ⟹ Coll_M(S) = Z2(S)`.
>
> **(v) The packing bound, restated.** Hence
> > `B(M) = max { Σ_{S ∈ 𝒫} r(S) : 𝒫 a family of DEMANDING chunks with
> > `s_M(S) = 0`, pairwise disjoint INTERIOR sets }`,
>
> and `min_M B(M) = 0` iff some `M` leaves **every** demanding chunk with
> `s_M(S) ≥ 1` — equivalently `≥ 2`, by (ii). **So (R2) is a weighted
> avoidance statement about one matching and the small-boundary hub sets,
> with no `r`-dependence at all.**

*Proof.* (i): every hub of `W_S` is covered by exactly one `M`-branch; if
that branch lies in `S` it is one of the `|M ∩ S|` branches with both
ends in `W_S` (a hub of `S`-degree 3 has no branch outside `S`, so an
`M`-branch with one end in `W_S` and one end outside meets `W_S` at an
interior, and a chord meets it at two), and otherwise the hub is an
interior whose matching branch is its free branch — which is (GR-64)'s
`Coll_M(S)`. Counting `W_S` both ways gives the first equality, and
`|W_S| − z(S) = |W_S ∖ Z2(S)|` with the second. The `Φ`-form is the same
count read on the free branches. (ii): `F` is a 2-factor, so each of its
circuits crosses the cut `∂(W_S)` an even number of times, whence
`|F ∩ ∂(W_S)|` is even; the chord term carries a factor 2. (iii) is (i)
plus `cap = 2z + exc`: `coll − cap + 6 = (z − s) − 2z − exc + 6 = r − s`.
The equivalence uses only `r ≤ 2` and `2 | s`: if `s ≥ 2` then
`term ≤ 0`. (iv): `s_M(S) = 0` says every interior's matching branch is
its free branch. (v) is (GR-64)(iii) with (iii)–(iv) substituted. ∎

**Reading.** Three things move.

- **The `min_M` quantifier acquires a mechanism.** (GR-59) proved `min_M`
  load-bearing without saying what it buys; (GR-91)(v) says exactly what:
  the matching must **avoid** a positive weight of free branches at every
  demanding hub set, and the demands are *thresholds on avoidance*, not
  on collision.
- **The parity collapse kills half of (GR-64)(iv).** The extremal family
  (GR-64)(iv) isolates — `(z, exc) ∈ {(3,1), (4,0)}` with `coll = z`, the
  "very thin extremal family" the dispatch offered as attack (c) — is
  *not* thinner than the `r = 1` family for the purposes of (R2): both
  are violated under exactly the same condition, `s_M(S) = 0`. The three
  attacks the dispatch named therefore reduce to **one**: rule out
  zero-slack demanding chunks. Attack (b), the (GR-64)(v) parity, is what
  performs the reduction — it is (ii) here — so the parity constraint
  *was* the productive one, but as a merger, not a contradiction.
- **The statistic is now cheap.** Nothing in (i)–(v) mentions a
  colouring, a rank or a deviation ladder — YLOC's own reading of what
  (R2) should be — and the measured `B(M)` distribution over all 24 671
  (inventory shape, matching) pairs, `{0: 19633, 1: 3482, 2: 1068,
  3: 380, 4: 108}`, **reproduces (GR-64)'s landed figure exactly** from
  the colouring-free side, as does `min_M B(M) = 0` at all 4924 shapes.
  The slack census is `{0: 165 126, 2: 551 490, 4: 360 260, 6: 48 179,
  8: 1662, 10: 258, 12: 16}` — every value even — and the positive terms
  are `{1: 5329, 2: 1277}`, each equal to its chunk's demand.

**Confidence: proven-informally** (three lines from (GR-64)'s own
definitions; asserted at 1 126 991 triples with the landed evaluator as
oracle). **What would change this:** an odd `s_M(S)` — which would mean
`F` is not a 2-factor, i.e. the host is not cubic or `M` is not perfect.
F13 control (1) exhibits odd slacks the moment the selection stops being
a matching, so the parity claim is not vacuous.

---

### Step G111 — (GR-92): **which chunks can demand anything at all** — six profiles, twelve with chords, and the two-cut normal form

> **(GR-92)** *(proven; (i)–(iv) asserted at **all 217 516** proper
> chunks of the 4924-shape inventory, **0** failures; `--dem`)*
>
> Let `S` be a proper chunk of a habitat shape, `ch = |ch(S)|`,
> `∂ = |∂(W_S)|`, so `z(S) = ∂ + 2ch`.
>
> **(i) The capacity floor, with the chord refinement.** If `W_S` is
> **proper** then, by (GR-32)(ii),
> > `cap(S) ≥ 7 + Σ_{γ ∈ ch(S)} (4 − exc(γ)) ≥ 7 + ch`;
>
> if `W_S` is **spanning** the same expression is an **identity**,
> > `cap(S) = 6 + Σ_{γ ∈ ch(S)} (4 − exc(γ))`,
>
> because then `E(G°) ∖ S = ch(S)` and (GR-21) pins
> `exc(E(G°)) = 6`. And `z(S) ≥ 2` always.
>
> **(ii) Six profiles, and `r ≤ 2`.** `r(S) ≥ 1` forces
> > `(z(S), exc(S)) ∈ {(2,3), (3,1), (3,2), (4,0), (4,1), (5,0)}`,
>
> hence `r(S) ≤ 2`, with `r(S) = 2` **iff**
> `(z, exc) ∈ {(3,1), (4,0)}`. *(This re-proves (GR-64)(iv)'s ceiling and
> its extremal profile in one line, and — by (GR-91)(iii) — identifies
> the ceiling-2 family with the chunks whose term, when positive, is 2.)*
>
> **(iii) The two-cut normal form.** A demanding chunk with `∂ = 2` and
> no chords has `(z, exc) = (2, 3)`, `S = E(W_S)`, **both cut branches of
> length exactly 2**, and complement excess exactly 3. Its demand is
> `M ∩ ∂(W_S) = ∅`, i.e. the matching avoids the 2-cut outright.
>
> **(iv) A chord in a demanding chunk must be long.**
> `Σ_{γ ∈ ch(S)} exc(γ) ≥ 2ch + 2 − ∂` when `W_S` is proper, and
> `≥ 2ch + 1` when `W_S` is spanning. In particular a spanning demanding
> chunk with one chord has that chord of **length 5**.
>
> **(v) The demand is weighted avoidance.** `s_M(S) ≥ r(S)` reads
> `Σ_{β ∈ Φ(S) ∖ M} w(β) ≥ r(S)`; by (GR-91)(ii) it is equivalent to
> `Φ(S) ⊄ M`.

*Proof.* (i) is (GR-32)(ii) verbatim in the proper case, and its own
computation `cap = 2z + exc(S) = 4ch + (6 − Σ_{ch} exc)` in the spanning
case. (ii): `r = 6 − z − exc` with `exc ≥ 7 − 2z` (from `cap ≥ 7`, which
covers the spanning case too since `ch ≥ 1` there) and `z ≥ 2` gives
`r ≤ 6 − z − max(0, 7 − 2z)`, i.e. `≤ 1` at `z = 2`, `≤ 2` at `z ∈
{3,4}`, `≤ 1` at `z = 5`, `≤ 0` at `z ≥ 6`; the profile list is the same
inequality solved. `r = 2` needs `z + exc = 4` with `2z + exc ≥ 7`, i.e.
`z ≥ 3`. (iii): `∂ = 2, ch = 0` gives `z = 2`, so `exc(S) = 3` by (ii);
`E(W_S) = S` as `ch = 0`; the cut criterion at `W_S` and at its
complement each demand excess `≥ 3` inside, and `exc(E(G°)) = 6` leaves
nothing for the two cut branches. (iv) is (i) against `cap ≤ z + 5`
(which is `r ≥ 1`). (v) is (GR-91)(i) and (ii). ∎

**Reading.** The demand system is **small and local**. Exhaustively over
the inventory: **15 470 of 217 516** proper chunks demand anything, in
twelve `(z, exc, ch, ∂, r)` profiles —

`{(2,3,0,2,1): 314, (2,3,1,0,1): 1946, (3,1,0,3,2): 2092,
(3,2,0,3,1): 4273, (4,0,0,4,2): 1381, (4,0,1,2,2): 20,
(4,0,2,0,2): 40, (4,1,0,4,1): 4643, (4,1,1,2,1): 32,
(4,1,2,0,1): 488, (5,0,0,5,1): 8, (5,0,1,3,1): 233}`

— with `∂ ≤ 5` and `ch ≤ 2` throughout, i.e. every demand lives at a
**small-boundary hub set with at most two long chords**, per shape
`{0: 150, 1: 774, 2: 896, 3: 1222, 4: 733, 5: 649, 6: 468, 7: 16, 8: 10,
9: 4, 10: 1, 15: 1}`. All 314 two-exit chordless demands are in (iii)'s
normal form. This is the precise sense in which YLOC's *"matchings and
small-boundary hub sets alone"* is correct, and it is what makes
(GR-64)(R1) a bounded enumeration rather than a `2^M` scan — though
*Step G112* replaces the enumeration altogether.

**Confidence: proven-informally** (arithmetic on the landed (GR-32)(ii)
and (GR-21); asserted at all 217 516 inventory chunks). **What would
change this:** a demanding chunk off the six profiles, which would
contradict (GR-32)(ii) — the assertion is live at every chunk, and F13
control (4) confirms the predicate is non-trivial (both `r ≥ 1` and
`r ≤ 0` chunks coexist at 392 of 404 sampled shapes).

---

### Step G112 — (GR-93): the **2-factor criterion** — violated chunks are unions of `F`-cycles, so violation detection needs **no chunk scan**

> **(GR-93)** *(proven; asserted **EQUAL** to the landed `2^M` ground
> truth (`gcap.two_ec_subsets` at `kmin = 1`, via `gorient.prep_shape`)
> at **all 24 671** (inventory shape, matching) pairs — **0**
> disagreements over **6606** violated (shape, `M`, chunk) triples — and
> every constructed branch set asserted to lie in the canonical chunk
> family; `--tf`)*
>
> Let `M` be a perfect matching, `F = E ∖ M`. If `term_M(S) > 0` then
>
> **(i)** every hub of `W_S` has **both** its `F`-branches inside `W_S`,
> so `W_S` is a **union of `F`-cycles**;
>
> **(ii)** `ch(S) ⊆ M`, and `S = E(W_S) ∖ C` for a **vertex-disjoint**
> set `C = ch(S) ⊆ M ∩ E(W_S)` with `|C| ≤ 2`;
>
> **(iii)** `∂(W_S) ⊆ M` and `|∂(W_S)| + 2|C| = z(S) ≤ 5`;
>
> **(iv)** conversely every such `(W, C)` whose `E(W) ∖ C` is a chunk
> `≠ E(G°)` with `r ≥ 1` **is** violated at `M`.
>
> Hence the set of positive-term chunks at `M` is computed by a search
> over the `2^{c(F)} − 1` nonempty unions of `F`-cycles together with
> their `≤ 2`-element internal-matching subsets — **no chunk
> enumeration**, and the search is *complete*.
>
> **(v)** Every proper union of `F`-cycles is one side of a **cyclic**
> edge cut of `G°` (both sides contain a circuit), so
> `|∂(W)| ≥ λ_c(G°)`, the cyclic edge connectivity.

*Proof.* (i): by (GR-91)(iii)–(iv) a positive term forces `s_M(S) = 0`,
i.e. every interior's matching branch is its free branch; then an
interior's two `F`-branches are its two `S`-branches, and a hub of
`S`-degree 3 has its matching branch in `S` and its other two branches in
`S` as well. So no `F`-branch leaves `W_S`, and `F` restricted to `W_S`
is 2-regular. (ii)–(iii): the chords and exits are exactly the free
branches, all in `M` by `s_M(S) = 0`; `z(S) ≤ 5` is `r(S) ≥ 1` with
(GR-92)(ii); `2|C| ≤ z ≤ 5`. `E(W_S) ∖ S ⊆ ch(S)` by definition, and
chords are pairwise vertex-disjoint (a hub has one free branch). (iv):
such an `(W, C)` has every free branch in `M`, hence `s = 0`, hence
`term = r ≥ 1`. (v): `W` and `V ∖ W` are each nonempty unions of
`F`-cycles, so each contains a circuit. ∎

**Reading.** This is the pass's instrument, and it is a genuine change of
complexity class, not a constant-factor win. On the inventory
`c(F) ∈ {1, 2}` (`{1: 22538, 2: 2133}` over the 24 671 pairs), so the
**largest union search is 3 subsets** where the landed route scans up to
`2^18 = 262 144` branch masks; and because the search's cost depends on
`c(F)` — not on `|E|` — it runs unchanged at `n_hub = 40`. That is what
makes *Step G115*'s reach possible, and it is also why the refutation in
*Step G114* was findable at all: a `2^{15}`-chunk scan over 36 860
Petersen length assignments is minutes of work per shape family, while
this is milliseconds.

Two structural corollaries used below: a violated chunk needs a
**zero-excess-ish short `F`-cycle union**, and — via (v) — a shape whose
cyclic edge connectivity is `≥ 6` has **no** violated chunk with a proper
`W_S` at all, whatever `M` is.

**Confidence: proven-informally** (the proof above; and exact against the
landed ground truth at every (inventory shape, matching) pair, with the
constructed sets asserted to be canonical chunks). **What would change
this:** a violated chunk whose hub set is not `F`-cycle-closed — the
`--tf` assertion is an equality of *sets*, so any such chunk fails it.
F13 controls (2) and (3) show both branches of the search are
load-bearing: dropping the spanning union `W = V` misses violations at
255 (shape, `M`) pairs, dropping the chord option at 261.

---

### Step G113 — (GR-94): two **PROVEN** sufficient conditions for `B(M) = 0` — and they cover the whole inventory and `n_hub = 8`

Let `X(G°)` be the set of **length-5** branches; `|X| ≤ 2` since (GR-21)
pins the total excess at 6 and (SD-6) caps a branch at 5.

> **(GR-94)** *(proven; both hypotheses' witnesses re-verified to give
> `B(M) = 0` at every shape where they hold — **0** failures at 4924
> inventory shapes and 39 689 `n_hub = 8` shapes; `--suff`, `--big8`)*
>
> Let `M` be a perfect matching of a habitat shape with `X ∩ M = ∅`.
>
> **(i) The spanning case is discharged by the length-5 proviso alone.**
> No violated chunk has `W_S` spanning.
>
> **(ii) Hamiltonian condition.** If in addition `F = E ∖ M` is a
> **single** circuit (a Hamiltonian cycle of `G°`), then `B(M) = 0`.
>
> **(iii) Cyclic-edge-connectivity condition.** If instead
> `λ_c(G°) ≥ 6` — including the degenerate case of no cyclic edge cut at
> all — then `B(M) = 0`.
>
> **(iv) Existence of the anchor.** Such an `M` exists at every habitat
> shape: `G°` is a bridgeless cubic (multi)graph of even order and
> `|X| ≤ 2`, so **Plesník 1972** supplies a perfect matching avoiding any
> two prescribed branches.
>
> Hence **(R2) holds at every habitat shape satisfying (ii) or (iii)**.

*Proof.* (i): a spanning `W_S` has `∂(W_S) = ∅`, so `z(S) = 2|C|` and
`r(S) = Σ_{γ ∈ C} exc(γ) − 2|C|` by (GR-92)(i)'s identity; `r ≥ 1` with
`|C| ≤ 2` ((GR-93)(iii)) forces `Σ_C exc ≥ 2|C| + 1`, i.e.
`exc(γ) = 3` for some `γ ∈ C ⊆ M` — a length-5 branch in `M`, excluded.
(ii): `c(F) = 1`, so the only union of `F`-cycles is `V(G°)` itself, and
(i) applies. (iii): by (GR-93)(v) a violated chunk with proper `W_S` has
`|∂(W_S)| ≥ λ_c ≥ 6`, so `z(S) ≥ 6` and `r(S) ≤ −exc(S) ≤ 0`; the
spanning case is (i). (iv) is the cited theorem. ∎

**Reading — and the measured coverage, which is the point.**

- **(ii) covers the entire inventory: 4924 of 4924.** Every one of the
  4924 shapes carries a Hamiltonian 2-factor whose complementary matching
  misses every length-5 branch. So on the stratum where (GR-64) measured
  `min_M B(M) = 0`, that value is now **proven**, shape by shape, by a
  theorem plus a finite check of its hypothesis — not merely observed.
- **(ii) covers 39 687 of the 39 689 `n_hub = 8` habitat shapes**, and
  the remaining 2 have `min_M B(M) = 0` by the general (GR-93) test. So
  (R2) is proven or verified across **both** exhaustive strata.
- **(iii) covers 2844 of 4924** — precisely the shapes with *no* cyclic
  edge cut. The measured cyclic-edge-connectivity census is
  `{2: 141, 3: 1937, 4: 2, None: 2844}`: **no inventory shape** has
  `4 < λ_c < ∞`, so (iii) is the weaker condition here and becomes the
  interesting one only at larger `n`.
- **(iv) is verified directly, not taken on trust.** Length-5 counts run
  `{0: 3021, 1: 1860, 2: 43}` and **0** shapes fail to admit an
  `X`-avoiding matching.

**Confidence: (i)–(iii) proven-informally** (self-contained, three lines
each on (GR-91)–(GR-93)). **(iv) true-modulo-a-named-gap:** Plesník's
theorem — *"an `(m−1)`-edge-connected `m`-regular graph of even order has
a 1-factor avoiding any prescribed `m−1` edges"*, Ján Plesník,
*Connectivity of Regular Graphs and the Existence of 1-Factors*,
Matematický časopis **22** (1972), no. 4, 310–318 — is stated for
**graphs**, and habitat shapes are **multigraphs**; the multigraph
reading is the named gap. It is not load-bearing on any figure here: the
`X`-avoiding matching is *exhibited* at every shape this pass touches
(4924 + 39 689 + 36 860), so (iv) is used only for the general statement.
**What would change this:** for (ii)/(iii), a shape satisfying the
hypothesis with `B(M) > 0` — asserted against at every covered shape;
F13 control (5) shows the length-5 proviso is not decoration (a
Hamiltonian 2-factor whose matching *does* contain a length-5 branch has
`B(M) > 0` at 237 (shape, `M`) pairs).

---

### Step G114 — (GR-95): **(GR-64)(R2) is FALSE** — 180 habitat shapes on the Petersen graph where **every** anchor matching has `B(M) ≥ 1`

(GR-94)(ii)'s hypothesis is not always satisfiable, and the first place
it fails is the obvious one: a **non-Hamiltonian** host. The Petersen
graph `P` is a habitat shape at **36 860 of the 36 960** length
assignments (GR-21) allows, and which ones fail is itself a checkable
sentence: `P` is cubic, loop-free, of girth 5, and its **only**
3-edge-cuts are its vertex stars, so the only proper connected `W` with
`|W| ≥ 2` and `∂(W) = 3` is a single hub's complement — at which (GR-25)
demands `exc(E(W)) ≥ 1`. Hence the gate rejects **exactly** the 100
profiles that pile all 6 excess units onto one hub's three branches
(asserted in both directions), and every other cut is `∂ ≥ 4`, i.e.
`2∂ ≥ 8 ≥ 7`, free of any length condition. `P` is off the swept
inventory (`n_hub = 10`) and it is the natural test of the boundary
*Step G113* draws.

> **(GR-95)** *(**REFUTED** — a witness family, machine-certified two
> independent ways; `--bigp`, `--wit`, `--dfg`)*
>
> **(i) The refutation.** Of the **36 860** habitat length assignments of
> the Petersen graph (all `excess_profiles(15, 6)` distributions gated
> through `cflank.cubic_habitat`; the 100 rejects are exactly the
> star-concentrated profiles, asserted both ways), exactly **180**
> satisfy
> > `B(M) ≥ 1` **at every one of their 6 perfect matchings**, i.e.
> > `min_M B(M) = 1`.
>
> The distribution is `{0: 36 680, 1: 180}`. **So (GR-64)(R2) is false:
> not every habitat shape carries a collision-slack anchor matching**,
> and by (GR-64)(iii) each of the 180 carries a **genuine floor**
> `d_fg ≥ 1` from the collision bound alone, with no colouring input.
>
> **(ii) A local criterion at `P`.** Every 2-factor of `P` is a pair of
> disjoint pentagons (asserted at all 6 matchings of all 36 860 shapes),
> so `M` is the 5 branches between them, and
> > `B(M) = 0` **iff** `X ∩ M = ∅` **and both pentagons of `F` carry
> > excess `≥ 1``.
>
> Asserted at all **221 160** (Petersen habitat shape, matching) pairs,
> 0 failures.
>
> **(iii) Exactly two mechanisms, both with demand 1.** Over all
> witnesses and all their matchings the violated chunks are
> `{(z, exc, ch) = (5, 0, 0): 720, (2, 3, 1): 360}` — a **zero-excess
> pentagon of the 2-factor** (proper `W_S`, `∂ = 5`, chordless, `r = 1`),
> and **`E(G°)` minus the length-5 branch** when that branch lies in `M`
> (spanning `W_S`, one chord, `r = 1`). No `r = 2` mechanism appears.
>
> **(iv) The witnesses' shape.** Every witness has **exactly one**
> length-5 branch and spreads the remaining 3 excess units over 2 or 3
> further branches: long-branch length multisets
> `{(5,4,3): 120, (5,3,3,3): 60}`. So the refutation needs the excess
> **spread**, and is a property of the **length assignment**, not of the
> graph — the same graph carries 36 680 assignments with
> `min_M B(M) = 0` (F13 control (6)).
>
> **(v) Habitat membership is certified canonically, not by (GR-25)
> alone.** `gridcol.class_shape` — the canonical certificate, which runs
> `kslide.no_rigid_branch_union`, a `2^M` scan with an exact matroid rank
> inside — accepts **all 180** witnesses (0 rejections, ~2 s each). And
> `min_M B(M) = 1` is reproduced at all 180 by the **landed `2^M` chunk
> scan** (`gcap.two_ec_subsets` via `gorient.prep_shape`), 0
> disagreements with the (GR-93) route.
>
> **(vi) (a′) is NOT refuted, and the E1(iv)/E2 detector does NOT
> fire.** At the 180 witnesses, computed exactly (exhaustive `z`-cube, no
> deviation cap): `d_adm ∈ {2: 60, 3: 120}` — every one **finite**, and
> every one `≥ min_M B(M) = 1`. Witnesses with `min_M B > d_adm`
> (which would prove `d_adm < d_fg`): **0**.

*Proof of (ii).* By (GR-93) the only unions of `F`-cycles are the two
pentagons and `V(P)`. A pentagon `W` has `E(W) = W`'s five branches (no
internal `M`-branch, since `M` joins the pentagons), so `S = E(W)` is a
chunk of cycle rank 1 with `z = ∂ = 5` and `r = 1 − exc(S)`: violated iff
`exc(S) = 0`. The spanning case is (GR-94)(i): violated iff some
`γ ∈ C ⊆ M` has `exc(γ) = 3`, and with only one length-5 branch the
`|C| = 2` sub-case (`Σ_C exc ≥ 5`) needs it too. ∎

**Reading — what this costs and what it buys.**

- **The (R2) route to (a′) is dead as posed.** YLOC's stated payoff was
  *"it would prove the collision mechanism can never obstruct (a′)"*.
  The mechanism **can** obstruct: there are habitat shapes where every
  anchor matching pays. Any (a′) argument that wanted (R2) as a lemma
  must be re-aimed.
- **What survives is strictly weaker and strictly enough** — see
  (GR-96)(iii): (a′) never needed `min_M B(M) = 0`, only
  `min_M B(M) ≤ d_adm`, and *that* is unrefuted. Stated honestly: the
  detector is **vacuous wherever `min_M B = 0`** — 81 302 of the 81 482
  shapes measured — so the only **non-vacuous** test of dominance
  anywhere is at these **180** witnesses, and there it passes with room
  (`d_adm ∈ {2,3}` against a floor of 1). The refutation therefore
  **sharpens** the target instead of closing the path, and supplies the
  first shapes at which the dominance statement has content.
- **(GR-64) is upgraded, not damaged.** At 180 shapes the bound is a
  non-vacuous lower bound on `d_fg` — the first ones known. YLOC named
  this outcome as *"a genuine floor on `d_fg`"* and it is exactly what
  arrived.
- **The boundary is Hamiltonicity, and it is sharp in both directions.**
  (GR-94)(ii) covers every shape of both exhaustively-swept strata; the
  refutation sits at a non-Hamiltonian host and needs, on top of that,
  a *spread* excess profile (iv). Both hypotheses are necessary: the
  Petersen graph with `(5,5)` lengths, or with the excess concentrated,
  has `min_M B(M) = 0`.
- **A by-product on (a′), reported and NOT developed.** At the 180
  witnesses `d_fg` is also computed exactly, and `d_fg = d_adm` at
  **every one** (`(d_adm, d_fg) ∈ {(2,2): 60, (3,3): 120}`). This is
  **new territory for (a′)** — (GR-58)'s exhaustive census is
  `n_hub ≤ 6` plus NKp(6)/NK55(6), and no `n_hub = 10` non-Hamiltonian
  shape had been tested — and it is a *corroboration*, not a proof, and
  not a re-run of (GR-58)'s census. The evaluator (`yloc.good_z`, the
  (GR-56)(iii) criterion) is cross-checked against the landed
  `gorient.fully_good_scan` at all 5640 admissible colourings of 3
  seeded witnesses (F13 control (7)).

**Confidence: REFUTED** — (GR-64)(R2) is false as a theorem. The
witnesses are exhibited, canonically habitat-certified, and their
`min_M B` re-derived by the landed `2^M` route; the matching enumeration
is complete (6 of 6, no cap). **What would change this:** only a defect
in the (GR-64) statistic itself — the witnesses are checked with the
landed `yloc.collide`/`coll_terms`/`pack_bound` on the landed chunk
family, so a repair would have to move (GR-64), not this step. Note
what is *not* claimed: the 180 are **not** proven minimal at
`n_hub = 10` (only the Petersen graph is swept there), and no claim is
made about `n_hub = 12+`.

---

### Step G115 — (GR-96): **(GR-64)(R1) delivered** — the sweep's new reach, the successor residual, and where this leaves (a′), E3 and the (GR-15) line (hand-off)

> **(GR-96)** *(measured, exhaustive where stated, caps disclosed;
> `--big8`, `--bigp`)*
>
> **(i) The extension.** By (GR-93) the chunk side of the collision
> sweep costs `2^{c(F)}`, not `2^M`, so (GR-64)'s disclosed cap lifts.
> `min_M B(M)`, exact and **uncapped on the chunk side**:
>
> | stratum | shapes | `min_M B(M)` | completeness |
> |---|---|---|---|
> | `n_hub ≤ 6` habitat (the (GR-64) inventory) | 4920 | `0` at all | exhaustive |
> | W3M / W3 / W4 / NKo2v | 4 | `0` at all | the named shapes |
> | **`n_hub = 8` habitat** | **39 689** | **`0` at all** | **exhaustive** (AGLU's landed count) |
> | **Petersen, `n_hub = 10`** | **36 860** | **`0` at 36 680, `1` at 180** | **exhaustive for that graph** |
> | **W5, `n_hub = 16`** (`E = 24`) | 1 | `0` | out of reach for (GR-64) |
> | **NK/NKo/NKp/NK55 at `m = 6`**, `n_hub = 30` (`E = 45`) | 4 | `0` at all | out of reach for (GR-64) |
> | **NK/NKo/NKp/NK55 at `m = 8`**, `n_hub = 40` (`E = 60`) | 4 | `0` at all | out of reach for (GR-64) |
>
> **81 482 shapes** in total, row-wise (W3M's isomorphism class occurs
> both as a named shape and inside the exhaustive `n_hub = 8` stratum),
> against (GR-64)'s 4924.
>
> **(ii) What stays capped.** `n_hub = 10` **beyond the Petersen graph**
> and `n_hub ≥ 12` beyond the four necklace families have **no search
> run** — there is no habitat enumerator there (GDEV's standing finding,
> now one stratum further out: `aglu.cubic_iso_classes(8)` costs ~116 s
> and `(10)` is ~50× that). `gorient.perfect_matchings`' cap is
> **disclosed as NOT bound** at every shape above (largest matching
> count 772, at `n_hub = 40`). The Petersen sweep is complete for *that
> graph*, not for `n_hub = 10`.
>
> **(iii) The successor residual — `min_M B(M) ≤ d_adm` ("collision
> dominance").** This is what (a′) actually needs from the collision
> layer, it is **weaker than (R2)**, and it is **unrefuted**: the
> E1(iv)/E2 detector reports **0** firings at every shape measured. It is
> **vacuous** wherever `min_M B(M) = 0` — 81 302 of the 81 482 shapes
> above, including all of (GR-64)'s own 4924 — so its only **non-vacuous**
> evaluation anywhere is at the **180** (GR-95) witnesses, where
> `d_adm ∈ {2, 3}` against a floor of `1`, computed exactly. **OPEN as a
> theorem**, and now with 180 shapes at which it has content. A proof would restore the whole
> payoff YLOC wanted from (R2); a refutation would be `d_adm < d_fg`,
> i.e. **an (a′) refutation and an E2 event**.

**Reading — the route ledger, and the consequence for (a′) stated
precisely (the dispatch required this).**

- **Route ledger. Entry 1** (uniform fully-good existence at `Λ = ∅`,
  `D = 0`) — **OPEN, unchanged in status**; **(a′) stays its primary and
  still carries NO bar**. What moves is the map: input (Y)'s sub-target
  **(GR-64)(R2) is REFUTED** (was: open, measured at 4924 shapes) and
  **(GR-64)(R1) is DELIVERED** (was: a named residual), and the residual
  the arc should carry forward on this leg is **(GR-96)(iii)**, not
  (R2). **Entries 2–5 untouched**; entry 5 stays PROVEN by (GR-54).
- **The consequence for (a′), exactly.** (R2) was a *sufficient*
  condition for the collision mechanism never to obstruct (a′). Its
  refutation removes that sufficiency but **refutes nothing about
  (a′)**: the obstruction (GR-64) prices is a *lower bound on `d_fg`*,
  and (a′) fails only if that bound (or anything else) pushes `d_fg`
  **above `d_adm`**. At all 180 witnesses `d_adm` exceeds the floor and,
  measured exactly, `d_fg = d_adm` — (a′) **holds** there. So the honest
  statement is: **the collision layer is a real obstruction with a real
  floor, and every shape ever measured still satisfies (a′)**; the
  quantitative gap between the floor and `d_adm` is (GR-96)(iii).
- **Input (Y)** stays **OPEN**. Its two-rung reading from (GR-65)–(GR-66)
  is unchanged; what this pass adds is that the *chunk* rung's cheapest
  named sub-target is settled negatively, and that the rung has a
  **complete, polynomial decision procedure** at a fixed matching
  ((GR-93)) — which is the first algorithmic handle the arc has on (Y)'s
  matching quantifier.
- **The (b′) bar was respected.** (GFLOW owns (b′) this wave.) One
  by-product is reported and **not developed**: (GR-93)(v) says the
  violated hub sets are sides of *cyclic* edge cuts, so the
  cyclic-edge-connectivity census `{2: 141, 3: 1937, 4: 2, None: 2844}`
  is available to whichever direction next needs a cut-connectivity
  invariant on the stratum. Nothing here measures or claims anything
  about (b′)'s availability half.
- **Suggested successors, in order** (a coordinator/user call, not made
  here): **(1)** (GR-96)(iii), collision dominance — the only sub-target
  on the (a′) path that is both weaker than (Y) and still buys the
  collision layer outright, and it is now cheap to *test* anywhere
  (GR-93) runs; **(2)** an `n_hub = 10` habitat enumerator, which would
  make the (GR-95) witness family a stratum-level statement rather than
  one graph's, and is the standing structural blocker of the whole arc
  (GDEV, re-confirmed); **(3)** input (Y)'s distance rung on (GR-55)'s
  coset coordinates, unchanged from YLOC's hand-off.
- **Riders, verbatim**: everything at **`Λ = ∅`**, **`D = 0`**, and
  **modulo (GR-4′)** where a closure chain is concerned; the `Λ ≠ ∅`
  closed-form analogue stays **unswept**; the `D > 0` lift stays
  **unswept**; **none of this closes (GR-15)**; **(GR-15) OPEN,
  unchanged in both directions**. (GR-64)(iii)'s prune stays **sound but
  INCOMPLETE** — **1250 of 24 671** killed, incompleteness **7856** —
  and both numbers travel with any figure derived from it; disjointness
  stays load-bearing, and (GR-91)(v) only *restates* the packing, it does
  not weaken the hypothesis. (GR-65)'s fit identity is consumed as a
  landed input and not re-derived. No landed figure moves: (GR-64)'s
  `B(M)` distribution and its `min_M B = 0` verdict on the inventory are
  **reproduced exactly** here from the colouring-free side.

**TERMINATION check (E1/E2/E3) — this draft's reading; the coordinator
re-runs it.**

- **E1 does NOT fire.** No g-flank; nothing here exhibits a shape whose
  every admissible colouring binds — no colouring is enumerated at all
  except in *Step G114*(vi)'s `d_adm`/`d_fg` computation and F13 control
  (7). Clause **(iv)** applied explicitly: **nothing found min-form
  `d_adm < d_fg`**, finite or infinite; the detector is run at the 180
  refuting witnesses precisely because they are where a firing was most
  plausible, and it reports **0**. Clause **(v)** applied explicitly:
  `d_adm` is computed **exactly, by exhaustive `z`-cube enumeration with
  no deviation cap**, at all 180 witnesses and is **finite at every
  one** — corroboration of (GR-54)'s proof that (v) is unfirable at
  `Λ = ∅`, `D = 0`, not a new claim. Clause (iii) respected: nothing
  here is a large-`d` claim.
- **E2 does NOT fire.** (a′) is neither refuted nor unprovable-as-posed.
  What is refuted is a **sub-target** ((GR-64)(R2)) — a named residual of
  input (Y), strictly smaller than (Y), which is itself strictly smaller
  than (a′). A sub-target refutation with a live weaker successor
  ((GR-96)(iii)) is a route event, and a route demotion is explicitly
  **not** an E2 event.
- **E3 is ARMED (by GBAL's entry-5 HIT) and does NOT fire.** E3's target
  is **entry 1**, and (a′) did not HIT here — the dispatch said so in
  advance and it is confirmed: (R2) is a sub-target of input (Y), not
  (a′), so **even a (R2) HIT would not have fired E3**, and a (R2)
  *refutation* fires it still less. **Firing is a coordinator action;
  this draft does not fire it and must not.**

---

### Verification (Steps G110–G115)

`notes/scripts/w4/gcoll.py` (**new with this pass**, untracked at draft
time; imports — all **read-only** — `yloc` (`all_shapes`, `named_shapes`,
`shape_ctx`, `matb`, `collide`, `coll_terms`, `pack_bound`, `adm_zs`,
`is_balanced_z`, `dist_of`, `good_z`, `d_adm_exact`), `cflank`
(`admissible`, `cubic_habitat`, `excess_profiles`), `gorient`
(`cm_colouring`, `fully_good_scan`, `perfect_matchings`), `gbal`
(`z_to_map`), `gcap` (`branch_stats`), `gridcol` (`class_shape`), `aglu`
(`cubic_iso_classes`), `gpsa` (`branches_at`)). **No rank and no
colouring is touched** except in *Step G114*(vi) (`d_adm`/`d_fg`, through
the landed evaluators) and F13 control (7). Local devices, none shadowing
a §1 primitive: `chunk_prof` / `slack_of` / `stat_of` (the (GR-91)–(GR-92)
statistics), `f_cycles` (the 2-factor decomposition), `is_chunk` (the
**only** duplicated canonical decision — the membership predicate of
`gcap.two_ec_masks(kmin = 1)`, needed because (GR-93) decides chunk-hood
for a *constructed* branch set without building the family; `--tf`
asserts every set it accepts lies in `gcap.two_ec_subsets`' own family,
at every violated chunk of every (inventory shape, matching) pair),
`violated_2f` / `pack_of` / `min_B` (the (GR-93) search),
`cyclic_edge_conn` / `_has_circuit`, `long5` / `ham_witness` /
`avoid5_witness` (the (GR-94) hypotheses), `petersen_family` /
`petersen_witnesses` / `stratum8` / `big_named` / `inventory` (shape
inventories).

**No geometry is sampled anywhere in this pass** — every object is a hub
multigraph, a branch subset, a perfect matching or a 2-factor — so the
standing `plane_basis` degeneracy guard has no sampled placement to
protect. It is discharged instead by routing **every** structural verdict
through a landed oracle and asserting agreement: `yloc.collide` /
`coll_terms` / `pack_bound` for the (GR-64) statistic,
`gcap.two_ec_subsets` (via `gorient.prep_shape`) for the chunk family,
`cflank.cubic_habitat` **and** `gridcol.class_shape` for habitat
membership, `gorient.perfect_matchings` for the matchings,
`gorient.fully_good_scan` for full goodness, `yloc.d_adm_exact` for
`d_adm`. Exact integers only; no floating point outside the self-timing
prints; the single rng is seeded from `C_SEED = 20260819` and printed;
the witness family is **deterministic** (no rng anywhere in *Step G114*).

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --slack   #  ~25 s  (GR-91): 1 126 991 triples, the even slack, B(M) reproducing (GR-64)'s distribution
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --dem     #  ~21 s  (GR-92): all 217 516 proper chunks, the six profiles, the two-cut normal form
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --tf      #  ~23 s  (GR-93): set-equality with the 2^M ground truth at all 24 671 (shape, M) pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --suff    #   ~6 s  (GR-94): coverage 4924/4924 (Hamiltonian), 2844/4924 (cyclic), 0 failures
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --big8    # ~226 s  (GR-96)(i): the complete n_hub = 8 stratum, 39 689 shapes
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --bigp    # ~241 s  (GR-95)/(GR-96): the Petersen family (36 860), the 180 witnesses, W5 + the eight necklaces
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --wit     # ~455 s  (GR-95)(iii)/(v): class_shape + the landed 2^M scan at all 180 witnesses
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --dfg     # ~311 s  (GR-95)(vi): exact d_adm and d_fg at all 180 witnesses; the E1(iv)/E2 detector
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --adv     # ~241 s  F13: seven controls, all must fire
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcoll.py --validate  # ~1530 s -- WELL OVER the 600 s foreground budget
```

**Budget note for the landing dispatch** (the README's *Two invocations
do not fit a 600 s foreground budget* row, extended): `--validate` runs
~1530 s and does **not** fit a sitting. The nine modes fit as **three**
foreground invocations: `--slack --dem --tf --suff` together (~75 s),
then `--big8 --bigp` together (~467 s), then `--wit` alone (~455 s),
then `--dfg --adv` together (~552 s) — four, if `--wit` is kept alone as
measured. Every figure quoted in *Steps G110–G115* was produced at
`PYTHONHASHSEED=0` and **re-confirmed per mode after the driver's last
edit**.

**The F11 table — which driver mode tests which sentence.**

| sentence | mode | what is asserted |
|---|---|---|
| (GR-91)(i): `coll = |W_S| − 2|M ∩ S| = z − s` | `--slack` | both equalities at **1 126 991** (inventory shape, matching, proper chunk) triples, against the landed `yloc.collide` |
| (GR-91)(ii): the slack is **even** | `--slack` | `s % 2 == 0` at every one of the same triples; census `{0, 2, 4, 6, 8, 10, 12}` |
| (GR-91)(iii): `term = r − s`, so `term > 0 ⟺ (r ≥ 1 ∧ s = 0)` and `term = r` | `--slack` | all three at every triple; positive-term census `{1: 5329, 2: 1277}` |
| (GR-91)(iv)–(v): the collision set is the interior set; `B(M)` unchanged | `--slack` | set-equality at every positive term; `pack_bound` of the reformulated terms equal to `yloc.coll_terms`' at every (shape, `M`) |
| (GR-91) reproduces (GR-64)'s headline | `--slack` | `B(M)` distribution `{0: 19633, 1: 3482, 2: 1068, 3: 380, 4: 108}` over 24 671 pairs and `min_M B = 0` at all 4924 — (GR-64)'s landed figures, colouring-free |
| (GR-92)(i): the capacity floor `cap ≥ 7 + Σ_ch(4 − exc)` / the spanning identity | `--dem` | both at **all 217 516** proper chunks of the inventory |
| (GR-92)(ii): **only six** `(z, exc)` profiles demand; `r ≤ 2`; `r = 2` only at `(3,1)`/`(4,0)` | `--dem` | asserted per chunk (an unclassified profile aborts); 15 470 demanding chunks in twelve `(z, exc, ch, ∂, r)` profiles |
| (GR-92)(iii): the two-cut normal form | `--dem` | at all **314** two-exit chordless demands: `(z, exc) = (2,3)`, both cut branches length 2, complement excess 3 |
| (GR-92)(iv): a demanding chord is long | `--dem` | `Σ_ch exc ≥ 2ch + 2 − ∂` (proper) / `≥ 2ch + 1` (spanning) at every demanding chunk with a chord |
| (GR-93): the 2-factor search is **exact and complete** | `--tf` | **set equality** with the `2^M` ground truth at all **24 671** (shape, `M`) pairs, 6606 violated triples, 0 disagreements |
| (GR-93): the constructed sets are canonical chunks | `--tf` | membership in `gcap.two_ec_subsets`' family at every violated chunk found |
| (GR-93): the search is `2^{c(F)}`, not `2^M` | `--tf` | `c(F)` census `{1: 22538, 2: 2133}`; largest union search **3** subsets against up to `2^18` masks |
| (GR-94)(ii): Hamiltonian + no length-5 in `M` ⟹ `B(M) = 0` | `--suff`, `--big8` | the witness matching's `B(M)` computed and asserted `0` at all **4924** inventory shapes and **39 687** `n_hub = 8` shapes that satisfy the hypothesis |
| (GR-94)(iii): `λ_c ≥ 6` + no length-5 in `M` ⟹ `B(M) = 0` | `--suff` | same, at the **2844** shapes satisfying it; `λ_c` computed exactly by a `2^n` cyclic-cut scan |
| (GR-94)(iv): an `X`-avoiding matching exists | `--suff` | exhibited at **all 4924** shapes (0 failures); length-5 census `{0: 3021, 1: 1860, 2: 43}` |
| (GR-94) coverage is total on both swept strata | `--suff`, `--big8` | `4924/4924`; `39 687/39 689`, remaining 2 at `min_M B = 0` by the general test |
| **(GR-95)(i): (R2) is REFUTED** | `--bigp` | `min_M B(M)` over **all 36 860** Petersen habitat shapes: `{0: 36 680, 1: 180}`, matching enumeration complete (6 of 6, no cap) |
| (GR-95)(ii): the Petersen local criterion | `--bigp` | asserted at all **221 160** (Petersen habitat shape, matching) pairs, plus "every 2-factor is two pentagons" at each |
| (GR-95)(iii): exactly two mechanisms | `--wit` | violated-chunk census `{(5,0,0): 720, (2,3,1): 360}` over all witnesses × matchings; a third profile aborts |
| (GR-95)(iv): the witnesses' excess profile | `--bigp` | long-branch multisets `{(5,4,3): 120, (5,3,3,3): 60}` |
| the Petersen habitat gate's rejects are exactly the star-concentrated profiles | `--bigp` | both directions asserted over all **36 960** profiles: **100** rejected, each with a hub whose star carries all 6 units; **0** star-concentrated profiles accepted |
| (GR-95)(v): the witnesses are habitat shapes, canonically | `--wit` | `gridcol.class_shape` accepts **all 180** (0 rejections); the landed `2^M` scan reproduces `min_M B = 1` at all 180 (0 disagreements) |
| (GR-95)(vi): the E1(iv)/E2 detector does not fire | `--dfg` | exact uncapped `d_adm` at all 180 (`{2: 60, 3: 120}`), all finite; `min_M B > d_adm` at **0** |
| the (a′) by-product: `d_fg = d_adm` at the witnesses | `--dfg` | exact `d_fg` at all 180; `(d_adm, d_fg)` pairs `{(2,2): 60, (3,3): 120}` |
| (GR-96)(i): the extension's reach | `--big8`, `--bigp` | `39 689` (`n_hub = 8`, asserted equal to AGLU's landed count), `36 860` (Petersen), W5, four `m = 6` and four `m = 8` necklaces, each with its matching count and the cap shown unbound |
| (GR-96)(ii): what stays capped | `--bigp` | printed as an explicit CAP DISCLOSED line naming the unswept strata |
| F13 (1): the slack parity is not vacuous | `--adv` | **6753** odd slacks under a seeded one-hub perturbation off a matching |
| F13 (2): the spanning union is load-bearing | `--adv` | dropping `W = V` misses a violation at **255** (shape, `M`) pairs |
| F13 (3): the chord branch is load-bearing | `--adv` | dropping `C ≠ ∅` misses a violation at **261** pairs |
| F13 (4): the demand predicate is non-trivial | `--adv` | both `r ≥ 1` and `r ≤ 0` proper chunks at **392 of 404** sampled shapes |
| F13 (5): (GR-94)(ii)'s length-5 proviso is not decoration | `--adv` | a Hamiltonian 2-factor whose matching contains a length-5 branch has `B(M) > 0` at **237** pairs |
| F13 (6): the refutation is a property of the **length assignment** | `--adv` | the Petersen graph carries **36 680** habitat assignments with `min_M B = 0` and **180** with `≥ 1` |
| F13 (7): the (a′) by-product's evaluator is sound at `n_hub = 10` | `--adv` | `yloc.good_z` == `gorient.fully_good_scan` at all **5640** admissible colourings of 3 seeded witnesses |

---

### Steps G116–G119 (2026-08-25, direction GFLIP) — **(GR-R1) is PROVEN**: **(GR-97)** completes (GR-69)(i)/(ii) into a two-sided **DEMAND FORM** of the (GR-51) weight criterion — a pattern is feasible **iff** every hub set's incident even branches cover both its all-A-demand count and its no-A-demand count, `inc_H(S) ≥ max(N_A(S), N_B(S))` — under which both Hall functionals are **manifestly even** and a flip's damage is an exact demand increment `e_γ(S) ∈ {0, 1, 2}`; **(GR-98)** is a four-line **counting lemma** off cubicity alone, `b ≥ n₁(S) − s(S)` for EVERY hub set at EVERY pattern with no monochromatic-A triple; **(GR-99)** chains them through submodularity of the slack into the **SELECTION THEOREM** — at every feasible pattern of ANY cubic loop-free hub multigraph (no habitat gate, no `2k` cap, no connectivity), **at most `b` A-branches are blocked and at most `a` B-branches are** — whose corollary at an unbalanced pattern is **at least `|δ| ≥ 2` feasible majority-side flips**, i.e. (GR-R1) with room to spare. **(GR-89)(ii)'s `n`-free bound `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12` loses its one named gap and is now a THEOREM** (at (GR-86)'s own landed confidence), and (GR-90)'s constant-4 row drops to *modulo (GR-C1) alone*. One landed prose clause is **CORRECTED** (the flip can also create a B-monochromatic **triple**, and that is the stratum's dominant blocking mechanism); **(GR-C2) is NOT attacked** and stays the whole residual for the constant 2 — **(GR-15) stays OPEN, no gap-map status move on `hK` itself; E3 stays ARMED and does NOT fire.**

Answering `notes/Pencil-fanout.md` §"GFLIP — thirtieth ordinal": **prove,
refute by witness, or prove-under-a-restricted-quantifier the clause
(GR-R1)** — *at every unbalanced admissible configuration, some
majority-side odd branch has a (GR-50)-feasible flip* (*Step G108*(ii)).
**The outcome is the first kind: a proof, with no restriction** — the
statement holds at every feasible pattern of every cubic loop-free hub
multigraph, with no `2k ≤ 6` cap, no habitat gate, no connectivity or
bridgelessness hypothesis, and the count of feasible majority flips is at
least `|δ|`, not merely one. Rank-free throughout: nothing imports or calls
`gexist.fully_good_rank` and no `d_fg` claim is made anywhere ((a′) / input
(Y) untouched). Read against *Steps G68–G73* ((GR-49)–(GR-54), esp. *Step
G70*'s (GR-51)), *Step G88* ((GR-69)) and *Steps G104–G109*
((GR-85)–(GR-90), esp. *Step G108*).

**Where the named route sketch survives and where it dies.** The spec's
candidate route — (GR-52)'s parity contradiction plus (GR-53)'s exhaustion
over maximal constraint structures — is **not** the proof found, and the
death is informative: (GR-52)/(GR-53) argue about *how many
monochromatic-pair hubs a pattern has*, which is a sufficient-condition
calculus ((GR-52) is one-directional), while (GR-R1) quantifies over
patterns that are merely *feasible* and may already carry many
monochromatic-pair hubs on the flipped-to side — so the pair-count
instruments do not see the hypothesis. What survives is the sketch's
*counting spirit*: the (GR-52)-style even/odd bookkeeping becomes the
observation that both Hall functionals are manifestly even in the demand
form ((GR-97)(ii)), and the "cannot block all of them at once" step becomes
the (GR-98) count. Nothing here re-derives (GR-52)/(GR-53) — they are
consumed unchanged inside (GR-54), which this pass cites and never
re-proves — and no exhaustion over structures is needed, which is why the
result carries no `2k ≤ 6` cap.

***Notation, inherited unchanged.*** `δ = a − b` is the odd-branch
imbalance and nothing else; `O` the odd branches, `a` of them A and `b` B
at the pattern under discussion; `H` the even branches; cuts written
`∂(S)`, and `∂_H(S)` / `e_H(S)` the even branches crossing / inside `S`;
`z ∈ GF(2)^E` is (GR-49)'s one bit per branch, colour **0 = A**; per hub,
`q_v` odd darts, `o_v` A-coloured ones, `b_v = q_v − o_v`, `d_v = 3 − q_v`;
(GR-50)'s `l_v = max(0, 1 − o_v)`, `u_v = min(d_v, 2 − o_v)`. **New here:**
`inc_H(S) := e_H(S) + ∂_H(S)` (even branches **meeting** `S`),
`N_A(S) := #{v ∈ S : o_v = q_v}`, `N_B(S) := #{v ∈ S : o_v = 0}` (a `q = 0`
hub counts in **both**), `n_j(S) := #{v ∈ S : o_v = j}`, the **slack**
`s(S) := inc_H(S) − N_B(S)`, and for an A-branch `γ`,
`e_γ(S) := #{ends v of γ in S : o_v = 1}` (its **lone-A ends** in `S`). A
pattern `p` is **feasible** if some admissible `z` has `z|_O = p`
((GR-50)); an odd branch is **blocked** at `p` if `p + χ_γ` is infeasible.

**Step 0 pin (mandatory, discharged before any derivation).**
(GR-49)–(GR-51) in full — in particular (GR-51)(i)'s two-sided Hall
criterion with its (a)/(b) inequalities and (GR-51)(ii)'s weight form,
consumed as the feasibility criterion and **not re-derived** (the proof
below is a change of variables in its statement, certified against the
(GR-50) oracle). (GR-52)/(GR-53)/(GR-54) consumed unchanged and not
re-attacked. (GR-69)(i) (`u_v = d_v − [b_v = 0]`) and (GR-69)(ii) (the
count `#{v ∈ S : b_v = 0} ≤ e_H(S) + ∂_H(S)`, i.e. the **necessity half of
the A-side demand inequality below, already landed**) — credited, and
extended here rather than rediscovered. (GR-85)–(GR-90) in full, in
particular *Step G108*(i)/(ii)'s descent and its named clause (GR-R1),
*Step G108*(iv)'s (GR-C2), and the measured record: (GR-R1) at 0 failures /
771 530 configurations (701 382 stratum + 1316 V8 + 47 628 + 21 204 seeded
`n = 8/10`). **Bars honoured:** (GR-C2) is not attacked (one by-product
line is *reported* at *Step G119*, not developed); no landed census is
re-run — the driver tests **pattern-level** sentences (new figures at a
different quantifier level; the equivalence to the configuration level is
(GR-49)/(GR-50), cited, not re-measured); (GR-15) / class uniformity
untouched; no `.lean` touched.

---

### Step G116 — (GR-97): the demand form — feasibility is two covering conditions, `inc_H(S) ≥ N_A(S)` and `inc_H(S) ≥ N_B(S)`, the Hall functionals are manifestly even, and a flip is an exact demand increment

**Why the pass starts here.** (GR-51)'s weight table is optimized for the
question GBAL asked — *which hubs can hurt* — and its `−1` entries make
every argument a bookkeeping of exceptional hubs. (GR-R1)'s question is
*how many branches can be blocked at once*, and for that the right
coordinates are demands, not weights.

> **(GR-97)** *(proven — a substitution in (GR-51); certified against the
> (GR-50) oracle at 57 232 (shape, pattern) pairs — ALL `2^{2k}` patterns
> per shape, ALL `2^n` hub sets per pattern — over the EXHAUSTIVE stratum,
> V8 and seeded `n = 8/10`, 0 disagreements; `--form`)*
>
> Let `G°` be a cubic loop-free hub multigraph, `p` any colouring of its
> odd branches.
>
> **(i) Closed forms.** `l_v = [o_v = 0]` and `u_v = d_v − [o_v = q_v]`
> (the `u`-half is (GR-69)(i) verbatim, since `b_v = 0 ⟺ o_v = q_v`; it
> holds at monochromatic triples too, where it reads `u_v = −1`).
>
> **(ii) The demand form.** (GR-51)(ii)'s two weight functionals are
> exactly
> > `W_A(S) = 2·(inc_H(S) − N_A(S))`,  `W_B(S) = 2·(inc_H(S) − N_B(S))`,
>
> so `p` is **feasible iff** for every hub set `S`
> > `inc_H(S) ≥ N_A(S)`  and  `inc_H(S) ≥ N_B(S)`.
>
> *Reading:* each even branch supplies exactly one A-dart to one of its
> ends; a hub with **no** A-odd dart demands one (`N_B` counts these), a
> hub with **only** A-odd darts (or none) can absorb at most `d_v − 1`
> (`N_A` counts these); feasibility says every hub set's demands are
> covered by the even branches meeting it. The necessity half of the
> A-side inequality is (GR-69)(ii)'s landed count; the equivalence is
> (GR-51)(i)+(ii). Both functionals carry a **manifest factor 2** — the
> evenness that (GR-52)'s parity contradiction extracted by hand is
> structural in these coordinates ((GR-52) itself is untouched).
>
> **(iii) The flip increment.** Flip an A-branch `γ` to B, giving
> `p′ = p + χ_γ`. Then `{v : o_v = q_v}` only **shrinks** (its ends with
> `o_v = q_v` leave; nothing enters), and `{v : o_v = 0}` **grows by
> exactly the lone-A ends of `γ`**:
> > `N_A′(S) ≤ N_A(S)`  and  `N_B′(S) = N_B(S) + e_γ(S)` for every `S`.
>
> **(iv) The block criterion.** If `p` is feasible, then
> > `p + χ_γ` is **infeasible ⟺ some `S` has `s(S) ≤ e_γ(S) − 1`**
>
> (with `e_γ(S) ≥ 1` forced, since `s ≥ 0`); the possible witness shapes
> are `(s, e_γ) ∈ {(0, 1), (0, 2), (1, 2)}`. The A-side never obstructs
> the flip, by (iii) and feasibility of `p`.

*Proof.* (i) is the two-case evaluation of `max(0, 1 − o_v)` and
`min(d_v, 2 − o_v)` ((GR-69)(i)'s proof, quoted). (ii): by (i),
`w_A(v) = 2u_v − d_v = d_v − 2[o_v = q_v]` and
`w_B(v) = d_v − 2l_v = d_v − 2[o_v = 0]`; summing over `S` with the
handshake `Σ_{v∈S} d_v = 2e_H(S) + ∂_H(S) = inc_H(S) + e_H(S)` gives
`Σ_S w_A + ∂_H(S) = (2e_H + ∂_H) − 2N_A + ∂_H = 2(inc_H − N_A)` and its
`B`-twin; (GR-51)(i)+(ii) say feasibility ⟺ both are `≥ 0` at every `S`
(a monochromatic-A triple is caught by the A-side singleton,
`N_A({v}) = 1 > 0 = inc_H({v})`, so no separate `l ≤ u` clause is
needed). (iii): flipping `γ` lowers `o_v` by one at each of its two ends
and changes nothing else; `o_v − 1 = q_v` is impossible, so nothing
enters `{o = q}`; `o_v − 1 = 0 ⟺ o_v = 1`, and an `{o = 0}` hub is not
an end of an A-branch, so nothing leaves. (iv): by (iii) the `p′`-A-side
inequality is implied by the `p`-A-side one, and the `p′`-B-side
inequality at `S` reads `inc_H(S) ≥ N_B(S) + e_γ(S)`, i.e.
`s(S) ≥ e_γ(S)`. ∎

**The `q = 0` clause is load-bearing, measured.** `N_A`/`N_B` count the
odd-dart-free hubs on **both** sides (such a hub demands one incoming
A-dart and one incoming B-dart from its three even branches). The
doctored variant that drops them — a strict relaxation — wrongly declares
**1648** stratum patterns feasible (`--form`; 0 at V8, 0/4 at the seeded
`n = 8/10` legs), so the clause is not a convention but a constraint.

---

### Step G117 — (GR-98): the counting lemma — `b ≥ n₁(S) − s(S)` at every hub set, off cubicity alone

> **(GR-98)** *(proven; the identity and both inequalities asserted at
> 3 458 768 (shape, pattern, hub set) triples — every pattern of every
> stratum shape and of V8, feasible AND infeasible, every hub set —
> `--lemma`)*
>
> Let `p` be any colouring with `o_v ≤ 2` at every hub (in particular any
> feasible `p`), `S` any hub set. Then, with `s(S) = inc_H(S) − n₀(S)`:
>
> **(i) The exact identity.**
> > `Σ_{v∈S} b_v = 2n₀(S) + 2n₁(S) + n₂(S) − s(S) − e_H(S)`.
>
> **(ii) The count.** `2b = Σ_{v∈V} b_v ≥ Σ_{v∈S} b_v` and
> `e_H(S) ≤ inc_H(S) = n₀(S) + s(S)` give
> > `2b ≥ n₀(S) + 2n₁(S) + n₂(S) − 2s(S)`, in particular
> > **`b ≥ n₁(S) − s(S)`**.
>
> Symmetrically (colour swap, `o ↔ b`): `a ≥ #{v ∈ S : b_v = 1} − s_A(S)`
> with `s_A(S) := inc_H(S) − N_A... ` — precisely, with
> `m_j(S) := #{v ∈ S : b_v = j}` and `s_A(S) := inc_H(S) − m₀(S)`,
> `a ≥ m₁(S) − s_A(S)` whenever `b_v ≤ 2` everywhere.

*Proof.* Cubicity: `d_v = 3 − o_v − b_v`, so
`Σ_S b_v = 3|S| − Σ_S o_v − Σ_S d_v`. With `o_v ≤ 2`,
`|S| = n₀ + n₁ + n₂` and `Σ_S o_v = n₁ + 2n₂`; the handshake gives
`Σ_S d_v = inc_H(S) + e_H(S) = n₀ + s + e_H`. Substituting,
`Σ_S b_v = 3(n₀ + n₁ + n₂) − (n₁ + 2n₂) − (n₀ + s + e_H)
= 2n₀ + 2n₁ + n₂ − s − e_H`, which is (i). (ii) is `e_H ≤ e_H + ∂_H`
plus `b_v ≥ 0` off `S`, then discarding `n₀ + n₂ ≥ 0`. The symmetric form
is the global A↔B swap `z ↦ z + 𝟙`, under which `o ↔ b`. ∎

**Reading.** A hub with exactly one A-odd dart forces B-darts nearby: it
has `b_v = q_v − 1` B-odd darts and its remaining even branches deliver
their B-darts elsewhere. (i) makes that exact: every `o = 1` hub in `S`
contributes **2** to the B-odd-dart count of `S`, discounted only by the
slack and by the internal even branches — and there are only `2b` B-odd
darts in the whole graph. Feasibility is **not** a hypothesis; the lemma
is pure cubic bookkeeping, which is what lets the theorem below apply it
to a *union* of witness sets without re-checking anything.

---

### Step G118 — (GR-99): the selection theorem — at most `b` A-branches are blocked; corollary: (GR-R1), with `≥ |δ|` feasible majority flips

> **(GR-99)** *(proven; asserted at 57 586 feasible patterns over six legs
> — the stratum EXHAUSTIVE (45 592 feasible patterns, all `2^{2k}` swept),
> V8, seeded `n = 8/10`, the named large shapes to `n_hub = 60` (patterns
> sampled, disclosed) and beyond-habitat random cubic shapes at
> `2k = 8/10` — 0 violations; the bound is TIGHT (18 stratum instances per
> side attain `#blocked = opposite count > 0`) and the corollary's `|δ|`
> is attained (minimum feasible-majority-flip count over the stratum's
> unbalanced patterns is exactly 2 = `|δ|`); `--thm`, `--wit`)*
>
> Let `G°` be a cubic loop-free hub multigraph and `p` a **feasible**
> colouring of its odd branches, `a` of them A and `b` of them B. Then
>
> **(i)** at most **`b`** A-branches are blocked, and at most **`a`**
> B-branches are.
>
> **(ii) Corollary — (GR-R1), strengthened.** If `p` is unbalanced with
> majority side A (`a > b`), then at least `a − b = |δ| ≥ 2` A-branches
> have (GR-50)-feasible flips. By (GR-49)/(GR-50) the same statement reads
> at configurations: **at every unbalanced admissible configuration, at
> least `|δ|` majority-side odd branches have (GR-50)-feasible flips** —
> in particular some one does, which is (GR-R1) verbatim.
>
> No habitat gate, no bound on `2k`, no connectivity, no bridgelessness:
> the hypotheses are exactly *cubic, loop-free, `p` feasible*.

*Proof of (i) (A side; the B side is the colour swap).* Let
`γ₁, …, γ_m` be blocked A-branches. By (GR-97)(iv) each has a witness
`S_t` with `s(S_t) ≤ e_t − 1`, where `e_t := e_{γ_t}(S_t) ∈ {1, 2}`.

*The slack is submodular and nonnegative.* `inc_H` is a coverage function
(a sum over even branches of `S ↦ [the branch meets S]`, each summand
submodular), `n₀` is modular, so `s = inc_H − n₀` is submodular; and
`s ≥ 0` at every set because `p` is feasible ((GR-97)(ii)). Hence for the
union `U := S_1 ∪ ⋯ ∪ S_m`, by induction on `m`
(`s(X ∪ Y) ≤ s(X) + s(Y) − s(X ∩ Y) ≤ s(X) + s(Y)`),
> `s(U) ≤ Σ_t s(S_t) ≤ Σ_t (e_t − 1)`.

*The counted ends are distinct hubs.* Each end counted by `e_t` is a hub
`v ∈ S_t ⊆ U` with `o_v = 1`. Within one branch the two ends are distinct
hubs (`G°` loop-free). Across branches: a hub with `o_v = 1` carries
exactly one A-odd dart, so it is an end of exactly **one** A-branch —
no hub is counted for two different `γ_t`. Hence
> `n₁(U) ≥ Σ_t e_t`.

*Count.* By (GR-98)(ii) applied at `U` (legitimate: `p` feasible gives
`o_v ≤ 2` everywhere),
> `b ≥ n₁(U) − s(U) ≥ Σ_t e_t − Σ_t (e_t − 1) = m`. ∎

*(ii)* is immediate: `#feasible A-flips ≥ a − b = δ ≥ 2` (`δ` even). The
configuration form: an unbalanced admissible configuration is an
admissible `z` ((GR-49)); its pattern is feasible (witnessed by `z`
itself), unbalancedness, majority side and flip-feasibility are functions
of the pattern alone, so the configuration-level quantifier factors
through the pattern level exactly. ∎

**Both inequalities are sharp, and blocked branches are real.** Blocked
majority instances exist in quantity (32 608 blocked (feasible pattern,
branch) instances on the stratum, up to **3** blocked at the
beyond-habitat `2k = 8/10` legs), so the theorem is not counting an empty
family; the bound `≤ b` is attained with `b > 0` at 18 stratum instances
per side; and the corollary's `≥ |δ|` is attained (stratum minimum
exactly 2 at `|δ| = 2`). The `b = 0` corner is the sharpest prediction —
*at an all-A feasible pattern no flip is ever blocked* — and the stratum
sweep confirms it exhaustively (every `#blocked = 0` cell of the
`(a, 0)`-pattern census).

**Witness anatomy — the proof's two shapes, realized.** At every one of
the 32 608 blocked stratum instances the minimal demand-form violator has
the shape (GR-97)(iv) predicts (`--wit`, all asserted):
`(s, e_γ, |S|)` histogram `{(0,1,1): 15 804, (0,1,2): 3480, (0,1,3): 996,
(0,1,4): 528, (1,2,2): 36, (1,2,3): 144, (1,2,4): 132, (1,2,6): 11 488}`
— i.e. either a **tight set swallowing one lone-A end** (`s = 0`) or a
**slack-1 set swallowing both** (`s = 1, e = 2`), exactly the two cases
the union argument prices.

**A landed prose clause CORRECTED, scoped exactly (the *Step G56*/*Step
G60* marker precedent; it touches no measurement).** *Step G109*'s
residual item 2 (and the dispatch spec quoting it) glosses (GR-R1) as
(GR-51)-shaped because *"flipping `γ` A → B can only create
**B**-monochromatic-pair hubs"*. That is **incomplete**: the flip can
also create a **B-monochromatic triple**, at an end `v` with `q_v = 3`,
`o_v = 1` — and the anatomy histogram shows this singleton case
(`|S| = 1`, forced `d_v = 0 < 1`) is the stratum's **dominant** blocking
mechanism (15 804 of 32 608 minimal violators). The corrected gloss:
flipping `γ` A → B can only create **B-side demand** — a new
B-monochromatic-pair hub or a B-monochromatic triple — and (GR-97)(iii)
is its exact form. Nothing downstream of the landed gloss moves: it was
motivation prose, not an input to any landed derivation.

---

### Step G119 — what (GR-R1)'s proof upgrades, what it does not touch, and the hand-off

- **(GR-89)(ii) is now a THEOREM**: `d_adm(M) − d_par(M) ≤
  4·min(k, ⌊n_hub/4⌋) ≤ 12`, uniform in `n`, with **no named gap left**.
  The chain is (GR-99)(ii) (pick a feasible majority flip — one exists at
  every unbalanced admissible configuration, including every intermediate
  configuration of the descent) + (GR-86) (each such flip repairs at price
  `≤ 4`) + (GR-69)(iii) (the starting imbalance is `≤ 2·min(k, ⌊n/4⌋)` at
  a parity-optimal configuration). Its confidence is the chain's weakest
  link, which is now **(GR-86)(iii)/(iv)'s own landed status**
  (proven-informally; the degenerate chain coincidences machine-checked,
  the one named gap of that step) — (GR-R1) is no longer a qualifier
  anywhere.
- **(GR-90)'s constant table, updated.** Row 4 ((b′) at `4·min(k, ⌊n/4⌋)`,
  was *PROVEN modulo (GR-R1)*) → **PROVEN**. Row 3 ((b′) at the constant
  4, was *proven modulo (GR-C1) + (GR-R1)*) → **PROVEN modulo (GR-C1)
  alone** — hence a full theorem on the `n_hub ≤ 6` stratum, where
  (GR-C1) is (GR-69)'s arithmetic. Row 5 (`2·min(k, ⌊n/4⌋)`) → proven
  modulo (GR-C2) alone. **(b′) at the constant 2 is UNCHANGED**: (GR-C2)
  is still the whole residual, per the standing bar it was not attacked.
- **One (GR-C2)-adjacent by-product, reported and NOT developed** (the
  spec's bar): (GR-99)(ii) gives `≥ |δ| ≥ 2` *feasible* majority branches
  at every unbalanced configuration, so a (GR-C2) failure now needs
  **every one of ≥ 2 feasible majority branches** to be a doubly-blocked
  matching branch — a strictly smaller target than *Step G108*(v)'s
  already-narrow cell, and a counting hypothesis ((GR-89)(iii) covers
  "every majority branch"; the "every **feasible** majority branch"
  variant is open). Offered to the (GR-C2) successor as a sharpened
  hypothesis, with no figure attached.
- **The greedy descent's stall count 0 is now a theorem, not a
  measurement**: *Step G108*(iv)'s "0 stalls at 771 530 configurations"
  is implied by (GR-99)(ii) at every intermediate configuration.
- **What is NOT touched.** Entry 5 ((GR-54)) — consumed, unchanged.
  Entry 1 / (a′) / input (Y) — not attempted; no rank computed anywhere.
  (GR-64) rows — GCOLL's, unchanged. (GR-15) — **OPEN, unchanged in both
  directions**; no flank, no class-uniformity claim. The shift-metric
  layer stays **UNBOUNDED** ((GR-43)); every statement here is a bound on
  a **difference** or a count of flips, never on `d_adm`.
- **Riders, verbatim.** Everything is at **`Λ = ∅`**, **`D = 0`**, and
  **modulo (GR-4′)** where a closure chain is concerned; the **`Λ ≠ ∅`
  closed-form analogue** and the **`D > 0` lift** stay **unswept**.
  (GR-97)/(GR-98) use cubicity throughout (`d_v = 3 − q_v`, the handshake
  with three darts per hub), so a `D > 0` lift must redo both; (GR-99)'s
  proof would survive any carrier in which (GR-51) and the cubic
  handshake do.

**The residual, as this landing leaves it (successor order).**
1. **(GR-C2)** — unchanged, the whole gap between the proven constant 4
   and (b′)'s 2, now with the sharpened "every *feasible* majority branch
   doubly-blocked" hypothesis above and *Step G108*(v)'s `n_hub = 8`,
   `2k = 2` cell as the first possible home. **[Settled at *Steps
   G120–G124* (2026-08-25, direction GCHEAP), which took exactly this
   hypothesis: proven at `n ≤ 10`, per-configuration form refuted from
   `n_hub = 12` (the `n = 8` cell is provably empty — *Step G108*(v)'s
   correction marker); successor **(GR-104)(i)**.]**
2. **(GR-C1) past the stratum** — unchanged (GPSA's first clause;
   (GR-69) is its exact `n ≤ 6` boundary).

---

### Verification (Steps G116–G119)

`notes/scripts/w4/gflip.py` (**new with this pass**; imports — all
read-only — `balb` (`stratum_cases`, `v8_specs`), `gbal` (`bounds_of`,
`feasible_at`, `named_cases`, `odd_idx`, `random_cases`), `gdesc`
(`imb_of`), `gflow` (`feas_flip`, `seeded_shapes`), `gpsa`
(`branches_at`)). **Rank-free**: `gexist.fully_good_rank` is never
imported or called and no `d_fg` claim is made anywhere. Local devices,
none shadowing a §1 primitive (checked against the README index and the
*Divergences* table): `odd_profile` ((o, q) off a bitmask pattern),
`even_masks`, `demand_data`/`demand_ok` ((GR-97), with the doctored
variant as the F13 control), `blocked_of`, `wit_anatomy` (the (GR-99)
witness extraction and shape asserts), `hist`, `seeded_legs`. Exact
integers over GF(2) throughout; no floating point; rngs seeded per mode
with the seed printed; no `set` printed (the one set comprehension is a
sampling dedup, never printed). **No pool is new**: the stratum is
`balb.stratum_cases` (= `gbal.pool_cases` behind the (GR-25) cut
criterion, EXHAUSTIVE), V8 is `balb.v8_specs`, the seeded `n = 8/10`
pools are `gflow.seeded_shapes` (= `balb.rand_habitat`), the named large
shapes are `gbal.named_cases`, and the beyond-habitat shapes are
`gbal.random_cases` — all reused read-only.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --form      # ~10 s (GR-97): closed forms + demand-form <=> oracle, 57232 pairs, + doctored control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --lemma     # ~25 s (GR-98): the identity and both inequalities at 3458768 triples
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --thm       # ~10 s (GR-99): the bound + the corollary at 57586 feasible patterns, six legs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --wit       # ~8 s  witness anatomy at all 32608 blocked stratum instances + controls
PYTHONHASHSEED=0 python3 notes/scripts/w4/gflip.py --validate  # ~44 s all four in one process
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-97)(i) the closed `l`/`u` forms | `--form` | asserted per hub against `gbal.bounds_of` at every (shape, pattern) pair of every leg |
| (GR-97)(ii) the demand form is **exactly** feasibility | `--form` | `demand_ok` (all `2^n` hub sets) asserted `==` the (GR-50) oracle (`gbal.feasible_at`) at all 57 232 pairs — stratum EXHAUSTIVE at both quantifiers, 0 disagreements |
| (GR-97) the `q = 0` clause is load-bearing | `--form` | the doctored variant (odd-dart-free hubs dropped) asserted a relaxation, and its wrong-feasible count printed: **1648** on the stratum |
| (GR-97)(iii) flip monotonicity (kept side) | `--wit` | `inc_H(S) ≥ N_A′(S)` asserted at **every** hub set of **every** blocked instance |
| (GR-97)(iv) the block criterion's witness shapes | `--wit` | every violator asserted to satisfy `e_γ ≥ 1`, `s ≤ e_γ − 1`, `s ≥ 0`; a violator asserted to **exist** whenever the oracle says blocked |
| (GR-98)(i)/(ii) the identity and both counts | `--lemma` | asserted at 3 458 768 (shape, pattern, hub set) triples, **feasible and infeasible patterns alike**; the `o = 3` skips counted and printed (2991 per side, all infeasible by (GR-97)) |
| (GR-99)(i) `#blocked ≤` opposite count, both sides | `--thm` | `assert len(bA) <= b` and `assert len(bB) <= a` at all 57 586 feasible patterns of six legs, 0 violations |
| (GR-99)(ii) `≥ \|δ\|` feasible majority flips | `--thm` | asserted at every unbalanced feasible pattern (32 822 across the legs); the minimum realized count printed (2 on the stratum = `\|δ\|`, so the corollary is tight) |
| (GR-R1), pattern form | `--thm` | `assert nf >= 1` at every unbalanced feasible pattern; the configuration form is the (GR-49)/(GR-50) factoring, **cited not re-measured** |
| the bound is TIGHT | `--thm` | `#blocked = opposite count > 0` counted: 18 per side on the stratum |
| blocked branches exist (the theorem is not vacuous) | `--thm`, `--wit` | 32 608 blocked stratum instances; up to 3 blocked per pattern at `2k = 8/10`; the naive "never blocked" sentence reported REFUTED |
| the corrected gloss (triples, not only pair hubs) | `--wit` | the singleton (`\|S\| = 1`) anatomy class — exactly the created-B-triple case — counted: 15 804 of 32 608 |
| no `2k` cap | `--thm` | the beyond-habitat leg: seeded random cubic shapes at `2k = 8/10` (NOT excess-6), 9864 feasible patterns, 0 violations |
| (a′) / `d_fg` / input (Y) / (GR-15) | — | **not attempted**; no mode computes a rank |

**Determinism.** `--validate` run at `PYTHONHASHSEED` 0 and 999: byte-identical
except the `[Ns]` wall-clock annotations. Every leg prints its seed.

**Caps, disclosed in full — an exhausted cap is not a proof of
nonexistence.** (1) Only the `n_hub ≤ 6` stratum is exhaustive — at
**both** quantifier levels (all `2^{2k}` patterns, all `2^n` hub sets);
V8 is one shape, complete. (2) The `n = 8/10` legs are **seeded samples**
(`gflow.seeded_shapes`, tries 200/90, seeds printed) — and each leg's
sample differs across modes because each mode seeds its own rng (offsets
+1/+3, printed). (3) The named large shapes (`n_hub` to 60) have their
patterns **SAMPLED** (300 seeded draws per shape) whenever `2k > 8`;
the sampled-shape count is printed. (4) The beyond-habitat leg is a
seeded sample (6 tries per size at `n = 12/16`, `2k ∈ {8, 10}`); those
shapes are **deliberately outside** the excess-6 habitat scope, since the
theorem carries no `2k` cap. (5) No search caps exist in any assertion
path and none was hit. **None of these caps qualifies the proof** — they
qualify only the machine cross-check's reach; the proof itself has no
cap.

**Scratch probes (README's standing rule).** One exploratory probe was
run during the derivation (the first-stratum-shape smoke test of the
demand form); it is **not retained** — its content is subsumed by
`--form`'s first leg, which asserts the same sentence at every stratum
shape. Every figure quoted above is produced by `gflip.py`.

---

### Confidence verdict (Steps G116–G119)

| | claim | standing |
|---|---|---|
| **(GR-97)** | the demand form — closed `l`/`u`, `W = 2(inc − N)`, feasibility ⟺ two covering conditions, the flip increment | **proven** (a substitution in (GR-51), with (GR-69)(i)/(ii) as the landed half, credited); certified against the oracle at 57 232 pairs, 0 disagreements, with the doctored control separating the `q = 0` clause |
| **(GR-98)** | the counting lemma `b ≥ n₁(S) − s(S)` (and its exact identity) | **proven** (four lines off cubicity; feasibility not needed); asserted at 3 458 768 triples including infeasible patterns |
| **(GR-99)(i)** | at most `b` A-branches blocked, at most `a` B-branches | **proven** (submodular union of (GR-97) witnesses + injectivity of lone-A ends + (GR-98)); 0 violations at 57 586 feasible patterns over six legs; **tight** (18 stratum instances per side) |
| **(GR-99)(ii)** | `≥ \|δ\|` feasible majority flips at every unbalanced admissible configuration | **proven** (arithmetic corollary + the (GR-49)/(GR-50) pattern factoring); tight (minimum 2 realized at `\|δ\| = 2`) |
| **(GR-R1)** | *some majority-side odd branch has a (GR-50)-feasible flip* | **PROVEN** — the graded outcome of the first kind, with no restricted quantifier and no habitat/`2k`/connectivity hypothesis. The measured 0/771 530 record is explained, not extended |
| **(GR-89)(ii)** | `d_adm(M) − d_par(M) ≤ 4·min(k, ⌊n_hub/4⌋) ≤ 12`, `n`-free | **upgraded: true-modulo-named-gap → THEOREM** (the named gap was exactly (GR-R1)); residual confidence qualifier = (GR-86)(iii)/(iv)'s own landed status (its degenerate coincidences are machine-checked, as recorded at *Steps G104–G109*) |
| **(GR-90) table** | rows 3/4/5 | row 4 **PROVEN**; row 3 **PROVEN modulo (GR-C1) alone** (a theorem on the `n ≤ 6` stratum); row 5 proven modulo (GR-C2) alone |
| the corrected gloss | the flip can create a B-**triple**, not only B-pair hubs | **proven** ((GR-97)(iii) singleton case) and **measured dominant** (15 804 / 32 608); a prose correction, no landed measurement moves |
| **(GR-C2)** | the selection clause for the constant 2 | **OPEN — not attacked** (standing bar); one sharpened hypothesis reported as a by-product, no figure |
| **(a′)** / input (Y) / (GR-64) rows | | **OPEN — not attempted**; no rank computed anywhere |
| **(GR-15)** | | **OPEN — unchanged in both directions**; no flank, no class-uniformity claim |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as GBAL's through GFLOW's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos)
(AC-9)); the only samplers draw **graphs**, not placements.

### What would change this (Steps G116–G119)

*(i)* **An error in (GR-51)** would undermine (GR-97) and everything
after; the demand form is however certified against the independent
(GR-50) oracle at every pattern of the whole stratum, so an error would
have to live in both. *(ii)* **A blocked-count witness above the bound**
— a feasible pattern with more blocked A-branches than `b` — refutes
(GR-99)(i); none exists on the exhaustive stratum, and the bound is
attained there, so any counterexample lives off the stratum and past the
sampled legs. *(iii)* **The `D > 0` lift** must redo (GR-97)/(GR-98)
(cubicity is used in both); the `Λ ≠ ∅` analogue stays unswept by
standing rider. *(iv)* **(GR-C2)** is untouched: proving it (or the
sharpened "every feasible majority branch" variant reported at *Step
G119*) closes (b′) at the constant 2 given (GR-C1); refuting it kills the
descent route to 2 but not the now-proven constant 4. *(v)* **A Lean
transcription** of (GR-97)–(GR-99) would be small (finite counting on a
multigraph, one submodularity lemma); nothing here pins a carrier choice
beyond what (GR-49)–(GR-51) already pin.

**TERMINATION check (E1/E2/E3) — this direction's reading; the
coordinator re-runs it.**

- **(E1) NOT FIRED.** No g-flank; the pass is rank-free and computes no
  rank, so clauses (i)–(iv) cannot fire on it. Clause (v) (`d_adm = ∞`)
  fires on nothing: every stratum shape's balanced patterns include a
  feasible one ((GR-54), consumed), and this pass adds a demand-form
  witness of feasibility at 45 592 stratum patterns.
- **(E2) NOT FIRED.** Entry 5 is PROVEN ((GR-54)) and consumed untouched;
  nothing here demotes any route — on the contrary, (GR-R1)'s proof
  removes a qualifier from a landed bound. The one correction (the
  triple-creation gloss) is prose, with successors named in place.
- **(E3) ARMED (by GBAL), DOES NOT FIRE, and this direction does not fire
  it.** E3 fires only on a HIT completing **entry 1** — i.e. (a′). This
  pass does not attempt (a′), computes no rank, and makes no `d_fg`
  claim. The HIT here is on **(b′)'s availability layer** ((GR-R1) →
  (GR-89)(ii) a theorem), which is not entry 1 and arms nothing. **Firing
  is a coordinator action; reported, not fired.**

---

### Steps G120–G124 (2026-08-25, direction GCHEAP) — **(GR-C2) is settled in its per-configuration readings and reshaped in its as-posed one**: **(GR-100)** is the **lone-dart identity** — at every admissible configuration `#{v : exactly one A-dart} = n/2 − δ` exactly — and its **blocked-end capacity**: the majority side's blocked ends occupy distinct lone-majority-dart hubs, so majority branches carry **at most `n/2 − |δ|` blocked ends** and at most `⌊(n − 2|δ|)/4⌋` of them are **doubly blocked** (sharpening (GR-89)(iii)'s counting from `n ≥ 4a − b` to `n ≥ 6a − 2b`); **(GR-101)** chains that through (GR-99)(ii) into the **selection corollary** — at every unbalanced admissible configuration and EVERY perfect matching, `#cheap majority branches ≥ |δ| − ⌊(n − 2|δ|)/4⌋` — so the **every-step form of (GR-C2) is a THEOREM for `n_hub < 6|δ|`**, i.e. everywhere `n_hub ≤ 10` at `|δ| = 2`: the landed 96 930 + 2 114 + 371 censuses become theorems, *Step G108*(v)'s hunt cell is **provably empty**, and **per-matching (b′) at the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum** (and at `n_hub = 8, 10` modulo (GR-C1) alone); **(GR-102)** is the **stall tax** `dist(z, M) ≥ |a_M − b_M + δ|`, localizing any failure to matchings with `d_par(M) ≥ 2|δ| − b_M`; **(GR-103)** shows the boundary is **TIGHT**: an explicit constructed habitat shape at `n_hub = 12 = 6|δ|`, `2k = 2`, carries a **parity-optimal** `|δ| = 2` configuration at which **every feasible majority branch is a doubly-blocked matching branch** — the spec's named refutation object, killing the per-configuration and every-step forms at `n ≥ 12` — while the **as-posed existential form survives at every audited pair** (gap `d_adm − d_par = 0`, and the stalled configurations' one-flip prices are exactly `[0, 0]`: the **descent step survives the stall**, only the cheapness *certificate* dies); **(GR-104)** mints the reshaped residual — the **price form** of the selection clause — and the **descent interpolation** `d_adm(M) − d_par(M) ≤ δ_M + 2·min(δ_M/2, ⌊n/12⌋)`, improving (GR-89)(ii) below `n = 12·(δ_M/2)`. **(GR-15) stays OPEN, no gap-map status move on `hK` itself; E3 stays ARMED and does NOT fire.**

Answering `notes/Pencil-fanout.md` §"GCHEAP — thirty-first ordinal": **prove,
refute by witness, or prove-under-a-restricted-quantifier the clause (GR-C2)**
(*Step G108*(iv)). **The outcome is graded, and the grading is the finding**:
the strongest per-configuration reading is **proven for `n_hub ≤ 10` and
refuted by witness at `n_hub = 12`, with `n = 6|δ|` the exact boundary in both
directions**; the as-posed existential reading is **proven for `n_hub ≤ 10`
and OPEN beyond**, with the refutation witnesses *failing to refute it* at
every audited pair — and the reason they fail (the stalled flips price 0) is
minted as the successor statement (GR-104). Rank-free throughout: nothing
imports or calls `gexist.fully_good_rank` and no `d_fg` claim is made anywhere
((a′) / input (Y) untouched). Read against *Steps G104–G109*
((GR-85)–(GR-90), esp. *Step G108*), *Steps G116–G119* ((GR-97)–(GR-99)) and
*Steps G68–G73* ((GR-49)–(GR-51)).

**Where the offered route sketch survives and where it goes further.** GFLIP's
*Step G119* offered the *"every **feasible** majority branch"* variant of
(GR-89)(iii)'s counting as the natural first attack. That is exactly what
lands — but at a **different dart level** than either predecessor: (GR-89)(iii)
counts `A(v)` over the two `F`-darts and (GR-97)/(GR-98) count odd darts per
hub, while the decisive count is over **all three darts** ((GR-100)(i) is the
`M`-inclusive analogue of (GR-85)(iv)'s `T`-identity). The demand instruments
(GR-97)/(GR-98) are consumed only through (GR-99), never re-derived.

***Notation, inherited unchanged, with one deliberate new symbol.*** `δ = a − b`
signed; `O`, `H`, `M`, `F = G° ∖ M`, `z`, colour **0 = A**, `m(v)`, blocked
ends, dart-free / one-end-blocked / doubly blocked, `d_par(M)`, `d_adm(M)`,
`f(p)` — all as at *Steps G104–G109*. A majority-side branch is **cheap**
(*Step G108*(iv)) iff its flip is (GR-50)-feasible and it is not a
doubly-blocked matching branch; a configuration is **stalled** iff it is
unbalanced and carries **no** cheap majority branch. **New:**
`α(v) ∈ {1, 2}` is the number of A-darts at `v` among **all three** darts —
deliberately *not* written `A(v)`, which *Steps G104–G109* reserve for the
two-`F`-dart count (`α(v) = A(v) + m_v` in that notation); `N₁ := {v : α(v) = 1}`
the **lone-A hubs**; `a_M, b_M, e_M` the A-odd / B-odd / even branch counts
**inside `M`** (`a_M + b_M + e_M = n/2`); `f₀` the number of majority-side
branches that are feasible **and** doubly-blocked matching branches;
`δ_M := min{|δ(z)| : z parity-optimal for M}`.

**Step 0 pin (mandatory, discharged before any derivation).** (GR-49) in full
(admissibility = no monochromatic hub, i.e. `α(v) ∈ {1, 2}`; the flip-set
legality test). (GR-50)/(GR-51) consumed as the feasibility oracle, not
re-derived. (GR-86) in full — in particular (i)'s blocked-end characterization
(*the ends at which `γ` carries the minority dart*) and the price ledger
(cheap ⟹ one-flip price `≤ 2`; doubly-blocked matching ⟹ `≤ 4`). (GR-89) in
full — the descent, (iii)'s counting bound (strengthened below, not
contradicted), (iv)'s cheap/(GR-C2) definitions and censuses, (v)'s hunt cell.
(GR-99)(ii) — **`≥ |δ|` feasible majority flips at every unbalanced admissible
configuration** — the landed selection theorem, consumed as the feasibility
supply. **Bars honoured:** (GR-C1) not attacked ((GR-102)/(GR-104) *consume*
it as a hypothesis exactly where the landed rows do); (GR-R1)/(GR-99) consumed,
not re-attacked; (GR-49)–(GR-54), (GR-67)–(GR-72), (GR-85)–(GR-90),
(GR-97)–(GR-99) not re-derived; no landed census re-run — the driver's
sentences quantify over **all unbalanced admissible configurations** (a
strictly larger set than the landed parity-optimal censuses) and over new
`n = 12` pairs, and the landed figures are cited, not re-measured; (GR-15) /
class uniformity untouched; no `.lean` touched.

---

### Step G120 — (GR-100): the lone-dart identity and the blocked-end capacity — the majority side can host at most `n/2 − |δ|` blocked ends, at any admissible configuration whatsoever

> **(GR-100)** *(proven; the identity asserted at all 449 446 admissible
> configurations of four legs — the stratum EXHAUSTIVE (408 688
> configurations over all 4 780 odd-carrying shapes, full `2^{|E|}` cube),
> V8, seeded `n = 8/10` — and the capacity at all 154 750 unbalanced ones,
> with attainment (gap 0) realized on every leg; `--cap`)*
>
> Let `G°` be a cubic loop-free hub multigraph, `z` admissible, `δ = a − b`.
>
> **(i) The identity.** Every hub has `α(v) ∈ {1, 2}`, and
> > `|N₁| = #{v : α(v) = 1} = n/2 − δ`  (signed; by colour swap
> > `#{v : exactly one B-dart} = n/2 + δ`).
>
> In particular **`|δ| ≤ n/2` at every admissible configuration**.
>
> **(ii) The injection.** A blocked end `v` of a **majority-side** branch is
> a lone-majority-dart hub (`v ∈ N₁` when A is the majority), and every hub
> is a blocked end of **at most one** branch (its minority dart is unique).
>
> **(iii) The capacity.** Summing (ii) over the majority side,
> > `Σ_{γ majority-side} #blocked ends(γ) ≤ n/2 − |δ|`,
>
> so at most `⌊(n − 2|δ|)/4⌋` majority-side branches are **doubly blocked**
> — of *any* kind, matching or 2-factor.
>
> **(iv) The strengthened total-failure count.** If **every** majority-side
> branch is doubly blocked (the hypothesis of (GR-89)(iii), matching-ness
> not even needed), then `2a ≤ n/2 − δ`, i.e.
> > `n ≥ 4a + 2δ = 6a − 2b`,
>
> which strictly sharpens (GR-89)(iii)'s `n ≥ 4a − b` (by `2a − b > 0`).

*Proof.* (i) Admissibility is `α(v) ∈ {1, 2}` ((GR-49): three darts, both
colours present). Counting A-darts branchwise: an even branch carries exactly
one (its two darts differ), an A-odd branch two, a B-odd branch none, so
`Σ_v α(v) = |H| + 2a = (3n/2 − a − b) + 2a = 3n/2 + δ`. Counting hubwise,
`Σ_v α(v) = |N₁| + 2(n − |N₁|) = 2n − |N₁|`. Equate. Nonnegativity of both
lone-dart counts gives `|δ| ≤ n/2`. (ii) By (GR-86)(i) a blocked end `v` of
`γ` has `m(v)` on `γ`; a majority-side (A-coloured) `γ` has an A-dart at `v`,
and a minority dart is the colour appearing **once**, so `α(v) = 1`. The
minority dart at `v` is unique, so `v` blocks at most one branch. (iii) The
sum counts distinct hubs of `N₁` (majority A; the B-majority case is the
colour swap through the second identity), and a doubly-blocked branch
consumes two. (iv) `2k` branches with two blocked ends each: `2a` ends are
distinct hubs by (ii) (loop-freeness makes a branch's own two ends distinct),
all in `N₁`. ∎

**Reading.** This is (GR-85)(iv)'s bookkeeping extended from the 2-factor to
**all three darts**: the `M`-side A-darts, which the `T`-identity deliberately
ignores, are exactly what a doubly-blocked *matching* branch spends — its
lone A-darts at both ends are `M`-darts. The identity says the whole graph
has only `n/2 − |δ|` lone-A hubs to spend, an imbalance-*decreasing* budget;
the majority side wants many flips exactly when the budget is smallest. That
tension is the entire content of the next step.

---

### Step G121 — (GR-101): the selection corollary — the every-step form of (GR-C2) is a THEOREM for `n_hub < 6|δ|`, the landed censuses become theorems, and (b′) at the constant 2 is a theorem on the whole stratum

> **(GR-101)** *(proven; asserted at all 874 244 unbalanced (configuration,
> matching) instances of four legs — the stratum EXHAUSTIVE at both
> quantifiers (23 939 pairs, 701 382 instances, reproducing gflow's landed
> denominators exactly), V8, seeded `n = 8/10` (matchings capped at 6 per
> shape, disclosed) — with the bound TIGHT (minimum slack 0 on every leg);
> `--sel`)*
>
> Let `z` be admissible and unbalanced, `M` any perfect matching. Then
>
> **(i)** `#cheap majority branches ≥ |δ| − ⌊(n − 2|δ|)/4⌋`.
>
> **(ii) The every-step form of (GR-C2).** If `n < 6|δ|` then a cheap
> majority branch exists at `z` — with **no** parity-optimality, habitat,
> or `2k` hypothesis. At `|δ| = 2` that is all of `n ≤ 10`; on the
> `n ≤ 6` stratum the count is `≥ 2` and **no feasible majority branch is
> ever a doubly-blocked matching branch** (capacity 0), proving *Step
> G107*/*G108*(v)'s parity-optimal class observation at every admissible
> configuration.
>
> **(iii) Censuses → theorems.** (GR-89)(iv)'s 0-failure record (96 930
> stratum + 2 114 `n = 8` + 371 `n = 10` parity-optimal configurations) and
> the greedy descent's 0-stall record at `n ≤ 10` are implied outright;
> *Step G108*(v)'s `n_hub = 8`, `2k = 2` hunt cell is **provably empty**
> (a failure needs `n ≥ 12`), so its cap disclosure can be retired.
>
> **(iv) (b′) at the constant 2, restricted.** With one cheap step from
> (GR-C1)'s parity-optimal `|δ| ≤ 2` configuration (price `≤ 2` by
> (GR-86)): `d_adm(M) − d_par(M) ≤ 2` **modulo (GR-C1) alone at every
> `n ≤ 10`**, hence — (GR-C1) being a theorem at `n ≤ 6` by (GR-69) — a
> **full theorem on the whole stratum**, where the landed per-matching gap
> histogram `{0: 23 444, 2: 495}` ((GR-70)(ii), cited) shows the constant
> 2 is exact. Its confidence is the chain's weakest link, which is
> (GR-86)(iii)/(iv)'s own landed status (the degenerate chain
> coincidences machine-checked — exactly the qualifier *Step G119*
> records for the constant-4 theorem).

*Proof.* (i) (GR-99)(ii) supplies `≥ |δ|` feasible majority flips;
(GR-100)(iii) caps the doubly-blocked majority branches (a superset of the
feasible doubly-blocked **matching** ones) at `⌊(n − 2|δ|)/4⌋`; a feasible,
not-doubly-blocked-matching branch is cheap by definition. (ii)–(iv) are
arithmetic and the citations named. ∎

**A landed inference CORRECTED, scoped exactly (the *Step G56*/*G60*/*G118*
marker precedent; it touches no measurement and no landed conclusion is
false).** *Step G108*(v), *Step G109* residual item 1 and (GR-89)(iv)'s
confidence row all read *"(GR-89)(iii) proves (GR-C2) below
`n = 3k + 5|δ|/2`"*. As stated that inference is **incomplete**: a (GR-C2)
failure makes every **feasible** majority branch a doubly-blocked matching
branch, while (iii)'s hypothesis needs **every** majority branch to be one —
and pre-(GR-99) nothing bounded the infeasible remainder (post-(GR-99) the
two readings coincide only at `b = 0`, which rigorizes exactly the
`2k = 2` cell of *Step G108*(v) and nothing else). Every conclusion drawn
from the inference is nevertheless **true**, by (GR-101)(ii) — with the
correct feasible-only hypothesis and a boundary (`6|δ|`) that is *larger*
than the one claimed. Nothing downstream moves.

---

### Step G122 — (GR-102): the stall tax — a stalled configuration is expensive, so stalls live only at matchings with large `d_par(M)`

> **(GR-102)** *(proven; asserted at every (configuration, matching)
> instance of `--sel`'s four legs and every configuration of `--bnd`'s
> full-cube audits, 0 violations, with equality realized at the (GR-103)
> witness)*
>
> **(i) The tax.** At every admissible `z` and every perfect matching `M`,
> > `dist(z, M) ≥ |a_M − b_M + δ|`.
>
> **(ii) Stall localization.** At a stalled configuration with majority A,
> every feasible majority branch lies in `M` (A-coloured), so
> `a_M ≥ f₀ ≥ |δ|` (the last by (GR-99)(ii)), and
> > `dist(z, M) ≥ f₀ + |δ| − b_M ≥ 2|δ| − b_M`.
>
> A **stalled parity-optimal** configuration therefore needs
> `d_par(M) ≥ 2|δ| − b_M` — at `2k = 2`, `|δ| = 2`: `d_par(M) ≥ 4`.

*Proof.* (i) Let `μ := #{v : m_v = 1} = 2a_M + e_M` (hubwise count of
`M`-side A-darts, branchwise: two per A-odd, one per even, none per B-odd
matching branch) and `ν := |N₁| = n/2 − δ` ((GR-100)(i)), and
`t := #{v ∈ N₁ : m_v = 1}`. The deviation set is
`S = {v : α(v) = 2, m_v = 1} ⊔ {v : α(v) = 1, m_v = 0}` (in *Step G104*'s
notation `A(v) = α(v) − m_v`), so `dist = (μ − t) + (ν − t) ≥ |μ − ν|`, and
`μ − ν = 2a_M + e_M − n/2 + δ = a_M − b_M + δ` by `e_M = n/2 − a_M − b_M`.
(ii) Substitute `a_M ≥ f₀ ≥ |δ|`, `b_M ≤ b`. ∎

*(Possible overlap, recorded: (i) is a per-pattern floor on `dist(·, M)`
and may re-express (GR-44)'s anchored-weight layer at a fixed pattern; left
as its own statement — it is consumed here only as the input to (ii)'s
localization.)*

---

### Step G123 — (GR-103): the boundary is TIGHT — an explicit `n_hub = 12` habitat witness, parity-optimal, at which every feasible majority branch is a doubly-blocked matching branch — and what survives it

> **(GR-103)** *(refutation by explicit, habitat-gated, independently
> re-checkable witness; three further seeded witnesses (7 candidate shapes
> from 400 tries, cap disclosed); full `2^{18}` cube audits at three
> witness (shape, matching) pairs; `--bnd`)*
>
> **(i) The witness.** The `n_hub = 12` shape (gated by
> `cflank.cubic_habitat`, excess 6, `2k = 2`)
> > `specs = [(0,4,2), (4,1,2), (1,5,2), (5,2,2), (2,6,2), (6,3,2), (3,7,2), (7,8,2), (8,9,4), (9,10,2), (10,11,4), (11,0,2), (0,1,3), (2,3,3), (4,8,2), (5,9,2), (6,10,2), (7,11,2)]`
>
> (the 2-factor `F` is the 12-cycle `0,4,1,5,2,6,3,7,8,9,10,11`; the two
> **odd** branches are `γ₁ = (0,1)`, `γ₂ = (2,3)`), with the perfect
> matching `M = {γ₁, γ₂, (4,8), (5,9), (6,10), (7,11)}` (branch indices
> `{12, …, 17}`) and the admissible configuration
> > `z = [1,0,1,0,1,0,1,1,1,1,1,0,0,0,1,1,1,0]`
>
> (the all-A pattern, `δ = 2`; every even branch delivers its A-dart off
> `U = {0,1,2,3}`, in-load exactly 2 elsewhere — the (GR-100)-extremal
> profile, `|N₁| = 4` tight). At `z` **both** majority branches are
> feasible ((GR-99)'s `b = 0` corner, oracle-asserted) **and both are
> doubly-blocked matching branches**: zero cheap branches. Moreover
> `dist(z, M) = 4 = d_par(M)` — the witness is **parity-optimal**, meeting
> (GR-102)'s tax floor with equality.
>
> **(ii) What it refutes.** The **per-configuration** form of (GR-C2) —
> *every parity-optimal `|δ| = 2` configuration carries a cheap majority
> branch* — is **FALSE from `n_hub = 12`**, and with (GR-101)(ii) the
> boundary `n = 6|δ|` is **exact in both directions**. The every-step
> variant (*Step G119*'s residual gloss, spec-named as the route to
> `2·min(k, ⌊n/4⌋)` at every `n`) dies with it.
>
> **(iii) What survives, measured.** At all three audited pairs (the
> constructed witness and two seeded ones): `d_par(M) = d_adm(M) = 4` —
> **per-matching gap 0** — with 160/200/68 *balanced* parity-optimal
> configurations, 104/72/52 parity-optimal `|δ| = 2` ones of which exactly
> **4 stalled each**, and the stalled configurations' exact majority
> one-flip prices are **`[0, 0]`**: the doubly-blocked flips are FREE
> there. **(GR-C2) as posed — the existential over parity-optimal
> configurations — HOLDS at every audited pair**, twice over (cheap-
> carrying optima exist in bulk, and balanced optima make the gap 0
> without any flip).
>
> **(iv) What the counting still localizes** (the spec's question). Any
> per-configuration failure needs `n ≥ 6|δ|` ((GR-101), sharper than
> (GR-89)(iii)); any **stalled parity-optimal** configuration needs
> `d_par(M) ≥ 2|δ| − b_M` ((GR-102)); at `n = 12`, `2k = 2` the stalled
> configurations are **exactly** the (GR-100)-extremal profile (capacity
> met with equality, `|N₁| = 2f₀`), which is why they are rare (4 per
> pair) and expensive. The proven constant-4 chain ((GR-99) + (GR-86) +
> (GR-69)(iii)) is untouched.

*Construction check (hand-verifiable, machine-asserted).* At `z`: each of
the four `γ`-ends has its lone A-dart on its `γ` (both `F`-darts B), so both
`γ`'s are doubly blocked; every other hub has two A-darts, so
`|N₁| = 4 = n/2 − δ` ✓. `dist = 4`: the deviation set is exactly the four
delivery ends `{7, 8, 9, 10}` of the even matching branches.
Parity-optimality and the flip prices are cube-computed (`--bnd`), not
argued. ∎

---

### Step G124 — (GR-104): the reshaped residual — the PRICE form of the selection clause — the descent interpolation, and the hand-off

> **(GR-104)** *(the reshaped residual, minted; its `n ≤ 10` half proven,
> its `n ≥ 12` half measured at the three audited pairs; the
> interpolation proven)*
>
> **(i) The price form.** *At some parity-optimal configuration with
> `|δ| ≤ 2` — balanced ones qualifying vacuously — some majority-side flip
> has `f(p + χ_γ) ≤ f(p) + 2`.* This is what the constant 2 actually
> consumes ((GR-C2) was only ever its sufficient certificate, via
> (GR-86)); it is a **theorem at `n ≤ 10`** (by (GR-101)(ii) + (GR-86)),
> and at the three audited `n = 12` stall pairs it holds with **price 0
> at the stalled configurations themselves**. It strictly relaxes
> (GR-C2): a doubly-blocked matching branch is allowed if its two repair
> chains happen to price `≤ 0`.
>
> **(ii) The descent interpolation.** From the cheapest parity-optimal
> start (`δ_M := min |δ|` over parity-optimal configurations), each
> descent step at current imbalance `d` is cheap when `n < 6d`
> ((GR-101)(ii)) and prices `≤ 4` otherwise ((GR-86) + (GR-99)), so
> > `d_adm(M) − d_par(M) ≤ δ_M + 2·min(δ_M/2, ⌊n/12⌋)`,
>
> unconditional in everything but `δ_M`. With the same (GR-69)(iii)
> input (GR-89)(ii) consumes (`δ_M ≤ 2·min(k, ⌊n/4⌋)`), this improves the
> landed `n`-free chain whenever `δ_M/2 > ⌊n/12⌋`: the gap is `≤ δ_M` for
> `n ≤ 11` (row 5's constant `2·min(k, ⌊n/4⌋) ≤ 6` **outright** at
> `n ≤ 10`), `≤ δ_M + 2` for `n ≤ 23`, `≤ δ_M + 4` for `n ≤ 35`, and
> `≤ 2δ_M ≤ 12` only from `n = 36` (at the habitat's `2k ≤ 6`).
>
> **(iii) The residual, in successor order.**
> 1. **The price form (i) at `n ≥ 12`** — the whole remaining gap between
>    the proven constant 4 and (b′)'s 2. A refutation now needs a
>    (shape, M) whose parity-optimal configurations are ALL unbalanced
>    and ALL price-stalled — (GR-102) forces `d_par(M) ≥ 2|δ| − b_M` at
>    such a pair, and none of the three audited pairs comes close (all
>    have balanced optima in bulk). The `n = 12`, `2k = 2` stall pairs
>    are the adversarial control the hunt should grow from.
> 2. **(GR-C1) past the stratum** — unchanged (GPSA's first clause;
>    (GR-69) is its exact `n ≤ 6` boundary).

---

### Verification (Steps G120–G124)

`notes/scripts/w4/gcheap.py` (**new with this pass**; imports — all
read-only — the moved balance layer **directly from `gridbal_common`**
(`branches_at`, `feas_flip`, `feasible_at`, `imb_of`, `odd_idx`,
`seeded_shapes`, `stratum_cases`, `v8_specs`; the 2026-08-25 move-down, not
the sibling re-exports), plus `gbal` (`assign_feasible`, `z_admissible`,
`z_of_orientation`, `z_pattern`, `z_to_map`), `gdesc` (`majority_of`),
`gflow` (`adm_cube`, `block_ends_at`, `f_layers`), `gorient`
(`perfect_matchings`), `cflank` (`cubic_habitat`)). **Rank-free**:
`gexist.fully_good_rank` is never imported or called and no `d_fg` claim is
made anywhere. Local devices, none shadowing a §1 primitive (checked against
the README index and the *Divergences* table): `lone_hubs` (the identity's
count, read off the cube's majority map `c`), `maj_data` (the per-
configuration majority blocked-end census), `cheap_of` (*Step G108*(iv)'s
cheap list at one (configuration, matching), feasibility cached per
pattern), `tight_specs`/`tight_z` ((GR-103)(i)'s construction), `audit_pair`
(the full-cube parity audit), `legs`, `hist`. Exact integers over GF(2)
throughout; no floating point; rngs seeded per mode with the seed printed;
no `set` iteration printed. **No pool is new**: the stratum is
`stratum_cases` (EXHAUSTIVE), V8 is `v8_specs`, the seeded `n = 8/10/12`
pools are `seeded_shapes` (= `balb.rand_habitat` behind the (GR-25) cut
criterion, tries 200/90/400, seeds printed); the one new *shape* is
(GR-103)(i)'s constructed witness, gated by the canonical `cubic_habitat`
before any claim is made on it.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --cap       # ~15 s (GR-100): identity + capacity at 449446 configurations, 4 legs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --sel       # ~18 s (GR-101)/(GR-102): cheap bound + stall tax at 874244 (configuration, matching) instances
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --bnd       # ~5 s  (GR-103): the n = 12 witness, the seeded hunt, three full-cube parity audits
PYTHONHASHSEED=0 python3 notes/scripts/w4/gcheap.py --validate  # ~40 s all three in one process
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-100)(i) the identity | `--cap` | `#{v : c(v) = B-majority} == n/2 − δ` (and the B-side twin) asserted at every admissible configuration of every leg — 449 446 configurations, the stratum cube EXHAUSTIVE |
| (GR-100)(ii) the injection | `--cap` | per hub: every blocked end of a majority branch asserted to be a lone-majority-dart hub, and the hub list asserted repeat-free, at all 154 750 unbalanced configurations |
| (GR-100)(iii) the capacity | `--cap` | `Σ blocked ends ≤ n/2 − \|δ\|` and `#doubly-blocked ≤ ⌊(n − 2\|δ\|)/4⌋` asserted per configuration; the attainment count printed per leg |
| (GR-100) capacity is exact | `--cap` | F13 control: gap 0 attained on **every** leg, so the doctored bound (capacity − 1) fails there |
| (GR-100)(iv) `n ≥ 6a − 2b` | — | arithmetic corollary of (iii) at total blocking; not separately driver-testable (its hypothesis is provably empty on every swept leg — that emptiness IS (iii)'s assert) |
| (GR-101)(i) the cheap bound | `--sel` | `#cheap ≥ \|δ\| − ⌊(n − 2\|δ\|)/4⌋` asserted at all 874 244 unbalanced (configuration, matching) instances; minimum slack printed: **0 on every leg** (tight) |
| (GR-101)(ii) every-step (GR-C2) at `n < 6\|δ\|` | `--sel` | `#cheap ≥ 1` asserted whenever `n < 6\|δ\|` — every instance of every leg qualifies; a NEW quantifier (all unbalanced configurations; the landed censuses are parity-optimal-only and are cited, not re-run) |
| (GR-101)(ii) capacity 0 on the stratum | `--sel`, `--cap` | the feasible-doubly-blocked-matching histogram: `{0: 701 382}` on the stratum; `--cap`'s doubly-blocked histogram `{0: 137 202}` |
| (GR-99)(ii) consumed | `--sel` | `#feasible majority ≥ \|δ\|` re-asserted at every instance (corroboration of the landed theorem, not a re-proof) |
| (GR-102)(i) the stall tax | `--sel`, `--bnd` | `dist ≥ \|a_M − b_M + δ\|` asserted at every (configuration, matching) instance and at every configuration of the three full-cube audits; equality realized at the (GR-103) witness |
| (GR-103)(i) the witness | `--bnd` | `cubic_habitat` gate, admissibility, `δ = 2`, both majority branches doubly-blocked matching branches, both flips oracle-feasible, 0 cheap, `dist = 4 = d_par(M)` — each a separate assert; the shape, matching and `z` printed for independent re-verification |
| (GR-103)(iii) the audits | `--bnd` | full `2^{18}` cube at three (shape, matching) pairs: `d_par`, `d_adm`, the balanced/unbalanced parity-optimal counts, the stall counts, the stalled one-flip prices `[0, 0]` — printed, and the as-posed verdict computed from them |
| (GR-103) more witnesses exist | `--bnd` | the seeded hunt: 7 candidate shapes from 400 tries (CAP disclosed), 3 further witnesses, each with the same asserts |
| (GR-104)(i) at `n = 12` | `--bnd` | the stalled prices `[0, 0]` (measured, three pairs — NOT a theorem) |
| (GR-104)(ii) the interpolation | — | arithmetic from (GR-101)(ii) + (GR-86) + (GR-99); its `n ≤ 10` collapse is `--sel`'s every-step assert |
| landed denominators reproduced | `--sel`, `--cap` | 23 939 stratum (shape, matching) pairs and 701 382 unbalanced instances — equal to gflow's landed figures, from an independent construction |
| (a′) / `d_fg` / input (Y) / (GR-15) | — | **not attempted**; no mode computes a rank |

**Determinism.** `--validate` run at `PYTHONHASHSEED` 0 and 999:
byte-identical except the `[Ns]` wall-clock annotations. Every seeded leg
prints its seed.

**Caps, disclosed in full — an exhausted cap is not a proof of
nonexistence.** (1) Only the `n_hub ≤ 6` stratum is exhaustive (full
`2^{|E|}` cube per shape, all perfect matchings); V8 is one shape, its cube
complete but its matchings capped at 6 in `--sel`. (2) The `n = 8/10` legs
are seeded samples (tries 200/90), matchings capped at 6 per shape
(13/23 shapes capped, printed). (3) The `n = 12` hunt is a seeded sample
(400 tries → 7 shapes at `2k = 2`); the three full-cube audits are complete
**at those (shape, matching) pairs only** — the as-posed form at `n ≥ 12`
is measured there and nowhere else, and its OPEN status does not move on
this evidence. (4) No search caps exist in any assertion path.
**None of these caps qualifies (GR-100)–(GR-102) or the (GR-103)(i)–(ii)
refutation** — those are proofs and an explicit witness; the caps qualify
only the machine cross-checks and the (GR-103)(iii)/(GR-104)(i)
measurements.

**Scratch probes (README's standing rule).** None were run: the constructed
witness was derived by hand from (GR-100)'s extremal profile and entered the
driver directly as `tight_specs`/`tight_z`; every figure quoted above is
produced by `gcheap.py`.

---

### Confidence verdict (Steps G120–G124)

| | claim | standing |
|---|---|---|
| **(GR-100)(i)** | the lone-dart identity `\|N₁\| = n/2 − δ`; `\|δ\| ≤ n/2` | **proven** (four lines off (GR-49) and cubicity); asserted at 449 446 configurations |
| **(GR-100)(ii)/(iii)** | the blocked-end injection and capacity `⌊(n − 2\|δ\|)/4⌋` | **proven**; asserted at 154 750 unbalanced configurations, attained on every leg |
| **(GR-100)(iv)** | total blocking forces `n ≥ 6a − 2b` | **proven** (strictly sharpens (GR-89)(iii), which stays true) |
| **(GR-101)(i)** | `#cheap ≥ \|δ\| − ⌊(n − 2\|δ\|)/4⌋`, every configuration, every matching | **proven** ((GR-100) + (GR-99)(ii) consumed); tight (slack 0) on every leg |
| **(GR-101)(ii)** | **every-step (GR-C2) for `n < 6\|δ\|`** — all of `n ≤ 10` at `\|δ\| = 2` | **PROVEN** — the graded outcome of the third kind, with the boundary exact by (GR-103); the landed 0-failure censuses are explained, not extended |
| **(GR-101)(iv)** | per-matching (b′) at the constant 2 | **THEOREM on the whole `n ≤ 6` stratum**; theorem modulo (GR-C1) alone at `n = 8, 10` |
| the corrected inference | "(GR-89)(iii) proves (GR-C2) below `3k + 5\|δ\|/2`" | **incomplete as landed** (feasible-only vs all-majority hypothesis); every conclusion re-proven true by (GR-101); a prose scoping correction, no measurement moves |
| **(GR-102)** | the stall tax; stalls need `d_par(M) ≥ 2\|δ\| − b_M` | **proven**; asserted everywhere swept; possible overlap with (GR-44) flagged for the coordinator |
| **(GR-103)(i)/(ii)** | the **per-configuration form of (GR-C2) is REFUTED from `n_hub = 12`**, by a named, habitat-gated, parity-optimal witness; `n = 6\|δ\|` exact | **refuted by witness** — the spec's second graded outcome, at the first counting-permitted cell |
| **(GR-103)(iii)** | the as-posed existential survives; gap 0; stalled flips price 0 | **measured** (three full-cube audits) — evidence, not proof |
| **(GR-104)(i)** | the price form — the reshaped residual | **minted**: theorem at `n ≤ 10`, measured intact at `n = 12`, OPEN beyond |
| **(GR-104)(ii)** | `d_adm − d_par ≤ δ_M + 2·min(δ_M/2, ⌊n/12⌋)` | **proven** (improves (GR-89)(ii)'s chain for `n < 12·δ_M/2`; row 5's constant outright at `n ≤ 10`) |
| **(GR-C2) as posed** | | **proven at `n ≤ 10`; OPEN at `n ≥ 12`** — no longer the right residual: (GR-104)(i) supersedes it as the successor target |
| (GR-49)–(GR-51), (GR-86), (GR-89), (GR-99) | | **untouched and consumed**; gflow's stratum denominators independently reproduced |
| **(a′)** / input (Y) / (GR-64) rows / **(GR-15)** | | **OPEN — not attempted**; no rank computed anywhere; no flank; no class-uniformity claim |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as GBAL's through GFLIP's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos) (AC-9));
the only samplers draw **graphs**, not placements.

### What would change this (Steps G120–G124)

*(i)* **An error in (GR-99)(ii)** would void (GR-101)/(GR-104)'s feasibility
supply — it is however a landed proven theorem, certified independently
here at 874 244 instances. *(ii)* **A stalled parity-optimal pair with no
balanced optimum and all `|δ| = 2` optima price-stalled** refutes the price
form (GR-104)(i) and with it the constant-2 route; (GR-102) confines such a
pair to `d_par(M) ≥ 2|δ| − b_M`, and the three audited pairs are nowhere
near. *(iii)* **A proof of (GR-104)(i)** closes (b′) at the constant 2
modulo (GR-C1) at every `n` — the audits suggest the stalled configurations'
chain pairs may *always* price `≤ 0` at optimality, and why is the open
mechanism question. *(iv)* **The `Λ ≠ ∅` / `D > 0` lifts** stay unswept by
standing rider; (GR-100) uses cubicity (three darts per hub) and `M` perfect
throughout, so a `D > 0` lift must redo it. *(v)* **A Lean transcription**
of (GR-100)–(GR-102) would be small (finite dart counting on a multigraph);
nothing here pins a carrier beyond what (GR-49)–(GR-51) already pin.

**TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator
re-runs it.**

- **(E1) NOT FIRED.** No g-flank; the pass is rank-free and computes no
  rank, so clauses (i)–(iv) cannot fire. Clause (v) (`d_adm = ∞`) fires on
  nothing: every audited pair has finite `d_adm` (printed), and the swept
  legs consume (GR-54) unchanged.
- **(E2) NOT FIRED.** Entry 5 is PROVEN ((GR-54)) and consumed untouched.
  The route demoted here — (GR-C2) as the constant-2 certificate beyond
  `n = 10` — is demoted **with its successor named in place**
  ((GR-104)(i), plus the proven `n ≤ 10` half), which is the retained
  carve-out; no board entry loses a route without a successor.
- **(E3) ARMED (by GBAL), DOES NOT FIRE, and this direction does not fire
  it.** E3 fires only on a HIT completing **entry 1** — i.e. (a′). This
  pass does not attempt (a′), computes no rank, and makes no `d_fg` claim.
  The HITs here are on **(b′)'s selection layer** ((GR-C2) settled
  per-configuration in both directions, (b′) at the constant 2 a stratum
  theorem), which is not entry 1 and arms nothing. **Firing is a
  coordinator action; reported, not fired.**

---

### Steps G125–G129 (2026-08-25, direction GPRICE) — **(GR-104)(i) is RESHAPED at the boundary stratum, with everything around the reshaping proven**: **(GR-105)** is the **colour-swap identity at the `f`-layer** — the global bit-complement `z ↦ 1 ⊕ z` is a dist-preserving admissibility involution at EVERY perfect matching, so `f(p) = f(p̄)` for every pattern and in particular the two majority one-flip prices at a `2k = 2` stall are **equal** ((GR-103)(iii)'s measured `[0, 0]` symmetry explained in one line); **(GR-106)** is the **reversal-set normal form** — at any matching with ALL odd branches inside `M` (the only cell a (GR-104)(i) failure can occupy at `2k = 2`), an admissible configuration is EXACTLY a set `R` of reversal hubs meeting every `F`-cycle evenly, labelled sink/source alternately, with no even matching pair mono-labelled and each A-end a source / B-end a sink, and `dist(z, M) = n − |R|` — making `f(p)` computable in `2^n` instead of `2^{3n/2}` (cube-asserted at 1 054 pairs, reaching `n = 18` where the cube stops at 12); **(GR-107)** is the **reachability theorem** — the patterns at which one reversal set stays valid form an affine subspace `p ⊕ L`, `L` spanned by end-free branches and block flips, giving the exact obstruction to price `≤ 0` (the flip branch γ-**linked** through a component chain) and the **2k = 2 reduction**: (GR-104)(i) at `2k = 2` holds **outright when some odd branch is off `M`**, and otherwise follows from **(GR-108)**; **(GR-108)** is the minted **BALANCE LAW** — *at every `O ⊆ M` matching, `d_par(M)` is attained at a balanced pattern* — measured with **0 violations at all 1 431 swept pairs** (the stratum sub-cell EXHAUSTIVE at 1 034, the (GR-103) control, seeded `n = 8/10/12`, and a new cell-targeted sampler to `n = 18`, `2k ∈ {2, 4}`), its **strong form** (every maximum reversal set reaches balance) proven-by-exhaustion on the stratum and **failing from exactly `n = 12`** (65/101 at the (GR-103) control) — so a proof must exchange between maximum reversal sets, and the failure boundary coincides with (GR-101)'s; **(GR-109)** the status: **(GR-104)(i) is a THEOREM at `2k = 2`, every `n`, modulo (GR-108) alone**, the refutation hunt is EMPTY to `n = 18` under disclosed caps, and the residual is (GR-108) plus the `2k ∈ {4, 6}`, `O ⊄ M` corner. **(GR-15) stays OPEN, no gap-map status move on `hK` itself; E3 stays ARMED and does NOT fire.**

Answering `notes/Pencil-fanout.md` §"GPRICE — thirty-third ordinal": **prove,
refute by witness, or settle under a restricted quantifier the price form
(GR-104)(i)**. **The outcome is the third kind, with the restriction exactly
named**: the price form is **proven on the whole `2k = 2` stratum at every
`n` modulo one minted law** ((GR-108), the balance law), whose own standing
is *measured* (1 431/1 431, the `n ≤ 6` sub-cell exhaustive) — and the
refutation object the spec names (a pair with all parity-optimal
configurations unbalanced and all price-stalled) is **not found**: every
swept `O ⊆ M` pair, at every `n ≤ 18` reached, has a **balanced**
parity-optimal configuration outright. Rank-free throughout: nothing imports
or calls `gexist.fully_good_rank` and no `d_fg` claim is made anywhere
((a′) / input (Y) untouched). Read against *Steps G104–G109*
((GR-85)–(GR-90)), *Steps G116–G119* ((GR-97)–(GR-99)) and *Steps G120–G124*
((GR-100)–(GR-104)).

**Where the offered mechanism question lands.** *Step G124*'s
what-would-change-this (iii) asked *why* the stalled configurations' repair
chains price `≤ 0` at parity-optimality. The answer this pass finds is that
the question dissolves one level up: at every `O ⊆ M` pair ever swept, a
**balanced** pattern already attains `d_par(M)` — the stalled `|δ| = 2`
optima are never the *only* optima — and the observed price 0 is forced by
that plus (GR-105) (`f(p + χ_{γ₁}) = f(p + χ_{γ₂})`, and each is trapped in
`[d_par, d_par + 4]` with the balanced value `d_par` available). The open
mechanism is re-aimed at the balance law itself, whose exact obstruction
family (GR-107) names.

***Notation, inherited unchanged, with two deliberate new terms.*** `δ`,
`O`, `H`, `M`, `F = G° ∖ M`, `z`, colour **0 = A**, `m(v)`, blocked ends,
`d_par(M)`, `d_adm(M)`, `f(p)` (= the minimum of `dist(·, M)` over
admissible configurations at odd pattern `p`) — all as at *Steps G104–G109*;
`α(v)` (all-three-dart A-count) as at *Steps G120–G124*. **New:** at an
`O ⊆ M` pair, a hub `v` is a **reversal hub** of `z` iff its two `F`-darts
are equal-coloured — a **sink** (both A, i.e. `A(v) = 2`) or a **source**
(both B, `A(v) = 0`); `R(z)` is the set of reversal hubs. `p̄` is the
pattern with every odd branch's colour flipped. An **end** is a hub of an
odd (matching) branch; all other hubs are **inner** (their matching branch
is even).

**Step 0 pin (mandatory, discharged before any derivation).** (GR-49)
(admissibility, one bit per branch, `α(v) ∈ {1, 2}`). (GR-50)/(GR-51)
consumed as the feasibility oracle. (GR-85) in full — `A(v)`, the
`dist = #{v : A(v) = 1}` objective, the three local matching conditions,
the free even-`M` bit. (GR-86) in full (the repair-chain price ledger:
cheap `⟹ ≤ 2`, doubly-blocked matching `⟹ ≤ 4`). (GR-89)(iv) (cheap,
(GR-C1)/(GR-C2)), (GR-99)(ii) (`≥ |δ|` feasible majority flips — consumed
as the feasibility supply, exactly as (GR-101) consumed it), and
(GR-100)–(GR-104) in full ((GR-103)(i)'s printed witness re-entered for
independent reconstruction, its landed audit figures asserted as a control,
not re-derived). **Bars honoured:** (GR-C1) not attacked (consumed as a
hypothesis exactly where (GR-104) consumes it); (GR-R1)/(GR-99), (GR-C2)'s
settled halves, (GR-103)'s refutation all consumed, none re-attacked or
repaired; (GR-49)–(GR-54), (GR-67)–(GR-72), (GR-85)–(GR-90),
(GR-97)–(GR-104)'s landed parts not re-derived; no landed census or
full-cube audit re-run — the driver's sentences quantify over the **new**
`O ⊆ M` (shape, matching) cell decomposition and over new `n = 14/16/18`
pools, and every landed figure is cited, not re-measured; (GR-15) / class
uniformity untouched; no `.lean` touched (the standing Lean hold).

---

### Step G125 — (GR-105): the colour-swap identity at the `f`-layer — `f(p) = f(p̄)` at every matching, so a `2k = 2` stall's two majority prices are EQUAL

> **(GR-105)** *(proven, one line off (GR-49); asserted at every pattern of
> every `O ⊆ M` pair of every leg — 1 431 pairs; `--cell`, `--seed`,
> `--hunt`)*
>
> Let `M` be ANY perfect matching and `p` any feasible odd pattern. The
> global bit-complement `z ↦ 1 ⊕ z` (flip every branch bit) maps the
> admissible configurations at `p` bijectively onto those at `p̄`, and
> **preserves `dist(·, M)`**. Hence
> > `f(p) = f(p̄)` for every pattern, and the `f`-spectrum is symmetric
> > under `δ ↦ −δ`.
>
> **Corollary (the `[0, 0]` symmetry).** At `2k = 2` the two balanced
> patterns are each other's complements, so the two majority one-flip
> prices from an unbalanced pattern are **equal**:
> `f(p + χ_{γ₁}) = f(p + χ_{γ₂})`. (GR-103)(iii)'s measured stall prices
> `[0, 0]` could never have been `[0, 2]`.

*Proof.* Complementing every bit flips both darts of every branch, so each
hub's dart colour vector complements: `α(v) ↦ 3 − α(v)`, and `{1, 2}` is
complement-closed — admissibility is preserved. The minority dart is the
colour appearing once; complementing the 2–1 split leaves the **same
branch** carrying the singleton, so `m(v)` is unchanged hub by hub, and
`dist(z, M) = #{v : m(v) ≠ M(v)}` is preserved exactly. The odd pattern
maps to `p̄`; the map is an involution. ∎

*(This is (GR-100)(i)'s "by colour swap" read one layer up — at the
`f`-layer rather than the identity layer; recorded because the price
symmetry it forces was left as a measured curiosity at *Step G123*.)*

---

### Step G126 — (GR-106): the reversal-set normal form at `O ⊆ M` — an admissible configuration IS an alternating sink/source set, `dist = n − |R|`, and `f` is computable in `2^n`

**Why this cell.** At `2k = 2` a (GR-104)(i) failure can only live at a
matching containing **both** odd branches: at any `|δ| = 2` optimal pattern
both majority branches are feasible ((GR-99)(ii), `a = 2`), and a feasible
majority branch off `M` is **cheap** by definition, pricing the flip `≤ 2`
at any optimal configuration ((GR-86)) — see (GR-107)(iii). So the open
territory is exactly the `O ⊆ M` pairs, where the 2-factor `F` is
**all-even** and the following exact model exists.

> **(GR-106)** *(proven; asserted `f`-value-by-`f`-value against the landed
> full-cube `f` (`gflow.adm_cube` + `f_layers`) at **1 054** (shape,
> matching) pairs — the stratum sub-cell EXHAUSTIVE, V8, the (GR-103)
> control, seeded `n = 8/10/12`; `--cell`, `--seed`)*
>
> Let `M` be a perfect matching with `O ⊆ M`, `F = G° ∖ M` the all-even
> 2-factor. For admissible `z` let `R(z)` be its reversal hubs (sinks
> `A(v) = 2`, sources `A(v) = 0`; every other hub has `A(v) = 1`). Then:
>
> **(i) Alternation.** `R(z)` meets every `F`-cycle in an even set, and
> sinks and sources alternate in each cycle's cyclic order.
>
> **(ii) The matching exclusions.** No even matching branch has both ends
> sinks, and none has both ends sources.
>
> **(iii) The end forcings.** An end of an **A**-coloured odd branch lying
> in `R(z)` is a **source**; an end of a **B**-coloured one is a **sink**.
> (Ends off `R(z)` are unconstrained.)
>
> **(iv) The distance identity.** `dist(z, M) = n − |R(z)|` **exactly**.
>
> **(v) Completeness.** Conversely, every labelled set `R` satisfying
> (i)–(iii) arises from an admissible configuration with pattern `p`; the
> fibre over `(R, labels)` is exactly the free orientations of the even
> matching branches with both ends off `R` ((GR-85)(iii)'s free bit).
>
> **(vi) The algorithm.** Hence `f(p) = n − max{|R| : R satisfies
> (i)–(iii) for p}`, computable by a `2^{n}`-enumeration with a linear
> validity check — independent of branch lengths, and reaching `n = 18`
> where the `2^{3n/2}` cube stops at `n = 12`.

*Proof.* Orient each even branch toward the end receiving its A-dart; odd
branches (all in `M`) deliver nothing. Each hub has exactly two `F`-darts,
both on even branches, so `A(v) = ` its `F`-in-degree `∈ {0, 1, 2}`, and
`Σ_v A(v) = |F| = n`. On one `F`-cycle, a hub with `A(v) ∈ {0, 2}` is
exactly a point where the walking direction reverses; reversal points are
even in number and alternate in–in (sink) / out–out (source) — (i), and
conversely any even alternating set is realized by orienting each arc
between consecutive reversal points consistently. Admissibility
(`α(v) = o_v + indeg(v) ∈ {1, 2}`, (GR-49)): at an **inner** hub, `o_v = 0`
and the matching branch can deliver, so `indeg ∈ [1, 2]` forces: a source
(`F`-in 0) must receive its matching dart — excluding a source partner at
the far end, since the branch delivers to only one end — and a sink
(`F`-in 2) must not receive it — excluding a sink partner, since the
branch must deliver to one end; a (source, sink) or (·, through) pair is
realizable with the delivery direction forced, and a (through, through)
pair leaves the bit free — (ii), (v).
At an **end**, the matching branch is the odd `γ`: an A-`γ` supplies one
A-dart (`o_v = 1`), so `α ≤ 2` forbids `F`-in 2 (sink) and `α ≥ 1` allows
`F`-in 0 (source); colour-swapped for B — (iii). For (iv): at a through
hub the two `F`-darts differ, so the minority dart is on an `F`-branch
`≠ M(v)` — deviating; at a sink the darts are (A, A, B-on-`M`) (the
matching dart is B by (ii)'s delivery arithmetic, or the odd branch is
B-coloured by (iii)), so `m(v) = M(v)` — not deviating; colour-swapped at
a source. Hence `dist = #through = n − |R|`. ∎

**The stall dictionary, for the record.** At `2k = 2`, pattern all-A: a
majority branch `γ = uw` is doubly blocked at `z` iff **both `u, w ∈ R(z)`
as sources**; a stalled configuration is one with all four ends sources.
(GR-103)(i)'s witness `z` is the reversal set `R = {0, 1, 2, 3` (sources)`,
4, 5, 6, 11` (sinks)`}` with `dist = 12 − 8 = 4` — the model re-derives its
whole audit row, and the driver asserts it.

---

### Step G127 — (GR-107): the reachability theorem — one reversal set serves an affine subspace of patterns, the price-`≤ 0` obstruction is a LINKAGE, and (GR-104)(i) at `2k = 2` reduces to the balance law

> **(GR-107)** *(proven; the composed criterion is what `--cell`/`--seed`
> assert against the cube at 1 054 pairs, since the driver's per-pattern
> validity check IS this theorem)*
>
> Fix an `O ⊆ M` pair and a set `R` satisfying (GR-106)(i)–(ii) whose
> labelling is encoded by the aux graph `aux(R)` — one even cycle per
> `F`-cycle through `R`'s members in cyclic order, plus an edge per even
> matching pair inside `R` — with `R` **structurally valid** iff `aux(R)`
> is bipartite and no odd branch has its two ends in one component with
> **opposite** parity classes (equal classes are required there, since both
> ends carry the same forced label). Each component `X` has two labelings (`o(X) ∈
> GF(2)`); an odd branch `γ` with a resident end `e ∈ X` must satisfy
> `colour(γ) = κ(e) ⊕ o(X)`.
>
> **(i) The affine structure.** The patterns at which `R` is valid form
> `p ⊕ L`, where `L ≤ GF(2)^O` is spanned by (a) `χ_γ` for every **free**
> branch (no end in `R`), and (b) `χ_{S(W)}` for every **block** `W` — an
> equivalence class of components under *sharing a resident branch* — with
> `S(W)` its resident branches.
>
> **(ii) Balance reachability.** With `d_W := ` the imbalance of `S(W)` at
> one orientation and `t := #free branches`, `R` reaches a balanced
> pattern iff some signing has `|Σ_W ε_W d_W| ≤ t` (the parity match is
> automatic).
>
> **(iii) The `2k = 2` reduction.** At `2k = 2`, whenever a parity-optimal
> configuration with `|δ| ≤ 2` exists ((GR-C1)'s conclusion, consumed):
> - if some odd branch is **off `M`**: (GR-104)(i) **holds outright** —
>   at a balanced optimum vacuously; at an all-A optimum the off-`M`
>   majority branch is feasible ((GR-99)(ii)) and cheap, so its flip
>   prices `≤ 2` ((GR-86));
> - if `O ⊆ M`: (GR-104)(i) **holds whenever the balance law (GR-108)
>   does** — a balanced pattern attains `d_par(M)`, and a balanced
>   parity-optimal configuration qualifies vacuously.
>
> So a (GR-104)(i) failure at `2k = 2` is exactly a failure of (GR-108)
> at an `O ⊆ M` pair — and at such a pair the failure is the statement
> `f(AB) ≥ f(AA) + 4`, since `f(AB) = f(BA)` by (GR-105) and (GR-86) caps
> the gap at 4.
>
> **(iv) The price-`≤ 0` obstruction, named.** If at some `f(p)`-optimal
> `R` the majority branch `γ` is free, or every component holding an end
> of `γ` holds no end of another odd branch, then `p + χ_γ ∈ p ⊕ L` and
> `f(p + χ_γ) ≤ f(p)` — **price `≤ 0`**. The obstruction is `γ` being
> **linked**: a chain of aux components and resident branches forcing
> `colour(γ)` equal to another branch's. At `2k = 2`: `f(AB) > f(AA)` at
> an `O ⊆ M` pair iff **every** structurally-maximum `R` is `γ₁`–`γ₂`
> linked.
>
> **(v) One repair is always affordable.** Removing an aux-cycle-adjacent
> pair from one `F`-cycle of `R` preserves structural validity (the
> shortened cyclic order keeps its 2-colouring; components only split), so
> a linkage confined to one removable pair costs `≤ 2` — the (GR-86)
> ledger's chain arithmetic recovered inside the model.

*Proof.* (i) Validity at `q` is solvability of `colour(γ) = κ(e) ⊕ o(X(e))`
over all resident ends — a linear system over GF(2) in the `o(X)` and the
`colour(γ)`; its solution set in the colour coordinates is empty or affine,
and it is nonempty (it contains `p`). The homogeneous solutions: flipping a
set of component orientations must flip each resident branch's colour
consistently, which ties together exactly the components sharing a resident
branch — the blocks — and leaves branches with no resident end free.
(ii) Choosing orientations independently per block contributes `± d_W` to
the imbalance and each free branch `± 1`; `Σ d_W + t ≡ 2k (mod 2)` makes
the parity automatic. (iii) Assembles (GR-99)(ii), (GR-86), (GR-105) and
the definitions as displayed; at `2k = 2` and `|δ| = 2` both odd branches
are majority-side, so "some odd branch off `M`" is "some majority branch
off `M`". (iv)–(v) are direct. ∎

---

### Step G128 — (GR-108): the BALANCE LAW — at every `O ⊆ M` matching a balanced pattern attains `d_par(M)`; measured with 0 violations to `n = 18`, exhaustive on the stratum sub-cell, its strong form failing from exactly `n = 12`

> **(GR-108)** *(MINTED, the reshaped residual; measured, NOT a theorem:
> 0 violations at all **1 431** swept `O ⊆ M` pairs — the `n ≤ 6` stratum
> sub-cell EXHAUSTIVE (1 034 pairs, every `O ⊆ M` matching of every
> odd-carrying shape, cube-asserted), V8's chord matching, the (GR-103)
> control pair, seeded habitat shapes at `n = 8/10/12/14`, and the NEW
> cell-targeted `(F, M)` sampler at `n = 12/14/16/18`, `2k ∈ {2, 4}`;
> `--cell`, `--seed`, `--hunt`, `--mech`)*
>
> *At every perfect matching `M` of a cubic loop-free hub multigraph with
> all odd branches inside `M`, the parity optimum is attained at a
> **balanced** pattern:* `d_adm(M) = d_par(M)`.
>
> **(i) What it says in the model.** Some structurally-maximum reversal
> set reaches a balanced pattern ((GR-107)(ii) with `M* = n − d_par`).
>
> **(ii) What was measured.** Gap histogram `{0: 1 431}` — no `O ⊆ M`
> pair with gap 2 or 4 exists anywhere swept, at any `n ≤ 18`, `2k ≤ 6`
> reached; in particular the landed stratum gap-2 pairs ((GR-70)(ii)'s
> 495) all live at `O ⊄ M` matchings. The `f`-spread across patterns is
> genuinely nonzero (up to 8 at V8) — the law is about the *minimum*, not
> pattern-independence.
>
> **(iii) The strong form, and its exact boundary.** *Every*
> structurally-maximum `R` reaches balance at **all 1 034** stratum
> pairs — but only **65 of 101** at the (GR-103) control (`n = 12`; worst
> seeded ratio 32/66): the `γ`-linked maximum family is exactly the
> stalled-optimum family and first inhabits `n = 12`, the same boundary
> (GR-101)/(GR-103) pinned. So the law is **not** a per-maximum-set fact
> from `n = 12` on: any proof must produce the balance-reaching maximum
> from a linked one — an exchange between maximum reversal sets, which is
> the exact open mechanism.
>
> **(iv) What refutes it.** An `O ⊆ M` pair at which every
> structurally-maximum `R` fails (GR-107)(ii) — at `2k = 2`: every
> maximum `R` linked with forced-equal colours. By (GR-107)(iii) that
> pair refutes (GR-104)(i) as well, and by (GR-102) it needs
> `d_par(M) ≥ 2|δ| − b_M` at its stalled optima.

---

### Step G129 — (GR-109): where (GR-104)(i) now stands, and the hand-off

> **(GR-109)** *(the status statement; no new mathematics)* **(GR-104)(i)
> is settled under a restricted quantifier with the restriction exactly
> named, and its `2k = 2` content is reshaped onto one clean law.**
>
> | statement | standing after this pass |
> |---|---|
> | (GR-104)(i) at `n ≤ 10` | **theorem** ((GR-101)(ii) + (GR-86), landed — untouched) |
> | (GR-104)(i) at `2k = 2`, any `n`, some odd branch off `M` | **PROVEN** ((GR-107)(iii), off (GR-99) + (GR-86)) |
> | (GR-104)(i) at `2k = 2`, any `n`, `O ⊆ M` | theorem modulo (GR-108) as landed; **(GR-108) since REFUTED (*Steps G135–G139*, GXESC) — the surviving route is the gap-2 law modulo the half-witness clause ((GR-117))** |
> | (GR-108), the balance law | minted and measured 1 431/1 431 as landed; **since REFUTED from `n = 16` ((GR-116), four verified witnesses outside this pool)** |
> | the spec's refutation object (all optima unbalanced ∧ all price-stalled) | **not found** — every swept `O ⊆ M` pair has a balanced optimum outright; an exhausted cap is *not found under cap*, never nonexistence |
> | (GR-104)(i) at `2k ∈ {4, 6}` | theorem at `n ≤ 10` (landed); at the `O ⊆ M` sub-cell it follows from (GR-108) wherever the law holds (measured, incl. V8); the `O ⊄ M` corner (every feasible majority branch a DBM while some odd branch sits off `M`, infeasible or minority) is **untouched and OPEN** |
>
> **The residual, in successor order.**
> 1. ~~**Prove (GR-108)**~~ — *(revised in place twice: by (GR-114),
>    Steps G130–G134, and then by (GR-119), Steps G135–G139.)*
>    **(GR-108) and existential escape are both REFUTED** ((GR-116),
>    four verified witnesses from `n = 16`); the successor is the
>    **half-witness clause** ((GR-117)(iii)): every pos-carrying
>    `O ⊆ M` pair has a maximum that is balance-valid or half-resident
>    — strictly weaker, with a proven surgical mechanism
>    ((GR-117)(ii)), and it closes (GR-104)(i) at `2k = 2`
>    unconditionally.
> 2. **The `2k ∈ {4, 6}`, `O ⊄ M` corner** of (GR-104)(i) — no landed or
>    new instrument addresses it beyond `n ≤ 10`; it needs either a
>    (GR-106)-style model with odd `F`-branches as fixed darts (the
>    reversal-point calculus survives; the colour-swap identity (GR-105)
>    survives; the alternation bookkeeping gains base offsets) or a
>    different reduction.
> 3. **(GR-C1) past the stratum** — unchanged (GPSA's first clause;
>    (GR-69) its exact `n ≤ 6` boundary).

---

### Verification (Steps G125–G129)

`notes/scripts/w4/gprice.py` (**new with this pass**, at the spec's pinned
path; imports — all read-only — the balance layer **directly from
`gridbal_common`** (`branches_at`, `imb_of`, `odd_idx`, `seeded_shapes`,
`stratum_cases`, `v8_specs`; never via the sibling re-exports), plus
`gbal.z_admissible`, `gflow` (`adm_cube`, `f_layers`), `gorient`
(`perfect_matchings`), `cflank` (`cubic_habitat`)). **Rank-free**:
`gexist.fully_good_rank` is never imported or called and no `d_fg` claim is
made anywhere. Local devices, none shadowing a §1 primitive (checked
against the README index and the *Divergences* table): `f_cycles` /
`cell_data` (the 2-factor cycle extraction), `rmodel_f` ((GR-106)(vi)'s
`2^n` computation of `f` at every pattern, with (GR-107)'s validity
criterion as the inner check), `rmodel_diag` ((GR-108)(iii)'s
maximum-family census), `cube_f` (the landed full-cube `f`, for the
cross-assert), `price_verdict` (the (GR-104)(i) sentence at one
`f`-table), `gr103_specs` ((GR-103)(i)'s **printed** witness, re-entered
for independent reconstruction and used as a control), `cell_shapes` (the
**NEW** cell-targeted sampler: draws `(F, M)` directly — random 2-factor +
random matching avoiding `F`-parallels, odd lengths placed inside `M`,
excess topped to 6 with `ℓ = 4`, `Λ = ∅` respected — each candidate gated
by the canonical `cflank.cubic_habitat` before any claim), `sweep_pair` /
`pairs_of` / `report`. Exact integers / GF(2) throughout; no floating
point; rngs seeded per mode with the seed printed; no `set` iteration
printed.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --cell      # ~5 s  (GR-105)/(GR-106)/(GR-107) asserted vs the cube: stratum EXHAUSTIVE + V8 + the (GR-103) control
PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --seed      # ~5 s  seeded n = 8/10/12 (n <= 10 all cube-asserted; n = 12 first 6)
PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --hunt      # ~53 s the refutation hunt to n = 18: seeded pool + cell-targeted pool, 2k in {2, 4}
PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --mech      # ~4 s  (GR-108)(iii): the maximum-family balance census
PYTHONHASHSEED=0 python3 notes/scripts/w4/gprice.py --validate  # ~67 s all four in one process
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-105) `f(p) = f(p̄)` | all | asserted at every pattern of every `O ⊆ M` pair, 1 431 pairs, 0 violations |
| (GR-106)(i)–(v) the normal form | `--cell`, `--seed` | `rmodel_f` (built on (i)–(iii) alone) asserted **equal to the landed cube `f`** at every pattern of 1 054 pairs — stratum EXHAUSTIVE, V8, the (GR-103) control, seeded `n = 8/10`, first 6 of `n = 12`; the criterion inside `rmodel_f` is (GR-107), so the same assert covers both |
| (GR-106) dist identity at the (GR-103) witness | `--cell` | the control re-finds `d_par = 4`, gap 0, `f = {4, 4, 4, 4}` — (GR-103)(iii)'s landed row, asserted |
| (GR-104)(i) at every swept pair | all | `price_verdict`: 'vacuous' or min flip price `≤ 2` at 1 431/1 431; the `REFUTATION` counter (any strict pair with all flips `≥ 4`) is **0** and any hit would print the full (shape, matching, `f`-table) |
| (GR-108) the balance law | all | gap histogram `{0: 1 431}` — the sentence *some balanced pattern attains `d_par`* asserted per pair in `--mech`'s legs, measured in the rest |
| (GR-108)(ii) `f`-spread ≠ 0 (the law is not pattern-independence) | `--cell`, `--seed` | spread histograms printed: stratum `{0: 16, 2: 865, 4: 153}`, V8 `{8: 1}` |
| (GR-108)(iii) the strong form and its boundary | `--mech` | every maximum reversal set reaches balance at 1 034/1 034 stratum pairs; **65/101** at the (GR-103) control; worst seeded `n = 12` ratio 32/66 |
| the hunt (refutation object) | `--hunt` | 373 pairs at `n = 12/14/16/18`, `2k ∈ {2, 4}` (86 + 96 + 60 + 73 + 25 + 20 + 4 cell-sampled + 9 seeded `n = 14`): kinds `{'vacuous': all}`, 0 candidates — **not found under the disclosed caps** |
| (GR-107) proper | `--cell`, `--seed` | not separately driver-testable as an isolated sentence: it is the inner validity criterion of `rmodel_f`, so the 1 054-pair cube assert exercises it at every pattern; its (iii)/(iv)/(v) clauses are derivations from landed theorems, cited above |

**Determinism.** `--validate` run at `PYTHONHASHSEED` 0 and 999:
byte-identical except the `[Ns]` wall-clock annotations. Every seeded leg
prints its seed.

**Caps, disclosed in full — an exhausted cap is not a proof of
nonexistence.** (1) Only the `n ≤ 6` stratum sub-cell is exhaustive (every
`O ⊆ M` matching of every odd-carrying shape). (2) The seeded legs use
`seeded_shapes` tries 200/90/400/300 at `n = 8/10/12/14` (matching caps
6/6/4/none, binding on 0 shapes — disclosed by the driver). (3) The
cell-targeted sampler runs tries 400/300/200/150/60 with pair caps
30/20/4 on the `n = 16` (2k = 2), `n = 16` (2k = 4) and `n = 18` legs
(the first not reached at 25 pairs; the latter two reached exactly);
`n = 18` sweeps only 4 pairs. (4) `--mech`'s `n = 12` pool is 120 tries.
(5) No search caps exist in any assertion path; `perfect_matchings`'s
internal cap 500 never binds at the sizes swept. **None of these caps
qualifies (GR-105)–(GR-107)** — those are proofs; the caps qualify
(GR-108)'s measured standing and the hunt's emptiness only.

**Scratch probes (README's standing rule).** None were run: every figure
quoted above is produced by `gprice.py`.

---

### Confidence verdict (Steps G125–G129)

| | claim | standing |
|---|---|---|
| **(GR-105)** | the colour-swap identity `f(p) = f(p̄)`, every matching; equal `2k = 2` prices | **proven** (one line off (GR-49)); asserted at 1 431 pairs |
| **(GR-106)** | the reversal-set normal form at `O ⊆ M`; `dist = n − \|R\|`; the `2^n` algorithm | **proven**; cube-asserted at 1 054 pairs to `n = 12`, then load-bearing to `n = 18` |
| **(GR-107)(i)/(ii)** | reachable patterns are affine; the balance-reachability signing criterion | **proven** (GF(2) linear algebra) |
| **(GR-107)(iii)** | the `2k = 2` reduction: off-`M` case outright; `O ⊆ M` case ⟸ (GR-108) | **proven** ((GR-99) + (GR-86) + (GR-105) consumed) |
| **(GR-107)(iv)/(v)** | the linkage obstruction to price `≤ 0`; adjacent-pair removal free | **proven** |
| **(GR-108)** | the balance law at `O ⊆ M` | **minted; measured** — 1 431/1 431, stratum sub-cell EXHAUSTIVE, 0 violations to `n = 18`; **NOT a theorem**; strong form fails from exactly `n = 12`, so a proof must exchange between maximum reversal sets |
| **(GR-104)(i)** | the price form | **theorem at `n ≤ 10`** (landed, untouched); **NEW: theorem at `2k = 2`, every `n`, modulo (GR-108) alone**; refutation object **not found** to `n = 18` under disclosed caps; `2k ∈ {4, 6}` `O ⊄ M` corner untouched and OPEN |
| (GR-103) audits, (GR-70)(ii), (GR-99)–(GR-102) | | **untouched and consumed**; the control pair's landed row independently re-derived by the new model |
| **(a′)** / input (Y) / (GR-64) rows / **(GR-15)** | | **OPEN — not attempted**; no rank computed anywhere; no flank; no class-uniformity claim |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same side
as GBAL's through GCHEAP's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos)
(AC-9)); the only samplers draw **graphs**, not placements.

### What would change this (Steps G125–G129)

*(i)* **A proof of (GR-108)** makes (GR-104)(i) a theorem on the whole
`2k = 2` stratum at every `n`, closing (b′) at the constant 2 there modulo
(GR-C1) alone; the pinned proof shape is the maximum-set exchange of
(GR-108)(iii), and the two free moves of (GR-107)(v) and the blocked-gap
structure at maximality are its inventory. *(ii)* **A refuting `O ⊆ M`
pair** (every maximum reversal set signing-blocked) kills the balance law
AND the price form at `2k = 2` in one object — (GR-102) confines it to
`d_par(M) ≥ 2|δ| − b_M` and this pass adds that every maximum reversal set
must be linked; nothing of the kind appeared to `n = 18`. *(iii)* **An
error in (GR-99)(ii)** would void (GR-107)(iii)'s off-`M` half — it is a
landed proven theorem. *(iv)* **The `2k ∈ {4, 6}`, `O ⊄ M` corner** is
named open above; a (GR-106) extension with fixed odd-`F` darts is the
natural instrument. *(v)* **The `Λ ≠ ∅` / `D > 0` lifts** stay unswept by
standing rider; (GR-106) uses cubicity and `M` perfect throughout.
*(vi)* **A Lean transcription** of (GR-105)/(GR-106) would be small
(finite dart counting plus a cycle-orientation bijection); nothing here
pins a carrier beyond what (GR-49)–(GR-51) already pin.

**TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator
re-runs it.**

- **(E1) NOT FIRED.** No g-flank; the pass is rank-free and computes no
  rank, so clauses (i)–(iv) cannot fire. Clause (v) (`d_adm = ∞`) fires on
  nothing: every swept pair has finite `d_adm` (gap 0 at every `O ⊆ M`
  pair; `O ⊄ M` pairs not re-measured).
- **(E2) NOT FIRED.** Entry 5 is PROVEN ((GR-54)) and consumed untouched.
  No route is demoted: (GR-104)(i) keeps its landed `n ≤ 10` theorem and
  gains a conditional `2k = 2` theorem; the residual is narrowed to
  (GR-108) + one named corner, each with its successor instrument named in
  place.
- **(E3) ARMED (by GBAL), DOES NOT FIRE, and this direction does not fire
  it.** E3 fires only on a HIT completing **entry 1** — i.e. (a′). This
  pass does not attempt (a′), computes no rank, and makes no `d_fg` claim.
  The movement here is on **(b′)'s selection layer** ((GR-104)(i) reshaped
  onto (GR-108) at `2k = 2`), which is not entry 1 and arms nothing.
  **Firing is a coordinator action; reported, not fired.**

---

### Step G130 — (GR-110): the arc-transversal normal form — at a fixed sink set, the maximum family IS an independent-transversal family, and sources slide freely inside sink-arcs

> **(GR-110)** *(proven; asserted configuration-by-configuration against
> the exhaustive labeled enumeration at **6 294** (pair, sink set) cells —
> the stratum EXHAUSTIVE, V8, the (GR-103) control, seeded `n = 12/14`;
> `--form`)*
>
> Fix an `O ⊆ M` pair in the (GR-106) model and let `K` be the sink set
> of some valid configuration. Then:
>
> **(i) The arc system.** On each `F`-cycle, sinks and sources alternate,
> so `K` cuts each `K`-meeting cycle into `|K ∩ C|` **arcs** (segments
> between cyclically consecutive sinks), and a valid configuration with
> sink set `K` has exactly one source in each arc's interior and nothing
> on `K`-free cycles.
>
> **(ii) The transversal characterization.** The valid configurations
> with sink set exactly `K` are **precisely** the choices of one source
> per arc interior such that (a) no even matching pair has both ends
> chosen and (b) no odd branch has one end chosen and the other in `K`.
> Every one has `|R| = 2|K|` — so either all of them are maxima or none
> is, and the maximum family stratifies by sink set into
> independent-transversal families.
>
> **(iii) The slide generator.** Consequently replacing one source by
> any other admissible position of its arc preserves validity and
> `|R|`; dually (fix the sources) sinks slide inside source-arcs — the
> colour-swap involution (GR-105) exchanges the two statements.
>
> **(iv) A Haxell-type sufficient condition (remark).** The conflict
> relation on positions ("both ends of an even matching pair chosen")
> is a partial **matching**, i.e. max degree `Δ = 1`; by Haxell's
> theorem (P. E. Haxell, *A note on vertex list colouring*, Combin.
> Probab. Comput. **10** (2001), no. 4, 345–347: classes of size
> `≥ 2Δ` admit an independent transversal — citation verified) if some
> maximum configuration's sink set avoids all odd-branch ends and every
> arc interior still has `≥ 2` positions after deleting the ends of one
> odd branch `γ`, then a maximum with `γ` **free** (no resident end)
> exists; at `2k = 2` such a maximum is valid at a balanced pattern, so
> (GR-108) holds at that pair. Weak in practice — singleton arcs abound
> at every swept `n` — and recorded only as the one unconditional
> "large-arc" criterion currently proven; not a headline claim and not
> driver-tested.

*Proof.* (i) is (GR-106)(i) read at the labels. (ii) One source per arc
is exactly alternation; among the (GR-106) constraints, the even-pair
exclusions inside `K` are inherited from the configuration that
produced `K`, sink–source pairs are unconstrained, source–source pairs
are (a), and the end forcings (GR-106)(iii) plus end-consistency say a
branch's resident ends carry ONE label — which given fixed `K` is (b).
Counting: `|R| = |K| + #arcs = 2|K|`. (iii) is (ii) applied twice. ∎

---

### Step G131 — (GR-111): the recombination theorem — two maxima exchange along glued difference components, the maximum family is recombination-connected, and the 2k = 2 refutation shape sharpens to UNIVERSAL linkage

> **(GR-111)** *(proven; asserted mechanically at **6 426** seeded
> `(x, y, T)` triples — every recombinant valid and maximum; `--recomb`)*
>
> Work at the orientation level (orientations of `F`'s edges; hub states
> through/sink/source by `F`-in-degree; (GR-106)'s constraints). For
> orientations `x, y` let `z` be the set of edges where they differ,
> with its connected components in `F`; a hub on a `z`-edge belongs to
> that edge's component (two `z`-edges at one hub share a component),
> and a `z`-fixed hub has equal states in `x` and `y`. **Glue**
> components `X ~ X'` whenever some constrained pair `(a, b)` (an even
> matching pair, or the two ends of one odd branch) has `a ∈ X`,
> `b ∈ X'` and a **mixed** state pair — `(x_a, y_b)` or `(y_a, x_b)` —
> violating that pair's constraint. Then for every union `T` of glued
> classes, the recombinants `x_T` (`y`-values on `T`, `x` elsewhere)
> and `y_T` (the complementary exchange) satisfy:
>
> **(i)** per hub, `{state_{x_T}(v), state_{y_T}(v)} =
> {state_x(v), state_y(v)}`, so the reversal counts of `x_T` and `y_T`
> sum to those of `x` and `y`;
>
> **(ii)** both recombinants are valid; and
>
> **(iii)** if `x` and `y` are maxima, **both recombinants are maxima**.
>
> **(iv) Connectivity.** Swapping the glued classes one at a time walks
> `x` to `y` through maxima: the maximum family is
> recombination-connected.
>
> **(v) The 2k = 2 separation criterion.** Let `x` be an AA-forcing
> maximum and `y` a BB-forcing one. If no glued class is pinned both
> ways — where an end of `γ₁` that is a **sink in `y`** pins its class
> OUT and an end of `γ₂` that is a **source in `x`** pins its class IN
> (mirror version with `γ₁`, `γ₂` swapped) — then `T` = the IN-pinned
> classes makes `x_T` an **AB-valid maximum**, and (GR-108) holds at
> the pair. Contrapositive, sharpening (GR-108)(iv): a refutation of
> (GR-108) at `2k = 2` requires **universal linkage** — at EVERY pair
> (`x` AA-max, `y` BB-max), a glued chain joining a pinned `γ₁` end to
> a pinned `γ₂` end. The converse implication is FALSE: the (GR-113)
> witness is universally linked (exhaustively, at that pair) and the
> law holds there anyway.

*Proof.* (i): a hub's state is a function of its two incident edge
values; on `T` both values are `y`'s (a hub with one `z`-edge has its
other edge shared), off `T` both are `x`'s, so each hub's two
recombinant states are its two original states in one order or the
other. (ii): a constrained pair sees pure `x`-states, pure `y`-states
(also when one hub is `z`-fixed, where mixed = pure), or genuinely
mixed states across two UNGLUED classes — legal by the definition of
gluing. (iii): both are valid, so both counts are `≤ M*`; by (i) they
sum to `2M*`. (iv): swap classes of `z` one at a time; each
intermediate pairs with its complementary recombinant by (iii).
(v): the pin conditions say exactly that in `x_T` every end of `γ₁` is
source-or-through and every end of `γ₂` is sink-or-through, i.e. `x_T`
is valid at the balanced pattern (A on `γ₁`, B on `γ₂`); it is a
maximum by (iii). ∎

*(Register note: the mixed-state pins are well-defined because an
AA-forcing maximum has all resident odd ends sources, a BB-forcing one
all sinks, and a `z`-fixed end shared by both must be through.)*

---

### Step G132 — (GR-112): the escape lemma — imbalance intervals move by at most one notch per move, so no fine move crosses the balance layer, and the law REDUCES to an escape statement

> **(GR-112)** *(proven at every `2k`; the no-crossing consequence
> asserted on every one of the fine-move graph's edges the driver
> builds — 0 violations; `--conn`)*
>
> **(i) The interval.** The valid patterns of a configuration form a
> subcube (forced branches pinned, free branches free), and their
> imbalance values are exactly `{μ, μ+2, …, M}` with `μ = β − d`,
> `M = β + d` (`β` = forced-A count minus forced-B count, `d` = #free).
> Classify: **bal** (`μ ≤ 0 ≤ M`), **pos** (`μ ≥ 2`), **neg**
> (`M ≤ −2`).
>
> **(ii) The moves.** The fine-move calculus: source slides and sink
> slides ((GR-110)(iii)), **adjacent-pair teleports** (remove an
> aux-cycle-adjacent reversal pair — always valid, (GR-107)(v) — then
> insert a reversal pair into any gap of the result), and **safe
> flips** (flip an aux component holding resident ends of at most ONE
> odd branch). All preserve validity and `|R|`, hence map maxima to
> maxima.
>
> **(iii) The notch bound.** A single fine move changes `μ` by `≥ −2`
> and `M` by `≤ +2`. *Proof:* the `μ`-lowering branch transitions are
> exactly A→free and A→B (each `−2`; the other four transitions move
> `μ` by `0` or `+2`), and each requires the branch to lose its **last
> source end** — a slide or teleport removes at most one source hub,
> and a safe flip converts the ends of at most one branch, so at most
> one branch can suffer one per move; the `M` half is the colour-swap
> mirror (GR-105). ∎
>
> **(iv) No crossing.** Hence no single fine move joins a pos
> configuration to a neg one (from `μ ≥ 2`, the successor has
> `μ ≥ 0`), and the FIRST non-pos configuration on any fine-move walk
> out of a pos configuration is **bal**.
>
> **(v) The reduction.** If at an `O ⊆ M` pair some maximum is
> pos-forcing and some fine-move sequence through the maximum family
> leaves the pos class, then a balance-valid maximum exists. So
> **(GR-108) follows from the ESCAPE statement**: *at every pair whose
> maximum family contains a pos-forcing member, some pos-forcing
> maximum admits a fine-move walk out of the pos class* (pairs with no
> pos/neg-forcing maxima satisfy the law vacuously — every maximum is
> balance-valid; pos and neg members come in (GR-105) pairs).

---

### Step G133 — (GR-113): the measured escape verdict — universal escape holds through `n = 14` and FAILS at an explicit `n = 16` witness whose stranded maxima defeat BOTH mechanisms; existential escape is intact everywhere swept

> **(GR-113)** *(measured; `--conn`, `--recomb`, `--strand`; caps
> disclosed below — an exhausted cap is not nonexistence)*
>
> Sweep the labeled maximum family of **1 099** `O ⊆ M` pairs (stratum
> EXHAUSTIVE 1 034, V8, the (GR-103) control, seeded cell pools at
> `n = 12` (2k = 2 and 4), `14`, `16`) and its fine-move graph at three
> nested levels (L1 slides; L2 + teleports; L3 + safe flips):
>
> **(i) The stratum strengthening.** On the exhaustive `n ≤ 6` stratum
> there is **no pos- or neg-forcing maximum at all** (12 448 labeled
> maxima, all balance-valid) — strictly stronger than (GR-108)(iii)'s
> landed stratum half, which quantified over reversal **sets**.
>
> **(ii) Universal escape** (every fine component holding a forcing
> maximum also holds a balance-valid one): holds at **every** swept
> pair through `n = 14` at level L2 — at the control, slides alone
> strand 2 components and teleports reconnect the whole 202-config
> family into ONE component — and **FAILS at exactly one swept pair**,
> the `n = 16` witness (`strand_witness` in the driver; one 16-cycle
> 2-factor, both odd branches matching chords): its 152 maxima split
> into one 88-component carrying all 56 balance-valid maxima plus 16
> pos and 16 neg, and two STRANDED pure components (32 pos / 32 neg —
> pure, exactly as (GR-112)(iv) forces). Safe flips do not rescue it.
>
> **(iii) Existential escape** (the (GR-112)(v) hypothesis): **0
> failures anywhere swept** at L2/L3. (At L1, slides alone already
> fail one `n = 14` pair even existentially.)
>
> **(iv) The separation mechanism's limits.** The (GR-111)(v)
> criterion, hunted constructively at every pos-forcing maximum: at
> the control it succeeds at **36/36** (all neg partners tried); at
> the seeded `n = 12` pool at 75/196; at the `n = 16` pool at 36/124 —
> and at the witness pair at **0/48, exhaustively**: the witness's
> 2-factor is a single cycle, so every configuration determines its
> orientation, and ALL (pos, neg) maximum pairs were tried — the
> witness is **universally linked**, yet the law holds there via its
> 56 natively balance-valid maxima.
>
> **(v) The two mechanisms are incomparable.** Fine moves rescue the
> witness's big-component pos maxima (16/16 reach balance-valid
> company) where separation rescues none; separation rescues all 36
> control pos maxima where slides alone strand some. Neither, alone or
> together, reaches the witness's stranded 32 — **any proof of
> (GR-108) must produce the balance-reaching maximum globally, not by
> locally repairing an arbitrary maximum**: maxima exist that are dead
> ends for every exchange in this calculus.

**Caps, disclosed in full.** (1) Only the `n ≤ 6` stratum leg is
exhaustive; V8 and the control are single named pairs. (2) The cell
pools run `cell_shapes` tries 120/120/60/40 at `n = 12(2k=2)/12(2k=4)/
14/16` with a pair cap 12 on the `n = 16` leg; `--form`/`--conn`/
`--recomb` draw their pools at distinct printed seeds. (3) The
separation hunt caps neg partners at 40 per pos maximum — the driver
counts and prints where the cap binds: at exactly **one** swept pair,
the witness itself inside `--recomb`'s `n = 16` leg, where `--strand`'s
exhaustive 48-partner hunt supersedes it — and draws one orientation
per attempt (reversal-free cycles' coins; at the witness no coin
exists). (4) The `--strand` leg is cap-free at its pair (single
`F`-cycle). None of
these caps qualifies (GR-110)–(GR-112) — those are proofs; the caps
qualify (GR-113)'s sweeps only.

---

### Step G134 — (GR-114): where (GR-108) stands after the exchange-calculus pass, and the hand-off

> **(GR-114)** *(the status statement; no new mathematics)*
>
> | statement | standing after this pass |
> |---|---|
> | (GR-108), the balance law | unchanged by this pass; **since REFUTED from `n = 16` (*Steps G135–G139*, GXESC)** |
> | (GR-108)(iii)'s stratum half | **strengthened, exhaustively**: every labeled maximum configuration on the `n ≤ 6` stratum is balance-valid (12 448/12 448) |
> | the fixed-sink structure of the maximum family | **theorem** ((GR-110)): independent-transversal families, sources sliding in sink-arcs |
> | exchange between maxima | **theorem** ((GR-111)): glued-difference recombination, maximum-family connectivity, and the sharpened refutation shape (universal linkage) |
> | the law's reduction | **theorem** ((GR-112)): fine moves never cross the balance layer; (GR-108) ⟸ existential escape |
> | universal escape (per-component locality) | **REFUTED** at the explicit `n = 16` witness — the second localization of (GR-108) to fail at a finite boundary (per-set at `n = 12`, (GR-108)(iii); per-component at `n = 16`, here) |
> | existential escape | the named open kernel of this pass, measured intact at all 1 099 swept pairs; **since REFUTED at the same witnesses (*Steps G135–G139*)** — the 0-failures record stands as a statement about this pool |
> | (GR-111)(v) separation as a complete proof route | **refuted**: the witness is universally linked (0/48, exhaustive at that pair) while the law holds there |
> | (GR-104)(i) at `2k = 2` | **unchanged**: theorem modulo (GR-108) alone ((GR-107)(iii)) |
>
> **The residual, in successor order** (revising (GR-109)'s entry 1 in
> place; entries 2–3 unchanged):
> 1. ~~**Prove (GR-108)**~~ — *(revised in place by (GR-119), Steps
>    G135–G139: both shapes died together — (GR-108) and existential
>    escape are REFUTED at the same four witnesses.)* The successor is
>    the **half-witness clause** ((GR-117)(iii)); the calculus and
>    parametrization of this pass remain the workspace.
> 2. The `2k ∈ {4, 6}`, `O ⊄ M` corner — untouched here, as barred.
> 3. (GR-C1) past the stratum — untouched here, as barred.

---

### Verification (Steps G130–G134)

`notes/scripts/w4/gblaw.py` (**new with this pass**, at the spec's pinned
path; left untracked for the coordinator to gate and commit). Imports —
all read-only — `imb_of` / `odd_idx` / `stratum_cases` / `v8_specs`
**directly from `gridbal_common`** (never via the sibling re-exports),
`cflank.cubic_habitat`, and **five `gprice` devices** (`cell_data`,
`cell_shapes`, `gr103_specs`, `pairs_of`, `rmodel_f`) — a §2-rule-2
sideways trip, disclosed as a *Harness debt* item below. **Rank-free**:
`gexist.fully_good_rank` is never imported or called and no `d_fg` claim
is made anywhere. Local devices, none shadowing a §1 primitive (checked
against the README index and the *Divergences* table): `valid_pats` /
`imb_interval` / `cls_of` (the first-principles validator and the
(GR-112) classification), `enum_family` (the exhaustive labeled maximum
family plus the per-pattern maxima, a SECOND validator cross-checked
in-driver against `valid_pats` and against the landed `rmodel_f`),
`arcs_of` / `transversal_family` ((GR-110)'s two sides), `slides` /
`gaps_of` / `teleports` / `aux_comps` / `safeflips` (the move calculus),
`orient_of` / `states_of` (the configuration ↔ orientation dictionary),
`glue_data` / `swap_T` / `recombine` / `separation` ((GR-111)),
`strand_witness` (the pinned `n = 16` witness, re-entered for
independent reconstruction and gated by `cubic_habitat` at use),
`family_of` / `form_pair` / `conn_pair` / `recomb_pair` / the pools /
reports. Exact integers / GF(2) throughout; no floating point; rngs
seeded per mode with the seed printed; no set iteration printed.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --form      # ~6 s  (GR-110) at 6 294 (pair, sink set) cells + enum == rmodel_f at every pattern of 1 072 pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --conn      # ~10 s (GR-112)/(GR-113): the fine-move census, three levels, no-crossing asserted on every edge
PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --recomb    # ~8 s  (GR-111) at 6 426 (x, y, T) triples + the separation hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --strand    # ~1 s  the witness in full: pinned component structure + the EXHAUSTIVE separation hunt
PYTHONHASHSEED=0 python3 notes/scripts/w4/gblaw.py --validate  # ~25 s all four in one process
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-110)(i)/(ii) the transversal characterization | `--form` | `transversal_family` (built from the theorem's clauses alone) asserted **set-equal** to the enumerated family at every (pair, sink set) cell — 6 294 cells across the stratum (EXHAUSTIVE), V8, the control, seeded `n = 12/14`; `|R| = 2|K|` asserted per cell |
| the labeled enumeration itself | `--form` | `enum_family`'s per-pattern maxima asserted `== n − f(p)` against the landed `rmodel_f` at **every pattern** of all 1 072 pairs, and every family member re-checked by the independent `valid_pats` |
| (GR-110)(iii) slides valid | `--conn` | every slide image validated and asserted to be an enumerated maximum (any miss aborts) |
| (GR-111)(i)–(iii) recombination | `--recomb` | 6 426 seeded `(x, y, T)` triples: both recombinants asserted valid AND maximum |
| (GR-111)(v) separation ⟹ balance | `--recomb`, `--strand` | every separation the hunt finds has its recombinant asserted balance-valid and maximum |
| (GR-112)(iii)/(iv) no crossing | `--conn` | asserted on EVERY edge of every fine-move graph built (pos↔neg forbidden; `μ` drop `≤ 2`), all levels, all 1 099 pairs |
| (GR-113)(i) stratum strengthening | `--conn` | the stratum leg's forcing counter: 0 pos/neg-forcing among 12 448 labeled maxima (exhaustive stratum) |
| (GR-113)(ii) universal escape + the witness | `--conn` | per-pair no-escape component counts at L1/L2/L3; the sole L2/L3 witness printed in full (shape, matching) |
| (GR-113)(iii) existential escape | `--conn` | per-pair existential-escape counter: 0 failures at L2/L3 |
| (GR-113)(iv) the witness's exhaustive linkage | `--strand` | pinned family (152; 48/48/56), pinned component profile (88 = 56+16+16, 32 pos, 32 neg), separation 0/32 stranded and 0/16 big-component over ALL 48 neg partners, asserted |
| (GR-108) itself | — | **not re-measured** (GPRICE's landed 1 431/1 431 stands; the bar on re-running landed sweeps respected); the driver's per-pair `assert bali` in the separation leg re-derives the law only at the pairs it sweeps, as a guard |

**Determinism.** `--validate` run at `PYTHONHASHSEED` 0 and 999:
byte-identical except the `[Ns]` wall-clock annotations. Every seeded leg
prints its seed.

**Scratch probes (README's standing rule).** Two interim probes (the
witness's component profile; the stranded separation hunt) were promoted
into the driver as `--strand` before landing; every figure quoted above
is produced by `gblaw.py`.

**Harness debt.** The five `gprice` devices above acquired their second
consumer via a disclosed §2-rule-2 sideways import — recorded as a
*Harness debt* item in `notes/scripts/README.md` (the canonical home).

---

### Confidence verdict (Steps G130–G134)

| | claim | standing |
|---|---|---|
| **(GR-110)** | the arc-transversal normal form; slides; `|R| = 2\|K\|` | **proven**; asserted at 6 294 cells |
| **(GR-111)** | glued-difference recombination; maximum-family connectivity; the universal-linkage refutation shape | **proven**; asserted at 6 426 triples |
| **(GR-112)** | the imbalance-interval notch bound; no fine move crosses the balance layer; (GR-108) ⟸ existential escape | **proven** (every `2k`); no-crossing asserted on every edge built |
| **(GR-113)** | universal escape to `n = 14`; REFUTED at the `n = 16` witness; existential escape 0 failures; the witness universally linked (exhaustive at that pair) | **measured** under the disclosed caps; the witness's own figures cap-free |
| **(GR-108)** | the balance law | **unchanged** — minted, measured, open; the residual is now *existential escape OR a global construction* |
| (GR-105)–(GR-107), (GR-103), (GR-104)(i) | | **untouched and consumed**; the control's landed figures re-derived only as in-driver guards |
| **(a′)** / input (Y) / (GR-15) | | **OPEN — not attempted**; no rank computed anywhere; no flank; no class-uniformity claim |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as GBAL's through GPRICE's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos)
(AC-9)); the only samplers draw **graphs**, not placements.

### What would change this (Steps G130–G134)

*(i)* **A proof of existential escape** makes (GR-108) a theorem at
`2k = 2` (with (GR-107)(iii)) — the walk may start at ANY well-chosen
maximum, which is exactly what the witness leaves open. *(ii)* **A pair
whose every fine component of forcing maxima is stranded AND whose
balance-valid stratum is empty** refutes (GR-108) outright; the witness
shows the first half is achievable per-component, so the hunt for the
second half now has a shape to grow from (grow `strand_witness`-like
single-cycle pairs and test `bal = 0`). *(iii)* **A fourth move class**
(multi-pair moves, or removal of non-adjacent pairs) could restore
universal escape — the witness is the exact test case, and the driver's
move generators are the harness for it. *(iv)* **An error in
(GR-107)(v)** (adjacent-pair removal's validity) would void the teleport
generator; it is a landed proven theorem. *(v)* **The `Λ ≠ ∅` / `D > 0`
lifts** stay unswept by standing rider; everything here uses cubicity
and `M` perfect throughout.

**TERMINATION check (E1/E2/E3) — this direction's reading; the
coordinator re-runs it.**

- **(E1) NOT FIRED.** No g-flank; the pass is rank-free and computes no
  rank, so clauses (i)–(iv) cannot fire. Clause (v) (`d_adm = ∞`) fires
  on nothing: at an `O ⊆ M` pair the empty reversal set is valid at
  every pattern ((GR-106)(v), vacuously), so `d_adm ≤ n` everywhere
  this model reaches.
- **(E2) NOT FIRED.** Entry 5 is PROVEN ((GR-54)) and consumed
  untouched. No route is demoted: (GR-108) keeps its measured standing
  and gains a proven exchange calculus; the residual is re-expressed
  (existential escape / global construction), not widened; the two
  refuted localizations (universal escape; separation-as-complete-route)
  were both minted and killed inside this same pass, with the law's
  standing unchanged.
- **(E3) ARMED (by GBAL), DOES NOT FIRE, and this direction does not
  fire it.** E3 fires only on a HIT completing **entry 1** — i.e. (a′).
  This pass does not attempt (a′), computes no rank, and makes no `d_fg`
  claim. The movement is on (b′)'s selection layer ((GR-108)'s exchange
  calculus), which is not entry 1 and arms nothing. **Firing is a
  coordinator action; reported, not fired.**

---

### Steps G135–G139 (2026-08-26, direction GXESC) — **(GR-108), the balance law, is REFUTED BY WITNESS — and existential escape falls with it; the price form survives at every witness, and its residual is reshaped onto a two-case GAP-2 LAW, three quarters of it proven**: **(GR-115)** is the **reversal-label ledger** — score sources +1 and sinks −1; per-cycle alternation and the even-pair exclusion force `Σ_j c_j + h = 0`, with `c_j` odd branch `j`'s resident-end score and `h` the **even-half ledger** (the score of the resident hubs whose even matching partner is through) — whose corollaries are all proven: an **M-closed** configuration (every matching branch fully in or fully out of `R`) is **balance-valid at every `2k`**; at `2k = 2`, `|h| ≤ 1` forces balance-validity and pos-forcing forces `h ≤ −2`; **(GR-116) REFUTES (GR-108)**: four explicit single-`F`-cycle `O ⊆ M`, `2k = 2` habitat pairs — two at `n = 16`, two at `n = 20`, the first ONE 2-chord endpoint transposition away from the (GR-113) witness diagram — have maximum families that are pure pos + neg with **NO balance-valid member** (`d_adm − d_par = 2`), every figure re-derived through THREE independent models (two of them landed); hence **existential escape ((GR-112)(v)'s hypothesis) is REFUTED** — with no bal maximum, no fine-move walk can leave the pos class ((GR-112)(iv)) — and (GR-109)'s "theorem modulo (GR-108) alone" loses its hypothesis; **(GR-117)** mints the reshaped residual, the **GAP-2 LAW**: at `2k = 2`, `O ⊆ M`, the price form (GR-104)(i) is EXACTLY `d_adm(M) ≤ d_par(M) + 2`, it **SURVIVES at all four witnesses** (both one-flip prices +2), and it is **PROVEN at every pair whose maximum family contains a balance-valid or half-resident member** (one (GR-107)(v) adjacent-pair removal at the lone resident end frees the branch at `M* − 2`) — the ONE open case, *every maximum forcing with both branches fully resident*, is measured EMPTY at all 248 hunted pairs, and a gap-4 pair (a genuine (GR-104)(i) refutation) would have to live there; **(GR-118)** is the measured record — the hunt legs and the exact failure boundary (exhaustively TRUE at `n ≤ 6`, clean to `n = 14` under caps, FALSE from `n = 16`), the M-closure coverage (`M* − M*_cl ∈ {0, 2, 4}` everywhere swept), and the (GR-113) witness anatomy: under **interval flips** through configurations of size `≥ M* − 2`, all 32 "stranded" maxima reach balance-valid company — the strandedness was an artifact of the L1–L3 move set, answering *Step G134*'s fourth-move question positively at the witness and moot for the law; **(GR-119)** the status. **(GR-15) stays OPEN, no gap-map status move on `hK` itself; E3 stays ARMED and does NOT fire.**

Answering `notes/Pencil-fanout.md` §"GXESC — thirty-fifth ordinal":
**prove existential escape / (GR-108), or refute by witness**. **The
outcome is the spec's named refutation-by-witness shape, in its strong
form**: pairs whose balance-valid stratum is empty while pos-forcing
maxima exist — *Step G134*'s hunt shape ("grow `strand_witness`-like
single-cycle pairs and test `bal = 0`") delivered exactly as written,
plus one proven ledger theorem and a proven three-quarters of the
successor law. Rank-free throughout: nothing imports or calls
`gexist.fully_good_rank` and no `d_fg` claim is made anywhere
((a′) / input (Y) untouched). Read against *Steps G125–G129*
((GR-105)–(GR-109)) and *Steps G130–G134* ((GR-110)–(GR-114)).

***Notation, inherited unchanged, with one new term.*** The (GR-106)
model throughout: `O ⊆ M` pair, `F = G° ∖ M` all-even, reversal set
`R`, sinks/sources, through hubs, `dist = n − |R|`, `M* = n − d_par`;
classes bal/pos/neg as at (GR-112)(i); "resident" = in `R`; a branch
is **full** (both ends resident), **half** (one), or **empty**.
**New:** the **score** of a resident hub is `+1` (source) / `−1`
(sink); `c_j` = the score-sum of odd branch `j`'s resident ends
(`∈ {−2, …, +2}`); `h` = the score-sum of the resident hubs on
half-resident EVEN matching branches (the **even-half ledger**); a
configuration is **M-closed** iff no branch (even or odd) is half.

**Step 0 pin (mandatory, discharged before any derivation).** (GR-105)
(colour swap), (GR-106) in full (the normal form; its constraints are
what "valid" means below), (GR-107)(iii)/(v) (the 2k = 2 reduction and
the adjacent-pair removal), (GR-110)–(GR-112) (the exchange calculus,
consumed as proven theorems), (GR-113)'s witness figures (re-entered
as controls, asserted, never re-derived), (GR-86) (the gap-4 cap),
(GR-99)(ii) and (GR-104) as landed. **Bars honoured:** (GR-C1) not
attacked; the `2k ∈ {4, 6}` `O ⊄ M` corner untouched; no landed
census re-run — GPRICE's 1 431-pair sweep and GBLAW's 1 099-pair
escape census are cited as records of their pools (the refutation
pairs are NEW pairs outside both pools); (GR-15) / class uniformity
untouched; no `.lean` touched (the standing Lean hold).

---

### Step G135 — (GR-115): the reversal-label ledger — sources minus sinks vanish cycle-by-cycle, so the forcing class of a configuration is stored on its half-resident even branches

> **(GR-115)** *(proven; asserted clause-by-clause EXHAUSTIVELY over
> all `3^n` labeled states of every `n ≤ 6` stratum pair (39 642
> valid configurations, 1 034 pairs), over every valid orientation
> word of the (GR-113) witness (22 876, ALL sizes), and over the
> labeled maximum families of V8 and the (GR-103) control; `--ledger`)*
>
> Score every resident hub `+1` (source) / `−1` (sink). At every
> valid configuration of every `O ⊆ M` pair (any `2k`):
>
> **(i) The identity.** Each `F`-cycle's score-sum is 0 (alternation),
> and each full even matching pair's is 0 (its labels differ,
> (GR-106)(ii)). Since `M` is perfect, partitioning `R` by matching
> branch gives
> > `Σ_j c_j + h = 0`.
>
> **(ii) M-closure forces balance — at every `2k`.** If no branch is
> half, then each `c_j ∈ {−2, 0, +2}` and `Σ c_j = 0`, so the full
> odd branches split into **equally many forced-A and forced-B** (a
> full source-source branch is forced A, sink-sink forced B,
> (GR-106)(iii)), and the free count `2k − #full` is **even**; the
> pattern colouring the forced branches as forced and splitting the
> free ones evenly is balanced and valid. **Every M-closed valid
> configuration is balance-valid.**
>
> **(iii) The `2k = 2` dictionary.** `|h| ≤ 1 ⟹` balance-valid (a
> forced-equal pair has `|c_1 + c_2| ≥ 2`). Pos-forcing `⟹ c_1, c_2
> ≥ 1 ⟹ h ≤ −2` — a net sink surplus of at least 2 on the even-half
> branches — with `h = −2` forcing **both** odd branches half.
> (Neg mirrors by (GR-105).)

*Proof.* (i): alternation ((GR-106)(i)) makes sinks and sources
equinumerous on each cycle; the branch partition then splits the zero
total into full-even (0 each, labels differ), odd (`c_j`), and
even-half (`h`) parts. (ii): a full odd branch has equal labels
(structural validity), so `c_j = ±2`; `Σ c_j = 0` forces the ±2's to
pair up; `2k` even makes the free count even; validity of the
displayed pattern is immediate from (GR-106)(iii). (iii): direct.
∎

*(Register note: (GR-115)(ii) is the first unconditional structural
balance-validity criterion after (GR-110)(iv)'s Haxell remark, and it
is checkable by a `2^{n/2}` chord-subset enumeration — the driver's
`closed_mstar`. Its coverage is real but partial: see (GR-118)(iii).)*

---

### Step G136 — (GR-116): the balance law (GR-108) is REFUTED — four witnesses, the first one transposition from the (GR-113) diagram — and existential escape is refuted with it

> **(GR-116)** *(refutation by witness; every pinned figure asserted
> through THREE independent models — the driver's orientation-word
> census, the landed `gprice.rmodel_f` ((GR-106)(vi), cube-asserted at
> 1 054 pairs in its own sweeps), and, at `n = 16`, the landed
> `gblaw.enum_family` (itself cross-asserted against `rmodel_f` at
> 1 072 pairs at its landing); `--verify`, discovery in `--hunt`)*
>
> **(i) The witnesses.** Four `O ⊆ M`, `2k = 2` habitat pairs, each
> with a single-cycle 2-factor and both odd branches matching chords
> (`refut_specs` in the driver, positional diagrams on the cycle
> `0..n−1`; shapes rebuilt deterministically and gated by the
> canonical `cflank.cubic_habitat`):
>
> | witness | `n` | maximum family | gap `d_adm − d_par` |
> |---|---|---|---|
> | **mut16** | 16 | `M* = 12`; 64 maxima = **32 pos + 32 neg + 0 bal** | **2** (`f = {AA: 4, AB: 6, BA: 6, BB: 4}`) |
> | **rand16** | 16 | `M* = 12`; 48 = 24/24/**0** | **2** (same `f`-table) |
> | **rand20a** | 20 | `M* = 16`; 32 = 16/16/**0** | **2** (same) |
> | **rand20b** | 20 | `M* = 16`; 48 = 24/24/**0** | **2** (same) |
>
> mut16's diagram: even chords `{8,5}, {1,9}, {13,15}, {12,3}, {2,7},
> {14,10}`, odd chords `{6,11}, {0,4}` — it differs from the (GR-113)
> witness diagram by **one endpoint transposition between two even
> chords** (odd chords identical; asserted). The near-miss was one
> swap from the law's grave.
>
> **(ii) What is refuted.** **(GR-108) as stated** — at these
> matchings NO balanced pattern attains `d_par(M)`: `d_adm = d_par +
> 2`. Hence also: **existential escape** ((GR-112)(v)'s hypothesis) —
> the maximum family is pure pos + neg, and by the no-crossing lemma
> (GR-112)(iv) the first non-pos stop of any fine-move walk would be a
> bal maximum, which does not exist; **universal escape's remaining
> hope** likewise; and the **`2k ∈ {4, 6}` `O ⊆ M` sub-cell route**
> "follows from (GR-108) wherever the law holds" loses its general
> form. Consistently with (GR-111)(v)'s contrapositive, the witnesses
> are universally linked — a refutation cannot be otherwise. Per
> (GR-115)(iii)'s contrapositive, every maximum at every witness has
> `|h| ≥ 2` and none is M-closed (asserted).
>
> **(iii) What is NOT refuted.** **(GR-104)(i) survives at all four
> witnesses**: the parity optima are the two unbalanced patterns and
> both majority one-flip prices are exactly `+2 ≤ 2` — see (GR-117).
> The theorems (GR-105)–(GR-107), (GR-110)–(GR-112) and (GR-115) are
> implications or mechanism facts and stand untouched; (GR-86)'s
> gap-4 cap stands (the witnesses realize gap 2). GPRICE's
> 1 431/1 431 and GBLAW's 1 099-pair records remain true of their
> pools — the witnesses are new pairs outside both, in the cell those
> samplers rarely draw (single-cycle `F` at `n ≥ 16`).
>
> **(iv) The boundary.** (GR-108) is exhaustively TRUE on the
> `n ≤ 6` stratum sub-cell (GPRICE, 1 034 pairs — landed) and
> measured-clean at `n = 8/10/12/14` (landed pools; plus this pass's
> 74 + 48 single-cycle pairs at `n = 12/14`, gap 0 throughout); it is
> **FALSE from `n = 16`** — the third localization boundary of the
> (GR-108) family after per-set `n = 12` ((GR-108)(iii)) and
> per-component `n = 16` ((GR-113)(ii)), and this time it is the law
> itself. Between 14 and 16 the record is caps-only, not exhaustive.

*Verification note.* The word census is a third, independent
implementation of the (GR-106) model (single-cycle specialization:
orientation words with sign-change residency); it reproduces the
(GR-113) witness's pinned `(M*, family, classes) = (12, 152,
48/48/56)` and, at `--ledger`, has its class and ledger values
asserted against the `valid_pats`/`cls_of` machinery at every one of
the witness's 22 876 valid words. The full `2^{|E|}` cube stops at
`n = 12` (|E| = 18), so no witness is cube-checkable — the bar met
here (two landed models + one fresh one, all exact, agreeing on every
figure) is the same bar the landed (GR-83) and (GR-113) witnesses
met. ∎

---

### Step G137 — (GR-117): the GAP-2 LAW — the price form at `2k = 2`, `O ⊆ M` is exactly `d_adm ≤ d_par + 2`, and it is proven except at one named configuration class

> **(GR-117)** *(minted; the equivalence and clause (ii) proven;
> clause (iii)'s hypothesis measured EMPTY at all 248 hunted pairs;
> `--hunt`'s gap histograms and `all22` counter)*
>
> **(i) The equivalence.** At an `O ⊆ M` pair with `2k = 2`:
> `f(AA) = f(BB)` and `f(AB) = f(BA)` ((GR-105)), so `d_par =
> min(f(AA), f(AB))`, `d_adm = f(AB)`, and the (GR-104)(i) sentence
> ('vacuous', or some majority one-flip price `≤ 2` at a `|δ| = 2`
> optimum) is **exactly**
> > `gap := d_adm(M) − d_par(M) ≤ 2`  — the **gap-2 law** —
> the gap being even ((GR-106)(iv): `dist ≡ n mod 2`) and `≤ 4`
> ((GR-86), landed). (GR-108) was the `gap = 0` form; the witnesses
> realize gap 2; a **gap-4 pair is exactly a (GR-104)(i) refutation**
> at this cell.
>
> **(ii) The proven three quarters.** The gap-2 law holds at every
> pair whose maximum family contains a member that is **balance-valid
> or has a half-resident odd branch**. *Proof.* A bal maximum gives
> gap 0. Otherwise take wlog a pos-forcing maximum `x` with γ₂
> half-resident at its lone source end `e`. Both cyclic `R`-neighbours
> of `e` on its `F`-cycle are sinks (alternation), and no resident odd
> end is a sink at a pos maximum, so a neighbouring sink `s` is not an
> odd end. Remove the adjacent pair `{e, s}` — valid by (GR-107)(v),
> constraints only relax. The result has γ₂ **free** and γ₁ still
> forced A, so it is valid at the balanced pattern (A, B) with
> `|R| = M* − 2`: `d_adm ≤ d_par + 2`. ∎ (By (GR-115)(iii), the
> `h = −2` pos maxima are automatically of this kind — both branches
> half.)
>
> **(iii) The one open case, exactly named.** The gap-2 law can fail
> only at a pair where **every maximum is forcing with both odd
> branches fully resident** (residency (2,2), `|h| = 4`). Measured:
> **0 such pairs** among all 248 gated single-cycle pairs hunted
> (`all22`), including all four refutation witnesses — at each of
> which the law therefore holds with gap **exactly** 2, by (ii) plus
> bal-emptiness. The named successor clause — the **half-witness
> clause**: *every pos-carrying `O ⊆ M` pair has a maximum that is
> balance-valid or half-resident* — would make (GR-104)(i) a
> **theorem at `2k = 2`, every `n`, unconditionally** (with
> (GR-107)(iii)'s proven off-`M` half), replacing the refuted
> "modulo (GR-108)" route by a strictly weaker hypothesis with a
> proven surgical mechanism.

---

### Step G138 — (GR-118): the measured record — the hunt and the boundary, the M-closure coverage, and the witness anatomy (the strandedness was the move set's artifact)

> **(GR-118)** *(measured; `--hunt`, `--closure`, `--strand`; caps
> disclosed below — an exhausted cap is not nonexistence)*
>
> **(i) The hunt** (the *Step G134* shape, single-`F`-cycle `2k = 2`
> diagrams, word census): the EXHAUSTIVE gated 2-chord-transposition
> neighbourhood of the (GR-113) witness (41 pairs — **1 refutation**,
> mut16) and seeded pools at `n = 12/14/16/18/20` (74/48/42/33/10
> gated pairs — refutations 0/0/**1**/0/**2**). Gap histogram over
> all 248: `{0: 244, 2: 4}`; **no gap-4 pair** (no (GR-104)(i)
> refutation) and **no all-(2,2) pair** anywhere.
>
> **(ii) The `n = 18` note.** The 33-pair `n = 18` leg is clean —
> the failure set is not monotone in `n` along these caps; nothing
> beyond "not found under cap" is claimed at 18.
>
> **(iii) M-closure coverage** (`--closure`, 1 100 pairs: stratum
> EXHAUSTIVE 1 034 + V8 + control + witness + cell pools at
> `n = 12/14/16`): an M-closed maximum — hence a balance-valid one,
> (GR-115)(ii) — exists at 970/1 034 stratum pairs, at V8 and the
> control, and at 19/64 of the pool pairs; the closed gap
> `M* − M*_cl ∈ {0, 2, 4}` everywhere swept. The criterion is real
> but partial: the (GR-113) witness itself has `M*_cl = 10 < 12`
> (closed gap 2) while carrying 56 bal maxima — M-closure does not
> explain them — and 30 of the 33 forcing mutation-leg pairs lack an
> M-closed maximum. (GR-115) asserted at every maximum of all 1 100
> pairs, 0 violations.
>
> **(iv) The (GR-113) witness anatomy** (`--strand`). Features of the
> 16 escaping vs 32 stranded pos maxima: ledgers `h` `{−4: 2, −3: 8,
> −2: 6}` vs `{−4: 8, −3: 20, −2: 4}`; residencies `{(1,1): 6,
> (1,2): 8, (2,2): 2}` vs `{(1,1): 4, (1,2): 20, (2,2): 8}`; **sink
> set shared with some bal maximum: 8/16 vs 0/32** — the sharpest
> separator found: a stranded maximum's sink system supports no
> balance-valid transversal at all ((GR-110)(ii)).
>
> **(v) The dip census — the fourth-move answer.** Widen the move set
> to **interval flips** (flip the orientation of one cyclic segment:
> toggles residency at the two cut hubs and colour-swaps the segment's
> interior — a strict superset of slides and single
> removals/insertions) through valid configurations of size
> `≥ M* − d`. At the witness, already at **`d = 2`** (2 454 valid
> words) **all 32 stranded pos maxima reach balance-valid company**
> (as do the 16 escapers). *Step G134*'s what-would-change (iii) is
> answered at its own test case: a fourth move class DOES restore
> universal escape there — and it is moot for the law, which
> (GR-116) refutes outright at pairs where no bal maximum exists for
> any calculus to reach.

**Caps, disclosed in full.** (1) The mutation leg is exhaustive over
gated 2-chord transpositions of the witness diagram only (41 of the 56
endpoint-transposition candidates — two per chord pair — pass the
F-parallel exclusion and the habitat gate under the driver's
deterministic `ℓ`-placement recipe; the others are not swept). (2) The seeded
single-cycle pools run `cyc_sample` tries 100/60/60/40/12 at
`n = 12/14/16/18/20` (seeds printed; the boundary legs on their own
seed so the discovery legs reproduce byte-identically). (3) The
`--closure` cell pools reuse `gprice.cell_shapes` tries 120/120/60/40
with pair cap 12 on the `n = 16` leg. (4) `--strand`'s dip census is
the witness pair only. (5) No assertion path is capped. **None of
these caps qualifies (GR-115), (GR-116)(i)–(iii) or (GR-117)(i)/(ii)**
— those are proofs or verified witnesses; the caps qualify the
boundary claim (GR-116)(iv), the hunt's emptiness figures and the
coverage figures only.

---

### Step G139 — (GR-119): where the arc stands after the refutation, and the hand-off

> **(GR-119)** *(the status statement; no new mathematics)*
>
> | statement | standing after this pass |
> |---|---|
> | (GR-108), the balance law | **REFUTED** — four verified witnesses from `n = 16`; exhaustively true at `n ≤ 6` (landed); measured-clean to `n = 14` under caps |
> | existential escape ((GR-112)(v)'s hypothesis) | **REFUTED** at the same witnesses (no bal maximum to escape to); GBLAW's 0-failures record stands as a statement about its 1 099-pair pool |
> | (GR-110)–(GR-112), the exchange calculus | **untouched, proven** — mechanism theorems, not law instances |
> | (GR-105)–(GR-107) | **untouched, proven**; (GR-107)(iii)'s off-`M` half still gives (GR-104)(i) outright there |
> | (GR-104)(i) at `2k = 2`, `O ⊆ M` | **⟺ the gap-2 law** ((GR-117)(i)); SURVIVES at every witness (price +2); **proven whenever some maximum is bal or half-resident** ((GR-117)(ii)); open exactly at the all-(2,2) case, measured EMPTY at 248 pairs |
> | (GR-104)(i) at `2k = 2`, whole cell | theorem at `n ≤ 10` (landed, untouched); now **theorem modulo the half-witness clause** ((GR-117)(iii)) — replacing the refuted "modulo (GR-108) alone" |
> | (GR-104)(i) at `2k ∈ {4, 6}`, `O ⊆ M` sub-cell | the (GR-108)-conditional route is dead in general; (GR-115)(ii) covers the M-closed-maximum pairs at every `2k`; otherwise open, the corner unchanged |
> | (GR-115), the ledger | **proven** (exhaustive asserts); its M-closure criterion the first unconditional balance-validity test after the Haxell remark |
> | the (GR-113) witness's stranded family | reconnects at dip 2 under interval flips — the L1–L3 strandedness was the move set's artifact ((GR-118)(v)) |
>
> **The residual, in successor order** (revising (GR-114)'s entry 1 in
> place; entries 2–3 unchanged):
> 1. **Prove the half-witness clause** ((GR-117)(iii)): every
>    pos-carrying `O ⊆ M` pair has a maximum that is balance-valid or
>    half-resident. It is strictly weaker than the dead (GR-108),
>    carries a proven surgical mechanism ((GR-117)(ii)), and closes
>    (GR-104)(i) at `2k = 2` unconditionally. Equivalently: refute it
>    together with the gap-2 law by an **all-(2,2), gap-4 pair** —
>    the hunt shape is pinned (`--hunt`'s `all22` and gap counters;
>    none found to `n = 20` under the disclosed caps), and such a
>    pair would refute (GR-104)(i) itself, moving (b′)'s constant.
> 2. The `2k ∈ {4, 6}`, `O ⊄ M` corner — untouched, as barred.
> 3. (GR-C1) past the stratum — untouched, as barred.

---

### Verification (Steps G135–G139)

`notes/scripts/w4/gxesc.py` (**new with this pass**, at the spec's
pinned path; left untracked for the coordinator to gate and commit).
Imports — all read-only — `odd_idx` / `stratum_cases` / `v8_specs`
**directly from `gridbal_common`** (never via the sibling re-exports),
`cflank.cubic_habitat`, the **five `gprice` devices** (`cell_data`,
`cell_shapes`, `gr103_specs`, `pairs_of`, `rmodel_f` — each acquiring
a THIRD consumer) and **seven `gblaw` devices** (`cls_of`,
`enum_family`, `safeflips`, `slides`, `strand_witness`, `teleports`,
`valid_pats` — each acquiring its SECOND consumer): §2-rule-2 sideways
trips, disclosed and recorded as an extension of the GBLAW *Harness
debt* item (`notes/scripts/README.md`, the canonical home).
**Rank-free**: `gexist.fully_good_rank` is never imported or called
and no `d_fg` claim is made anywhere. Local devices, none shadowing a
§1 primitive (checked against the README index and the *Divergences*
table): `lab_val` / `ledger_of` / `ledger_assert` (the (GR-115)
clauses), `closed_mstar` (the `2^{n/2}` M-closed optimum),
`word_valid` / `word_stats` / `word_census` (the single-cycle
orientation-word census — the third independent (GR-106)
implementation), `specs_of_diagram` / `cyc_sample` /
`witness_positional` / `witness_mutations` (the hunt cell),
`refut_specs` (the four pinned witnesses, re-entered for independent
reconstruction and gated at use), `dsu_find` / `dip_census` (the
interval-flip graph), `closure_pair` / pools / reports. Exact
integers / GF(2) throughout; no floating point; rngs seeded per mode
with the seed printed; no set iteration printed.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --ledger    # ~4 s   (GR-115) exhaustive/witness/family asserts
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --closure   # ~8 s   M-closure coverage + closed-gap histogram, 1 100 pairs
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --hunt      # ~190 s the single-cycle hunt: 248 pairs, gap histograms, the 4 refutations found
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --verify    # ~50 s  the 4 pinned witnesses through the three models, every figure asserted
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --strand    # ~1 s   the (GR-113) witness anatomy + the dip census
PYTHONHASHSEED=0 python3 notes/scripts/w4/gxesc.py --validate  # ~250 s all five in one process
```

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (GR-115)(i)–(iii), every clause | `--ledger` | asserted at every valid configuration: EXHAUSTIVE `3^n` labeled states on the stratum (39 642 configs / 1 034 pairs), every valid word of the (GR-113) witness (22 876, with word-model class and ledger cross-asserted against `valid_pats`/`cls_of`/`ledger_of`), V8 + control maximum families; also at every maximum of `--closure`'s 1 100 pairs and inside `--verify` |
| (GR-116)(i) the witnesses' figures | `--verify` | each pinned `(M*, N, pos, neg, bal, gap, min|h|)` asserted in the word census AND `rmodel_f`'s `f`-table asserted `= {4, 6, 6, 4}` AND (n = 16) `enum_family`'s family/class profile asserted equal — three independent models |
| (GR-116)(i) mut16's provenance | `--verify` | the one-transposition relation to the (GR-113) diagram asserted set-theoretically (odd chords identical) |
| (GR-116)(ii) no M-closed / no `\|h\| ≤ 1` maximum at a witness | `--verify` | `\|h\| ≥ 2` and non-closure asserted at every maximum of both `n = 16` witnesses ((GR-115)'s contrapositive) |
| (GR-116)(iv) the boundary legs | `--hunt` | `n = 12/14` single-cycle pools: gap histogram `{0: all}`; the `n ≤ 6` exhaustive half is GPRICE's landed record, cited not re-run |
| (GR-117)(i) gap parity/cap | `--hunt`, `--verify` | gap asserted even and `= (bal-maxima = 0)`-consistent at every censused pair; the 4-cap is (GR-86), landed |
| (GR-117)(iii) the hunt for the open case | `--hunt` | `all22` counter = 0 at all 248 pairs; `price_refut` (gap ≥ 4) counter = 0; any hit would print the full diagram |
| (GR-118)(iii) coverage | `--closure` | per-leg counts + closed-gap histograms; the `(M*_cl = M*) ⟺ (an M-closed maximum exists)` consistency asserted per pair |
| (GR-118)(iv)/(v) anatomy + dip census | `--strand` | the 32/16 strand split re-derived through the landed L1–L3 generators and asserted; feature histograms printed; dip-`d` reachability computed on the interval-flip graph, `d = 2, 4, 6, 8` |
| the witness control | `--hunt`, `--ledger` | (GR-113)'s pinned `(12, 152, 48/48/56)` asserted in the word model before any hunt leg runs |

**Determinism.** `--validate` run at `PYTHONHASHSEED` 0 and 999:
byte-identical except the `[Ns]` wall-clock annotations. Every seeded
leg prints its seed; the discovery legs keep the exact rng stream that
found the witnesses (the added boundary legs draw from their own
printed seed).

**Scratch probes (README's standing rule).** Two interim probes (the
first re-derivation of the candidates through `rmodel_f`/`enum_family`;
the `n = 20` figure/timing check) were promoted into the driver as
`--verify` before landing; every figure quoted above is produced by
`gxesc.py`.

### Confidence verdict (Steps G135–G139)

| | claim | standing |
|---|---|---|
| **(GR-115)** | the reversal-label ledger; M-closed ⟹ balance-valid (every `2k`); the `2k = 2` dictionary | **proven**; asserted exhaustively on the stratum + 22 876 witness words + every family swept |
| **(GR-116)** | (GR-108) REFUTED; existential escape REFUTED; boundary `n = 16` | **refuted by witness** — four pairs, every figure asserted through three independent exact models, two of them landed (the (GR-83)/(GR-113) verification bar); the boundary's `8 ≤ n ≤ 14` half is measured-only under disclosed caps |
| **(GR-117)(i)** | price form ⟺ gap-2 law at `2k = 2`, `O ⊆ M` | **proven** ((GR-105) + (GR-86) + definitions) |
| **(GR-117)(ii)** | gap ≤ 2 whenever some maximum is bal or half-resident | **proven** ((GR-107)(v) surgery) |
| **(GR-117)(iii)** | the half-witness clause | **minted, measured** — all-(2,2) pairs 0/248, gap-4 pairs 0/248; NOT a theorem |
| **(GR-118)** | hunt, coverage, anatomy, dip census | **measured** under the disclosed caps; the witnesses' own figures cap-free |
| (GR-105)–(GR-107), (GR-110)–(GR-112), (GR-86), (GR-99)–(GR-104) | | **untouched and consumed**; (GR-113)'s figures re-asserted as controls |
| **(a′)** / input (Y) / (GR-15) | | **OPEN — not attempted**; no rank computed anywhere; no flank; no class-uniformity claim |

**Which side of the (`≤3`-closedHubNbhd) line this sits on.** The same
side as GBAL's through GBLAW's: exact GF(2) / integer combinatorics on
constructed hub multigraphs, never `PencilNondegFeasible G`; no rank is
computed anywhere; no σ-fixed witness is read as generic (§(K-clos)
(AC-9)); the only samplers draw **graphs**, not placements.

### What would change this (Steps G135–G139)

*(i)* **A proof of the half-witness clause** makes (GR-104)(i) a
theorem at `2k = 2`, every `n` (with (GR-107)(iii)'s off-`M` half),
leaving (b′) at the constant 2 resting on (GR-C1) plus the
`2k ∈ {4, 6}` `O ⊄ M` corner alone — the exact position (GR-109)
claimed modulo the now-refuted (GR-108), re-based on a strictly weaker
hypothesis. *(ii)* **An all-(2,2), gap-4 pair** refutes (GR-104)(i)
at `2k = 2` outright and moves (b′)'s constant; the hunt shape is
pinned and its counters are the detector. *(iii)* **An error in
(GR-106)/(GR-107)(v)** would void both the witnesses and the surgery —
both are landed proven theorems, and the witnesses additionally ride
two independent implementations of the model. *(iv)* **The
`2k ∈ {4, 6}` `O ⊆ M` sub-cell** could be re-attacked with the
ledger: (GR-115)(ii) is `2k`-free, and the pair-removal surgery frees
one branch at cost 2 at any `2k` — the balanced-pattern bookkeeping is
what changes. *(v)* **The `Λ ≠ ∅` / `D > 0` lifts** stay unswept by
standing rider; everything here uses cubicity and `M` perfect
throughout. *(vi)* **A Lean transcription** of a refutation witness
would be small (one explicit multigraph, one matching, a finite
verified census); nothing here pins a carrier beyond what
(GR-49)–(GR-51) already pin.

**TERMINATION check (E1/E2/E3) — this direction's reading; the
coordinator re-runs it.**

- **(E1) NOT FIRED.** No g-flank; the pass is rank-free and computes
  no rank, so clauses (i)–(iv) cannot fire. Clause (v) (`d_adm = ∞`)
  fires on nothing: at every `O ⊆ M` pair the empty reversal set is
  valid at every pattern, so `d_adm ≤ n` everywhere this model
  reaches — including the four witnesses (`d_adm = 6` at each).
- **(E2) NOT FIRED.** Entry 5 is PROVEN ((GR-54)) and consumed
  untouched. A minted law ((GR-108)) is refuted, but it is not a
  ledger entry, and the refutation arrives **with its successor
  named** (the E2 carve-out): (b′)'s residual *narrows* from
  "modulo (GR-108) [false]" to "modulo the half-witness clause",
  three quarters of whose content is proven here; (a′)/(b′)/(c)/(d′)
  all remain open-with-a-named-dispatchable-attack.
- **(E3) ARMED (by GBAL), DOES NOT FIRE, and this direction does not
  fire it.** E3 fires only on a HIT completing **entry 1** — i.e.
  (a′). This pass does not attempt (a′), computes no rank, and makes
  no `d_fg` claim. The movement is on (b′)'s selection layer (the
  (GR-108) refutation and the gap-2 reshaping), which is not entry 1
  and arms nothing. **Firing is a coordinator action; reported, not
  fired.**
