## §(K-flank) — the adversarial rank test at the uncovered flanks: **half 2 proven-informally per shape; no disproof**

Sibling of §(K-slide-comb), computing the geometry at the flank taxonomy its
*Step D5* left. Standing notation inherited from the *Shared dictionary*,
§(K-tight) (the escape criterion, `U`, `R_a`, `r`, `r̃ = ★r`, `C(M)`, `s₀`),
§(K-pitch) ((T1)–(T3), `Q`), §(K-slide) (`G°`, decorations, (W1)–(W4), (S1),
(S5), `P21`) and §(K-slide-comb) (the flank taxonomy of *Step D5*).

§(K-slide-comb) *Step D5* and §(K-slide) *Step 5* left a list of **shapes no
class-uniform mechanism covers**, all of them built **combinatorially only** —
`def`, `hnoRigid`, the chromatic / acyclicity obstruction, the packing. No
geometry had ever been computed at any of them, and the opening recon's R2
("the conjecture survives all exact-rational rank tests") **predates** them,
so it is not evidence about them. This section computes the geometry, keeping
two questions apart:

1. does the pinned kernel `hK` hold at these shapes (a failure forces a
   re-pin), and
2. does the **pencil conjecture itself** hold there — at a nondegenerate
   pencil realization of a flank shape, does the body-hinge rank reach the Tay
   target (a failure disproves the phase's target theorem)?

**Verdict (2026-08-05, sixth pass).**

(i) **HALF 2 HOLDS at every flank shape — proven-informally, per shape, by an
exact witness; there is no disproof.** At each shape an exact rational
configuration is exhibited that satisfies **all four conjuncts** of
`IsNondegPencilRealization` (`Molecule/Pencil/Motive.lean:110`) and whose
exact-ℚ body-hinge rank **equals** the Tay target `6(|V| − 1) − def`. Because
`HasGenericPencilRealization` (`Motive.lean:140`) is itself an **∃** over
(framework, normal, point), one such witness *is* the statement at that shape
— no genericity or sampling argument is consumed. Tested: the eight named
shapes below and **843** flank class shapes in whole strata (Step F3),
including the **exhaustive** 438 menu-blocked `K4` shapes and all 210 all-`{3,4}`
`K5` class shapes. Zero failures.

(ii) **HALF 1: no `hK` counterexample, and no re-pin needed.** At all 16
probed `e₀`-end splits (8 shapes × both ends) and at **every** eligible split
of the 5-chromatic flank, `hK`'s realization antecedent is witnessed by a
*nondegenerate* target-rank `G′` seed and the escape is **observed on both KT
routes**, with the §(K-tight) criterion matching the observation seed by seed
and the escaping configuration re-certified as a legal nondegenerate
realization of `G` at target rank. The hard stratum is what these shapes sit
in (`s₀ = 0`, `dim R_a = 1`, `dim U = 2` at every clean seed): the flanks are
not an easy case in disguise.

(iii) **(K-pitch) closes at every flank split** (16/16): the transmitted
wrench is **non-null** (`Q(r) ≠ 0`) at the first valid seed of each, with
(T1)–(T3) and the (T2) sign law re-validated, `dim V_bc = 3` and the Klein Gram
on `V_bc` of rank 3. By §(K-slide) *Step 3*'s one-witness logic each such
certificate closes (K-pitch) at that split individually. So the flank shapes
join the §(K-slide) *Step 4* battery as **individually closed members** —
what they are *not* is covered by a **class-uniform** device.

(iv) **What resists at the flanks is the degeneration, not the geometry — and
it resists one level *earlier* than the collapse.** At the very shapes where
the collapse's assignment problem is unsolvable, the undegenerate rank problem
is **maximally healthy**: the full pencil-row family of `G` is independent
(rank `= 5|E| =` target), and at `ε = 1` the transmitted wrench is non-null.
But the **full-support slide-in limit is itself degenerate at every structural
flank** (Step F6, `--limit`; 40 sampled decorations each, no (W1)–(W4)
witness), in a shape-dependent way — so §(K-slide)'s `G°`-level carrier, the
object *Step 3* designates as where a class-uniform argument should live, does
not reach these shapes under the full support either. This **corrects** the
reading this pass started from ("the flanks obstruct only the tetrahedral
alignment"): they obstruct the alignment **and** the full-support limit. The
slide support is a free parameter ((S1) remark (iii)), so what is bounded is
the device *as run*, not the carrier in principle — the concrete next probe is
named in Step F7.

(v) **A ∀-realization escape statement is FALSE — exhibited.** At `P21`,
5 of 35 valid target-rank `G′` seeds have an `s₀`-jump (all five on the
`plane_basis` coincidence locus — §(K-out) (OC-38)(iii); `s₀ = 1`, hence
`dim R_a = 0`, `dim U = 1`) and therefore fail at **every** placement of `v`
— the first such seed ever exhibited in the phase's numerics, confirming a
§(K-tight) *Step 2.3* prediction that had never been tested. `hK`'s ∃-form is
untouched (30 of 35 seeds escape). Each jump seed's `G − v` stress is
supported on the **theta sub-multigraph `{12, 13, 23a, 23b}`** (12 edges, line
rank 6) — *exactly* the support §(K-slide) *Step 5* exhibits for `P21`'s
reduced-support **limit** stress: the parallel-edge obstruction is **not
confined to the `ε = 0` limit**; it inhabits a nonempty locus of the pencil
chart itself.

**What would change this.** *For half 2:* an error in the model dictionary
(the harness' 5-rows-per-hinge Euclidean-perp rigidity model vs
`BodyHingeFramework.rigidityRows`) — the standing §(K-tight) caveat, shared by
every numeric result in this workbook; or a flank shape outside the tested
strata (the `(K-res)` **length-6** flank is still unprobed, Step F7). *For
half 1:* a split at a flank shape where **no** seed escapes — none found, and
the only non-escaping seeds found are the ones the calculus proves must fail.
*For (iv):* a flank shape whose generic pencil rows are dependent (the strata
of Step F3 say there is none up to `|V| = 41`), or — in the other direction —
a **reduced slide support** under which a structural flank *does* carry a
(W1)–(W4) witness, which would move the flank inside the (K-slide) carrier
(Step F7 item 2).

### Step F0 — the two questions are not independent, and the quantifiers matter

Both halves must be stated against the landed objects, or the test measures the
wrong thing.

**Half 2 is an ∃.** `HasGenericPencilRealization K 3 G` unfolds
(`Motive.lean:140`) to: **∃** a body-hinge framework `F` and maps
`normal, point : α → Fin 4 → K` with `IsNondegPencilRealization G F normal
point` and `finrank (span F.rigidityRows) = 6(|V| − 1) − def`. The word
"generic" names the *stratum* (the nondegeneracy conjuncts), **not** a
Zariski-generic quantifier. So a single exact configuration settles half 2 at a
shape outright. Its four conjuncts, in the harness model (where the support
extensor **is** `pt(u) ∧ pt(v)`, so `ExtensorThroughPoint` at both endpoints
is built in):

1. `HasPencilPanelRealization` — per body a nonzero `normal v` with
   `point v ⬝ᵥ normal v = 0` and every incident hinge inside `normal v ^⊥`;
   equivalently, the hats of `{v} ∪ N(v)` admit a nonzero common annihilator
   (`kbare_common.verify_pencil_witness`, which also rejects coincident
   adjacent points);
2. every link's endpoint points **projectively distinct**;
3. `LinearIndepOn normal (closedHubNbhd v)` at every body;
4. `LinearIndepOn point (closedNbhd v)` at every **non-hub** body — i.e. at a
   degree-2 body, `pt(v), pt(p), pt(q)` not collinear.

At an all-lengths-`≥ 3` shape conjunct 3 is a nonzero-normal condition
(`closedHubNbhd` is a singleton at every body — hubs have no hub neighbours),
and conjunct 4 is the non-collinearity of every interior's little star. Both
are asserted per witness here, not assumed; so is `rank ≤ target`.

**Since each flank shape is tight, half 2 = full row rank.** `def = 0` and
`5|E| = 6(|V| − 1)` give `#rows = target = 6|V| − 6`. Two bounds then pin the
rank from above at *every* configuration, and neither needs the deficiency
theory: the six trivial twists always lie in the kernel (`rank ≤ 6|V| − 6`),
and the row count is what it is (`rank ≤ 5|E|`). So attainment is exactly
**independence of the whole pencil-row family**, and a `rank_modp` equal to the
target *certifies* the rational rank outright (`rank_p ≤ rank_ℚ ≤ #rows =
target`, the first inequality because a nonvanishing `k × k` minor mod `p` is a
nonvanishing integer minor). That is how the strata of Step F3 are certified
cheaply and exactly — `p = 2⁶¹ − 1` — with an exact-ℚ recheck at each
stratum's first shape and at every named witness of Step F2.

**Half 1 is an ∃ on both sides.** `hK` as pinned (`notes/Phase39-design.md`
§"W5-L7 research recon") reads: `G` simple, `5 ≤ |V|`, 2-edge-connected,
**`hnoRigid`**, `deg v = 2`, the two links, `(¬ hub a ∨ ¬ hub b)`, `e₀ ∉ E(G)`,
**and `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)`** ⟹ ∃ `hubSel`,
a seed `q` and a target-size set `s` of genuine edges with the `pencilRow`
subfamily independent at `q`. Three consequences for a refutation attempt:

- The conclusion is "**some** chart seed of `G` reaches the target", not "the
  given `G′`-seed extends". So a target-rank `G′`-seed that fails to extend is
  **not** a counterexample — only a shape where *no* `G`-seed reaches the
  target is, and by L7b (`hasGenericPencilRealization_of_independent_pencilRow_
  target`, `Escape.lean:186`, **landed**) that would refute half 2 as well.
  Hence: **half 2 holding at a shape closes the only route by which that shape
  could refute `hK`'s content.** The converse bridge — from a *witness
  configuration* to a *chart seed* — is the deferred re-seeding lemma
  `exists_pencilSeed_of_nondeg` (`Engine.lean`; the point-reproduction side is
  landed, the normal side and the final assembly are not). That step is
  **shape-independent**, so the flanks introduce no new gap; but the strict
  statement of what this section proves for half 1 is *the mathematics of
  `hK` at these shapes*, with the chart restatement resting on that landed-in-
  part lemma.
- `hnoRigid` sits in the antecedent, and `P21` **fails** it (its parallel pair
  is a rigid `C₆`, `no_rigid_branch_union` = False). So `hK` is **vacuous** at
  `P21`; `P21` is a `(K-res)`-shaped habitat member, and the probes there test
  the escape *mechanism* only. All seven other shapes carry `hnoRigid`.
- The antecedent asks for a **nondegenerate** `G′` realization. Every `G′`
  seed used below is re-certified against all four conjuncts (`G′` has a
  length-2 path, so its conjuncts 3 and 4 genuinely bite: the meet-line
  interior's two hub normals must be independent and `pt(a), pt(b), pt(c)`
  non-collinear).

**The placement-sampler trap, and the guard.** `widened.place_pencil_general`
places a single-panel interior with `localtest.in_plane_point`, whose
`plane_basis` returns two **parallel** in-plane directions whenever the
normal's third coordinate is `0` (`notes/scripts/README.md` *Divergences*; the
defect behind the corrected `widened.py` escape figures — §(K-tight) *Step 3*).
A hub normal is drawn from `rquat`, so this is not rare: at these shapes
**11 of 40** seeds are affected, and each affected hub collapses its whole
closed star onto a line. Read naively such a seed *looks like a disproof*. The
guard used throughout is structural, not a coordinate test: at a generic
pencil configuration the hats of `{v} ∪ N(v)` have rank **3** at every body
(3 is the maximum — at a hub they all lie in the 3-dimensional panel; at a
degree-2 body there are only three of them, and rank 3 there **is** conjunct
4). Step F4 measures that this guard detects exactly the artifact.

### Step F1 — the shapes, and their habitat certification

All eight are re-certified by the driver, **asserted** and not assumed:
`def = 0`, tight (`5|E| = 6(|V| − 1)`), 2-edge-connected, **`hcard`** (every
hub has `≤ 2` hub neighbours) and **triangle-free** — the last two being
exactly the conditions the (K) consumer carries
(`hasGenericPencilRealization_of_independent_pencilRow_target`,
`Escape.lean:186`). `hnoRigid` (`kslide.no_rigid_branch_union`) is **reported**
per shape rather than asserted, precisely because `P21` fails it; in the
`--strata` sweeps it *is* asserted, via `kslidecomb.shape_ok`.

| shape | `G°` | `χ(G°)` | `Δ(G°)` | `\|V\|` | `\|E\|` | target | flank |
|---|---|---|---|---|---|---|---|
| `K5`, lengths `(3,3,3,3,4,4,4,4,4,4)` | `K5` | 5 | 4 | 31 | 36 | 180 | D5-1, 5-chromatic |
| `K5 + v` (6th hub on `0,1,2`), `(4⁹,3⁴)` | 13 edges | 5 | 5 | 41 | 48 | 240 | D5-1, the Brooks `Δ ≥ 5` branch |
| 6v/11e, `(3⁸,4³)` | 11 edges | 4 | 4 | 31 | 36 | 180 | D5-2, no acyclic 4-colouring |
| `K222` octahedron, `(3⁶,4⁶)` | 12 edges | 3 | 4 | 36 | 42 | 210 | D5-3 (starved menu; (C7) rescues it) |
| wheel `W5`, all-3 | 10 edges | 4 | 5 | 26 | 30 | 150 | high-concurrency probe |
| wheel `W7`, all-3 | 14 edges | 4 | 7 | 36 | 42 | 210 | high-concurrency probe |
| `K4`, lengths `(1,1,3,5,3,5)` | `K4` | 4 | 3 | 16 | 18 | 90 | D5-3, first menu-blocked shape |
| `P21`, `(3;3,3;4,5,3,3)` | `K4` + doubled `23` | 4 | 4 | 21 | 24 | 120 | §(K-slide) 5, parallel `G°`-edge |

Two additions to the workbook's list, both deliberate:

- **`K5 + v`** exhibits the *second* branch of the Brooks characterization
  (§(K-slide-comb) verdict (i): `χ(G°) ≥ 5` forces `G° = K5` **or**
  `Δ(G°) ≥ 5`). The workbook names that branch but never exhibits it; here it
  is, as a class shape with `χ = 5`, `Δ = 5`, `G° ≠ K5`.
- **the wheels** are the sharpest *geometric* adversary available: their centre
  is a single body carrying `Δ(G°)` concurrent coplanar hinges, which is where
  a rank cap would be most plausible (and where the collapse's four-position
  ceiling bites hardest). All-length-3 is exactly tight for a wheel
  (`3m = 6(m − n + 1)` iff `m = 2n − 2`), so no search is needed. `W7` puts
  **seven** hinges in one pencil and still attains. The one visible mechanism
  by which a high-degree hub could cap the rank is that *all* of a body's
  hinges live in the 3-dimensional `Λ²Π̂(h)`, however many there are; the
  measurement says that does not bite for `Δ(G°) ≤ 7`. It is **not** evidence
  about unbounded `Δ`, which the class does not bound.

Two corrections to workbook prose, both checked, both **now applied in place**
(this section is their record):

- §(K-slide) *Step 5* described `P21` as "`G°` = `K4 − 02` plus doubled `23`".
  The spec it cites (and `kslide.flanks()` builds) is **all six `K4` edges plus
  a second `23`**: 7 hub paths, `Σℓ = 24 = 6(7 − 4 + 1)`, `|V| = 21`. With
  `K4 − 02` there would be 6 paths and the quoted lengths could not be tight —
  the sentence's own length list `(3; 3,3; 4,5,3,3)` has seven entries. Read
  "`K4` with `23` doubled".
- §(K-slide-comb) verdict (i) said "84 of the all-`{3,4}` assignments qualify"
  at `K5`. Reconciled: **210** = `C(10,4)` all-`{3,4}` assignments with
  `Σℓ = 36` are class shapes (all of them are — `hnoRigid` never fails here),
  of which **84** = `C(9,3)` have the *designated* split edge `(0,1)` of
  length 3. Both figures are right under their own convention; the driver here
  uses "`e₀` := the first length-3 edge", as `--k4full` does, and reports 210.

### Step F2 — (F1): half 2 at the named shapes

> **(F1)** *(proven-informally, per shape)* — at each of the eight shapes of
> Step F1 there is an exact rational configuration satisfying all four
> conjuncts of `IsNondegPencilRealization` whose exact-ℚ body-hinge rank equals
> the Tay target. Hence `HasGenericPencilRealization ℚ 3 G` holds at each —
> and, the witness being rational, over every field of characteristic 0 (rank
> of a fixed rational matrix is unchanged by field extension), and over
> `GF(2⁶¹ − 1)` by the same witness's mod-`p` rank.

*Proof.* By Step F0 the predicate is an `∃`, the witnesses are exhibited
(`flanks.py --conj`, seeds printed), and every conjunct plus `rank ≤ target` is
asserted at each witness. The rank figures: `180 = 180`, `180`, `210`, `240`,
`150`, `210`, `90`, `120` — in each case `= #rows = target`. ∎

Two remarks. **(a)** Attainment is *full row rank*, so at these tight shapes
the conclusion is the strongest possible: the pencil rows of `G` are
**independent**, and the deficiency bound is met with no slack anywhere.
**(b)** By the chart's irreducibility (a tower of affine-linear fibers —
§(K-slide) *Step 1(e)*) the attaining set is dense open, so the witnesses are
generic in the usual sense too; nothing below needs that.

### Step F3 — the strata: attainment is not an artifact of one length assignment

A single exhibited assignment per hub graph would be a weak test of a
*class*-flavoured worry, so half 2 is run over whole strata
(`flanks.py --strata`; the `rank_modp = #rows = target` certification of
Step F0, with an exact-ℚ recheck at each stratum's first shape):

| stratum | shapes | half 2 |
|---|---|---|
| `K5`, all-`{3,4}` assignments (`Σℓ = 36`) | 210 of 210 candidates are class shapes | **210/210** |
| 6v/11e, all-`{3,4}` (`Σℓ = 36`) | 155 of 165 candidates | **155/155** |
| `K222`, all-`{3,4}` (`Σℓ = 42`), seeded sample (seed 20260805, 40 draws) | 40 | **40/40** |
| `G° = K4`, the **menu-blocked** shapes, exhaustive | 438 of the 877 | **438/438** |

**843 flank class shapes, 0 failures.** The `K4` row is the exhaustive
menu-blocked flank of *Step D5 item 3* — every shape the pure dictionary
misses is included — and by the `--k4full` record every one of them carries an
`ℓ ≤ 2` edge (the only all-`≥ 3` `K4` shape is `(3,3,3,3,3,3)`, which solves),
so hub–hub adjacency and meet-line interiors are inside the sweep, not
excluded from it. Every shape in every row was additionally re-certified
`hcard` + triangle-free.

### Step F4 — the sampler-artifact control (and why the deficits are not evidence)

`flanks.py --degen`, at the 5-chromatic flank, seeds 1..40 (**restated and
re-measured 2026-08-06**, slice S2 — see the correction below): **17** samples
the *composite* guard accepts, **all** at rank 180 = target; **11** rejected by
the closed-star rank test, each short of the target by **exactly** the number
of hubs whose closed star collapsed to a line (deficits 1 and 2 observed);
**10** rejected *only* by the coincident-hinge clause, **every one at the full
target rank 180**; 2 unplaceable. So

- every rank deficit ever seen at these shapes is a sampler artifact, and the
  closed-star rank test is *exact for the rank deficit* on this shape — it
  detects precisely the rank-deficient samples and predicts the deficit;
- a **coordinate** test would not do: `--degen` exhibits samples with two
  zero-coordinate normals whose stars are nonetheless generic, and one with a
  single zero-coordinate normal that collapses. Only the structural rank
  condition classifies correctly. (This is the `plane_basis` precedent
  generalized: the right guard is a rank assert on the sampled *object*, not a
  test on the sampled *parameter*.)

> **CORRECTION (2026-08-06; F13, and one of the four claims it falsified).**
> This step used to say the star-rank guard "is *exact* on this shape — it
> detects precisely the affected samples", and the driver printed the same
> sentence. That is true of the **rank-deficient** samples and false of the
> **sampler-degenerate** ones: **10 of the 38 placeable seeds here** pass the
> closed-star rank test, satisfy all four `IsNondegPencilRealization`
> conjuncts, sit at the **full target rank** — and carry a coincident hinge
> line, i.e. a body with two of its hinges on one line, a free rotor. That is
> §(K-out) (OC-7)'s blind spot, reproduced independently on a different shape,
> in a different driver, at a **26 %** rate rather than (OC-7)'s ≈ 9 %. The
> acceptance site of this module (`flanks.clean_pencil_seed`) now applies the
> composite guard `repin.star_generic`, and `--degen` reports both columns side
> by side so the difference between the two tests stays measured. Nothing in
> half 1 or half 2 moves: a coincidence costs no rank, so every attainment
> witness this section quotes is still an attainment witness — it is now also
> drawn from a strictly cleaner pool.

Without the guard, 11 of 40 seeds at the headline flank shape would have read
as rank deficits at a shape "no mechanism covers" — the exact shape of a false
disproof.

### Step F5 — half 1: `hK`, the escape mechanism, and the pitch at the flanks

**(a) Both `e₀` ends, all eight shapes** (`flanks.py --split`; seeds 101..120,
3 placements per route). At every split: `hK`'s antecedent witnessed by a
nondegenerate target-rank `G′` seed; `s₀ = 0`, `dim R_a = 1`, `dim U = 2` —
the **hard stratum**; the §(K-tight) structure identities
(`dim U = dim R_a + 1`, `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U`) asserted; `critA` and
`critB` both true and **both routes observed to escape**; and the escaping
`G`-configuration re-certified against all four nondegeneracy conjuncts at
target rank (so each escape is *also* a half-2 witness). 16/16 splits.

**(b) Every eligible split of the 5-chromatic flank** (`flanks.py
--allsplits`). `hK` quantifies over `(v, a, b)`, so one bad split would
refute it. Every `v` with `deg v = 2` and a degree-2 neighbour is probed:
**26 splits — 26/26 escape**, at the first valid seed each. Eight of them have
**both** chain ends hubs (the two interiors of each of the four length-3
paths) — the (K-tight) hard form with the 5-dimensional combined failure span;
the other 18 are the three eligible interiors of each length-4 path, where one
chain end is free and the failure locus is 1-dimensional (strictly easier,
§(K-tight) *Step 4*). The escapes here are rank-level (the nondegeneracy
re-certification runs at the 16 `e₀` splits of (a)); nothing rests on it, since
half 2 at the shape is certified independently in Step F2.

**(c) The pitch certificate** (`flanks.py --pitch`). At the first valid seed of
each of the 16 splits: (T1) `r ⊥_E V_bc` with `W = V_bc ⊕ T` of dim 5 and
`W^⊥ = ⟨r⟩`; (T2) the sign law with `Q(r)·Q(z) < 0`; (T3) the motion-form
criterion agreeing with the §(K-tight) span form, and the route-A
`★r`-in-panel form; `dim V_bc = 3` with the Klein Gram of rank 3; and
**`Q(r) ≠ 0`** — a **non-null transmitted wrench**, which certifies escape on
both routes. 16/16. By §(K-slide) *Step 3* each certificate closes (K-pitch)
at that split, so the eight shapes of Step F1 are individually closed exactly
as the seven §(K-slide) *Step 4* battery members are.

**(d) The `dim R_a = 0` stratum, exhibited at last** (`flanks.py --rzero`).
§(K-tight) *Step 2.3* proves that a target-rank `G′` seed with `dim R_a = 0`
has `dim U = 1`, so the two placement functionals can never be independent on
`U` and the seed **fails at every placement**. No such seed had ever been
exhibited: the record was "every target-rank seed ever probed escapes"
(§(K-tight) *Step 3*). At `P21`, split `v = 100`, seeds 101..140: **30** seeds
with `dim R_a = 1` (escaping), **5** with `s₀ = 1`, `dim R_a = 0`, `dim U = 1`
(8/8 placements fail at each, as predicted), 5 invalid. Consequences:

- the prediction is **confirmed** against an exhibited *legal nondegenerate*
  target-rank `G′` realization;
- any **∀-realization** form of the escape ("every target-rank `G′` seed
  extends") is **FALSE at `P21`** — independent confirmation, at a
  whole-seed rather than a placement-locus granularity, of the design doc's
  "Finding 1 makes any ∀-realization opaque-`r` escape hypothesis false".
  `hK`'s ∃-form is untouched;
- the count-theoretic prediction (`widened.split_report`) is
  `dim R_a = 5 + def(G′) − def(G − v) = 1`; the jump is **geometric**, i.e.
  the *pencil* stratum carries corank the count does not see. **The
  "not thin in the sampler's rational range (5/35)" reading this bullet
  carried is REFUTED** (2026-08-19, direction SIGZ): **the five σ-jump seeds are EXACTLY the five at which `localtest.plane_basis` degenerates at hub `c`** (§(K-out) **(OC-38)**(iii), a set equality; under the composite gate `repin.star_generic`, `σ = 0` at all 360 gate-accepted seeds, cap 500), so the
  ≈ 14 % hit rate is a property of `plane_basis`, not of the variety. The
  five seeds remain **legal** chart points and everything else in this step
  stands; what falls is only the genericity reading.

**Correction to the numerical record** (the reason this matters beyond `P21`).
§(K-tight) *Step 3* recorded "**every** target-rank seed ever probed escapes",
and the gap map's (K-tight) row read "no genuine escape failure anywhere in the
corrected numerics". Both were true when written and both needed one
qualifier: the statement holds on the **hard stratum `dim R_a = 1`** (and above
it), and it is **false without that qualifier**, by the five seeds above. The
mathematics is unchanged (Step 2.3 always said so); the *record* was stated
more strongly than the stratum it was measured on. **Both are amended in
place** (§(K-tight) *Step 3*; the gap map's (K-tight) row).

**(e) What carries the jump — a hypothesis this pass refuted and replaced.**
The natural guess was "the parallel pair's rigid `C₆` picks up a stress".
Measured: at every one of the 5 jump seeds the `G − v` self-stress is
supported on **12 edges, on the four chains among hubs `{1,2,3}`** — hub pairs
`(2,3), (2,3), (1,2), (1,3)`, i.e. the **theta sub-multigraph
`{12, 13, 23a, 23b}`** — with **line rank 6**. Not the parallel pair alone.
That is *exactly* the support, edge count and line rank §(K-slide) *Step 5*
exhibits for `P21`'s reduced-support **limit** stress. So (S5)'s parallel-edge
obstruction is not an artifact of the `ε = 0` degeneration: the same theta
circuit closes on a nonempty locus of the pencil chart itself, where it forces
`dim R_a = 0`.

### Step F6 — what this settles for the gap map

**The geometry of `G` is unobstructed; both degenerations are not.**
§(K-slide-comb) *Step D5* item 4 suspected that "it is the *alignment* device
that fails to be class-uniform". Half of that is now measured and half is
**corrected**.

*Measured, and confirming Step D5:* where the collapse's assignment problem has
no solution at all, the undegenerate pencil-row family of `G` is
**independent** — full row rank, no slack (Steps F2/F3) — and the `ε = 1`
transmitted wrench is non-null (Step F5c). So no flank shape's *geometry*
resists.

*Corrected:* the obstruction is not confined to the tetrahedral alignment.
`flanks.py --limit` runs `kslide.limit_witness` at **generic, non-aligned**
decorations of the **full-support** `ε = 0` limit system, 40 seeds per shape,
and finds **no (W1)–(W4) witness at any of the four structural flanks**, with a
different first-failing conjunct per shape (the tally is printed; the assert
order is (W1) → (W4), so a tally concentrated on a later conjunct certifies the
earlier ones held at every seed):

| shape | full-support limit at 40 generic decorations |
|---|---|
| `K5`, χ = 5 | (W1) fails at 5 seeds; at the other 27 valid ones (W1)+(W2) hold and **(W3)** fails — `z(limit)` degenerate, the two `T`-conditions dependent on `V_bc` |
| 6v/11e | (W1) holds at all 30 valid seeds; **(W2)** fails at all 30 — `dim V_bc(limit) = 2`, the limit system over-constrained at `b, c` |
| `K222` octahedron | (W1),(W2),(W3) hold at all 30 valid seeds; **(W4)** fails at all 30 — the limit twist is Klein-**null** at every sampled decoration |
| `K5 + v`, χ = 5, Δ = 5 | identical profile: **(W4)** fails at all 30 valid seeds |
| `P21` | **(W1)** fails at all 35 valid seeds — the proven parallel-edge order-0 obstruction, (S5) |
| wheels `W5`, `W7`; `K4` `(1,1,3,5,3,5)` | **witness found at seed 101** — (W1) `dim mot = 9`, (W2) `dim V_bc = 3`, (W3) `z` defined, (W4) `Q(z_lim) ≠ 0` |

So the `G°`-level limit carrier — §(K-slide) *Step 3*'s designated home for a
class-uniform argument — **does not reach the structural flanks under the full
slide support**, and the three shapes where it does reach are exactly the ones
that were never structurally obstructed (two wheels and a menu-blocked `K4`,
each witnessed at the very first seed). The failure profiles are **uniform per
shape**, not scattered: 30/30 at `K222` and `K5 + v` ((W4) null twist), 30/30 at
6v/11e ((W2) `dim V_bc = 2`), 27/27 of the (W1)-passing seeds at `K5` ((W3) `z`
degenerate), 35/35 at `P21` ((W1)). Uniformity over 30-odd rational decorations
is consistent with identical vanishing on the decoration variety — which is
what a *proof* of the full-support limit's degeneracy at these shapes would
assert — but sampling can only ever refute identical vanishing, never
establish it, so this is evidence for the shape of the obstruction, not a
proof of it.
Since the ε = 1 pitch is non-null at these same splits (Step F5c), the
vanishing is a property of the **degeneration**, not of the shape; and since
the support Σ is a free parameter ((S1) remark (iii)), the negative bounds the
device *as run*. It is nonetheless a second, independent obstruction at the
flanks, and it is new: no prior pass ran the limit witness at these shapes.

**Mechanism, since supplied — see §(K-pure), not restated here** (2026-08-05,
fan-out direction C). **(PC-OBS)** explains the `K5` row of the table above
structurally, and *proves* the vanishing instead of sampling it: a chord
self-stress of the hub-point framework forces `z` into the isotropic `Λ²π̂` at
**every** decoration, and at the all-`{3,4}` `K5` shape `V_bc = α(pt c)`, the
strong-containment branch that makes **(W3)** fail — exactly the profile
measured here. The two passes' drivers are independent (`flanks.py --limit`, 40
non-aligned decorations per shape; `pure.py --flanks`, 10–11 chart seeds plus the
chord predictor) and they agree at every shape they share, which is evidence
rather than redundancy. The `K222` and 6v/11e mechanisms are still open there
too, and §(K-pure) *Step P7* additionally **answers** item 2 of Step F7 below.

**One flank shape moves inside the (K-slide) carrier — and it is a
menu-blocked one.** The `K4` shape `(1,1,3,5,3,5)`, a member of *Step D5 item
3*'s 438 menu-blocked shapes, carries a full (W1)–(W4) limit witness at the
first seed. By (S1) that closes (K-pitch) there **through the `G°`-level
carrier**, not merely through an `ε = 1` certificate. So for that shape the
menu obstruction is strictly stronger than the device requires: the 438-shape
flank is (at least in part) a defect of the *dictionary*, exactly as (C7)'s
partial rescue suggested, and not of the slide device. The two wheels are new
(K-slide) members on the same footing — the §(K-slide) *Step 4* battery table
gains three rows (done, marked `†` there).

Two readings, kept separate:

- **Settled.** No flank shape is a counterexample to the conjecture; no flank
  shape is a counterexample to `hK`; each flank shape is individually closed
  for (K-pitch) by an exact `ε = 1` certificate, and three of them through the
  `G°`-level carrier as well. The *Shapes no mechanism covers* list of the gap
  map is accordingly re-titled: these are shapes no **class-uniform** mechanism
  covers — every one of them is now individually discharged.
- **Not settled.** Nothing here is class-uniform. 843 shapes with `|V| ≤ 41`
  are 843 shapes, and the uniform statement remains (K-tight)/(K-move)/
  (K-pitch) exactly as before. This pass **removes a disproof risk and adds
  mechanism data**; it moves no uniform gap.

One structural consequence worth recording for direction C's benefit: at a
tight class shape, half 2 *is* the statement "the pencil rows of `G` are
independent at some chart point", i.e. the non-vanishing of one maximal
minor of the pencil rigidity matrix — a **pure-condition-shaped** statement in
White–Whiteley's idiom, on `G` itself rather than on a degenerated limit. The
843 shapes say that minor is nonzero at every tested class shape; what is
missing is a *reason*, and the pure condition of `G` (not of the limit) is
where a uniform reason would live.

### Step F7 — what remains open (honestly)

1. **Class uniformity.** Untouched. This section is per-shape certificates.
2. **Reduced slide supports at the structural flanks — ANSWERED**, by fan-out
   direction C the same day: **§(K-pure) *Step P7*** (the mathematics is there,
   not restated here). This pass named it the single most valuable follow-up its
   data points at, and it delivered: **5 of the 6 probed flank shapes close by a
   reduced support** — all three obstructed `K5` 5-chromatic shapes, the `K222`
   octahedron and θ(3,4,5), each by "no slide at `c`" — so the 5-chromatic flank
   *is* inside the (K-slide) carrier after all. The **6v/11e** flank is the one
   exception: it fails (W2) at every probed nonempty support, and its split
   closes by the `ε = 1` chart certificate only.
3. **The `(K-res)` length-6 flank** (gap map, *Shapes no class-uniform
   mechanism covers*) is **still unprobed**. It is out of this dispatch's
   target list, and it cannot be reached from the tight class: §(K-slide-cl)
   *Step C0*'s "`ℓ = 6` forces a rigid complement" lemma means a length-6 path
   is impossible under `hnoRigid`, so a probe needs a genuine `(K-res)`
   residual member (`notes/Pencil-W4-informal.md` §"widened kernels" *Step 4*),
   and none parallel-free was at hand. The right next probe, and cheap: build
   one, and run `--conj`/`--split` on it.
4. **The model dictionary.** Every rank figure lives in the harness'
   5-rows-per-hinge Euclidean-perp model (row space `= {w : ⟨w, C(e)⟩ = 0}`,
   kernel `= ⟨C(e)⟩`, global kernel the 6 trivial twists — checked implicitly
   by every `rank = 6|V| − 6` figure here). The §(K-tight) caveat stands
   unchanged; it is shared by the whole workbook, not specific to this pass.
5. **The chart bridge.** Half 1's chart-level restatement rests on
   `exists_pencilSeed_of_nondeg`, landed only in part (Step F0). Shape-
   independent, but not free.
6. **`P21`'s `s₀`-jump locus is LOCATED** (2026-08-19, direction SIGZ), and
   this item is closed as posed: 5/35 was never a dimension count, and **the five σ-jump seeds are EXACTLY the five at which `localtest.plane_basis` degenerates at hub `c`** (§(K-out) **(OC-38)**(iii), a set equality; under the composite gate `repin.star_generic`, `σ = 0` at all 360 gate-accepted seeds, cap 500) — the coincident pair `(c, 113, 115)` dropping the
   length-6 topological path's span from 6 to 5. So the locus is the
   sampler's coincidence locus, a proper closed subset. Whether an analogous
   locus exists at *parallel-free* shapes stays open (none seen: 0 jump seeds
   at the other seven shapes), but §(K-out) **(OC-37)** now proves that no
   such locus can be **combinatorially forced** anywhere in `hK`'s habitat.

### Verification

`notes/scripts/w4/flanks.py` (tracked, new this pass; exact ℚ throughout, no
floating point; imports the harness read-only; every sampled configuration
carries the four-conjunct nondegeneracy check *and* the star-rank genericity
guard; all seeds are literals and printed). Reproduce, from the repo root and
with `PYTHONHASHSEED=0`: `python3 notes/scripts/w4/flanks.py --conj | --degen |
--strata | --split | --allsplits | --pitch | --rzero | --limit`.

| driver | ~time | what it asserts |
|---|---|---|
| `--conj` | 10 s | HALF 2 at the 8 named shapes: class + habitat certification, then an exact nondegenerate configuration at the Tay target (8/8, exact-ℚ ranks 180/180/210/240/150/210/90/120) |
| `--degen` | 4 s | the sampler control at the 5-chromatic flank *(re-measured 2026-08-06, slice S2)*: **17** composite-guard-clean samples, all at the target; **11** rejected by the closed-star rank test, each short by exactly the number of collapsed stars; **10** rejected only by the coincident-hinge clause, all at the FULL target rank — the *Step F4* correction |
| `--strata` | 85 s | HALF 2 over whole strata: `K5` 210/210, 6v/11e 155/155, `K222` 40/40 (seed 20260805), `K4` menu-blocked 438/438 — 843 shapes, 0 failures, exact-ℚ recheck per stratum |
| `--split` | 193 s | HALF 1 at both `e₀` ends of all 8 shapes: antecedent witnessed + nondegenerate, hard-stratum invariants, criterion = observation, both routes escape, escape re-certified as a half-2 witness |
| `--allsplits` | 176 s | HALF 1 at **every** eligible split of the 5-chromatic flank (the ∀ in `hK`) |
| `--pitch` | 65 s | (T1)–(T3) + `Q(r) ≠ 0` at all 16 flank splits (16/16): (K-pitch) closes at each |
| `--rzero` | 84 s | the `dim R_a = 0` stratum at `P21`: 30/5/5 seeds, `dim U = 1`, 8/8 placements fail, and the theta-sub-multigraph stress support (12 edges, line rank 6) |
| `--limit` | 762 s | the (K-slide) FULL-SUPPORT limit carrier at the flanks, 40 generic decorations per shape, first-failure tally per conjunct: witnesses at `W5`, `W7` and the menu-blocked `K4` (seed 101, `dim mot = 9`); **none** at `K5` (W3 27/27), 6v/11e (W2 30/30), `K222` and `K5+v` (W4 30/30), `P21` (W1 35/35) |

**Confidence verdict: HALF 2 — the pencil conjecture at the uncovered flanks
— is PROVEN-INFORMALLY per shape** (exact nondegenerate witnesses at the Tay
target; 8 named shapes + 843 stratum shapes, 0 failures), so **no
counterexample exists at the shapes most likely to carry one and the disproof
risk is removed** — the **class-uniform** target theorem is *not* thereby
established (nothing in this section is uniform: (i) and Step F7 item 1);
**HALF 1 — `hK` at the flanks — carries no counterexample and needs no
re-pin** (16/16 `e₀`-end splits and every eligible split of the 5-chromatic
flank escape on both routes, with the (K-tight) criterion matching seed by
seed), with the strict caveat that the chart-level restatement rests on the
partly-landed re-seeding lemma; **(K-pitch) closes at every flank split**
(16/16 non-null transmitted wrenches); **the geometry of `G` is unobstructed at
the flanks while BOTH degenerations are obstructed there** — the tetrahedral
alignment (§(K-slide-comb), already known) and now, newly, the **full-support
slide-in limit** at all four structural flanks (uniform per-shape failure
profiles over 30-odd generic decorations each; **reduced** supports were named
here as the follow-up and were probed the same day by direction C, which
recovers 5 of the 6 flank shapes — §(K-pure) *Step P7*), against which three
previously-uncovered shapes —
the two wheels and a **menu-blocked `K4` shape** — do carry full (W1)–(W4)
limit witnesses and so join the (K-slide) battery; and **a ∀-realization escape
statement is REFUTED at `P21`** by an exhibited `dim R_a = 0` seed whose forced
failure confirms a (K-tight) prediction never before tested. **Class uniformity
is untouched** — this pass removes a disproof risk and adds mechanism data; it
closes no uniform gap.
