# PENCIL — strategic assessment and route candidates (post-fan-out)

**Status: written 2026-08-05, immediately after the three-way kernel-(K) research
fan-out landed (A `0ee85777`, C `e38eb6b5`, B `7b4422dd`). Not mathematics — this
is a *strategy* document.** It answers one question the fan-out forced: *why does
class uniformity of the escape keep resisting, and is there a tool we have not
tried?* It exists so a fresh session can pick the phase's direction without
re-deriving the diagnosis from three workbook arcs and eight dispatch days.

Reading order for a fresh session: `notes/Phase39.md` *Current state* (status +
the standing adjudications), then this file (why the wall is where it is, and the
candidate routes), then `notes/Pencil-informal.md`'s **State of (K)** gap map
(the canonical per-gap status). The mathematics is **not** restated here; every
claim below points at the workbook section that owns it.

**Nothing here is adjudicated.** The phase direction was with the user when this
was written. §4's candidates are *derivations*, not verified routes — each needs
a recon or a spike before it can be priced.

## 1. The two questions this doc answers

1. **Why does class uniformity resist?** Five structurally different routes have
   now failed: route 1 (locality), route 2 (pointwise reuse), the naive
   collinear collapse, the tetrahedral collapse (antecedent *and* statement),
   and the un-specialized pure condition. That is a recurring wall one level
   above any single route, so the question is whether the wall is intrinsic.
   (§4-C1, the candidate this doc rated best, has since been run and is a
   **sixth** — `notes/Pencil-informal.md` §(K-dom) *Step D6*: it relocates the
   crux from `Q(z) ≢ 0` to `rank dV = 9`, a strictly stronger and equally
   per-shape determinantal condition, so §2.2's diagnosis survives it intact.
   That is one prediction of this doc's own analysis confirmed by a driver.)
2. **Did the KT formalization yield extractable technique that generalizes?**
   This was a stated goal of opening the phase. §3 gives the ledger.

## 2. Why class uniformity resists — a three-ingredient diagnosis

### 2.1 The mechanism that normally works

Every combinatorial-rigidity theorem this project has formalized (Laman, Tay,
Lovász–Yemini, the `k`-frame matroid, tree packing) runs on three ingredients:

1. **An irreducible parameter space**, so "generic" is well-defined and *one*
   witness certifies generic behaviour.
2. **The condition is a rank condition indexed by subsets of a ground set.**
   "Rank `≥ r`" is "some `r×r` minor `≢ 0`"; because the minors are
   subset-indexed and satisfy exchange, independent sets form a **matroid**.
3. **A min-max theorem for that matroid** (Edmonds partition, Nash-Williams
   packing) converting independence into a *count*.

Ingredient 2 is where geometry actually becomes combinatorics. Combinatorics
does not enter because the condition is "polynomial `≠ 0`"; it enters because
the polynomials are *subset-indexed determinants of one fixed matrix*.

### 2.2 Which ingredient the pencil pin costs

**Ingredient 1 survives**, and that is why the per-shape story works so
smoothly: the pencil chart is irreducible (a tower of affine-linear fibres,
§(K-slide) *Step 1(e)*), so one exact witness settles a shape. This is the logic
behind §(K-flank)'s `∃`-witnesses and (S1)'s one-witness rule.

**Ingredient 2 fails for (W4)**, and §(K-pure) localizes exactly how. The needed
condition is `Q(z) ≠ 0`. That *is* a "polynomial `≢ 0`" statement — `z` is a
cofactor expression — but it is **one polynomial per (shape, split)**, not a
subset-indexed family over a ground set. No exchange, no matroid, no min-max, no
count.

The invariant-theoretic reason it is structural rather than a failure of
ingenuity: a rank condition is invariant under arbitrary change of basis in the
target, whereas `Q` is the **Klein form**, preserved only by a form of `PGL₄`
acting on `Λ²`. Matroid theory is blind to it by construction. §(K-pure) *P5*
states this as "the Klein quadric is invisible to the matroid — it is exactly the
extra structure that makes body-hinge geometry more than body-bar
combinatorics".

This also explains why Tay's theorem was reachable and this is not. In Tay's
setting the quadric enters only in *choosing* the per-hinge subspaces; once
chosen generically the rank is pure matroid union. **The pencil pin is a
quadric-defined degeneracy of that subspace arrangement**, so it lands off the
generic stratum where matroid union computes the answer. §(K-pure) *P6*'s `P21`
exhibit is that in miniature: ambient free bars independent 15/15 and the (C6)
packing present — matroid union says "fine" — yet decoration rows dependent at
every support.

### 2.3 The asymmetry — and it predicts the whole arc's record

Counting is available for exactly **one direction** of the condition needed.

- Proving `R_3`-**dependence** is combinatorial: Maxwell overbracing
  (`|E| > 3|V| − 6`) forces a self-stress at *every* placement.
- Proving `R_3`-**independence** is not: the double banana has
  `|E| = 3|V| − 6` exactly and is still dependent. Independence is where the
  open problem lives.

(PC-OBS) fires on **dependence**. So *the obstruction is combinatorially
certifiable and the non-obstruction is not* — the device failing is provable by
counting; the device working needs a witness. That predicts the record, and the
record complies:

| result | direction | scope |
|---|---|---|
| (K-slide-comb) refuted | negative | class-wide, combinatorial (`χ(K5) = 5`, acyclicity) |
| (K-slide-cl) refuted as stated | negative | class shapes, via Maxwell overbracing of `K5` |
| `ℓ = 5,6` refuted (§(K-Λ) *Step 7*) | negative | structural, every `k ≥ 5` |
| the conjecture at the flanks (§(K-flank)) | positive | **per shape** (8 named + 843 stratum) |
| (S1) battery; §(K-pure)'s 5-of-6 rescues | positive | **per shape / per member** |
| (C6) packing | positive **and** uniform | but it is the *ambient* hypothesis, so it buys nothing |

Every negative is uniform; every positive is per-shape. **That is not bad luck —
it is the asymmetry expressing itself.** Consequence worth stating plainly: what
the arc has accumulated are class-wide *non-existence* facts, and non-existence
facts do not compose into an existence proof.

### 2.4 The whole crux inside one Grassmannian

(PC-Z) lets the crux be restated compactly. `V_bc` is a 3-dimensional subspace
of `Λ²K⁴ ≅ K⁶`, i.e. a point of `Gr(3,6)` (dimension 9). The escape fails iff
`V_bc` meets `α(a)` or `Λ²π̂` — each a *fixed* 3-space, and "meets a fixed
3-space" is the Schubert condition `σ₁`, of **codimension 1**.

So the failure locus is a hypersurface and a *generic* point of `Gr(3,6)` avoids
it: **the conjecture is true for generic reasons.** The entire difficulty is that
`V_bc` is not a generic point — it is the relative twist system of a class-member
graph, hence lies in the image of

>  {class far graphs + pencil realizations} → `Gr(3,6)`,  `H ↦ V_bc`

and **we have no description of that image.** If it were Zariski-dense we would
be done uniformly in one line.

> **Partly answered, 2026-08-05** (`notes/Pencil-informal.md` §(K-dom); the
> mathematics is not restated here). The image is Zariski-dense — the map is
> dominant — at every *class* habitat probed, but its dimension is capped by
> `min(9, 6k − 14)` in the **companion length** `k`, so at `k = 3` it is a
> 4-fold inside the discriminant hypersurface of `Gr(3,6)`. `k = 3` happens
> exactly at the (K-res) `C₆` residuals. Crucially the far graph contributes at
> most `3(k−3)` to that dimension, so §4-C1's "the image grows with the far
> graph" is false and the paragraph's hope of "done uniformly in one line" does
> not survive: density per shape is per shape.

This also restates §(K-pure) *P7*'s locality/pitch trade as a fact about that
map: the degenerations that give combinatorial control **move `V_bc` onto the bad
hypersurface** — that is what (PC-OBS) proves — while the honest chart avoids it
(§(K-flank) F5(c)'s 16/16 `Q(r) ≠ 0` at `ε = 1`) but affords no combinatorial
handle. *Degenerate enough to compute, and you break the thing you are
computing.* §(K-pure)'s two unexplained residuals (`K222` and
`K4 (1,1,3,5,4,4)`, where `V_bc ∩ Λ²π̂ ≠ 0` with no chord stress) are the
sharpest available data on the map's image.

### 2.5 Counting saturation — no count-expressible invariant can help

This rules out a family of would-be invariants, including the most tempting one.

The 2026-07-30 recon established `dim R_a ≥ 2` makes the escape **automatic** —
so "carry `dim R_a ≥ 2`" would convert quadric-avoidance into a *rank* condition
and restore ingredient 2. It cannot work: at tight shapes
`index(G) = 5|E| − 6(|V| − 1) = 0`, which **forces**
`dim R_a = 5 + def(G′) − def(G − v) = 1`. The hard stratum is exactly where the
count pins everything.

And it is worse than uninformative. §(K-flank) *F5(d)* exhibits five legal
nondegenerate target-rank `P21` seeds where the count predicts `dim R_a = 1` and
the geometry delivers `dim R_a = 0`; its own words: "the jump is **geometric**,
i.e. the pencil stratum carries corank the count does not see."

> **On the tight class, counting data is saturated *and* provably blind to the
> discriminating phenomenon.** Any invariant expressible in counting/matroid
> terms is constant where it must vary. This is the crispest form of "geometry
> does not translate here": the translation's source data is already exhausted.

## 3. What the KT formalization gave, and where its boundary is

### 3.1 The reuse ledger is favourable

The phase consumed KT's machinery heavily and successfully:

- R1 confirmed the **carrier material is all in-tree** — the Phase-35
  containment model, the `ExtensorThroughPoint`/`ExtensorInPanel` duality,
  `screwComplementIso` for on-stratum self-duality.
- The W5 arc ran on KT lemmas throughout: Lemma 6.2 and Case II survive with
  pinned choices; Lemma 3.4 supplied the degree-two machinery; Lemma 6.13/4.6
  made the L6/L7 coupling benign; KT 6.5/6.6 (`Contraction.lean:1004/1171`) is
  what W4-L4 traded minimality for feasibility against.
- The counting side is **entirely** inherited — deficiency theory (Phase 19),
  Edmonds partition and matroid union (Phases 12–14). (C6) is Edmonds applied.

`hsplit` closed **in full** on inherited material. The yield was real.

### 3.2 We did not exhaust KT — we reached the boundary of its applicability

What had to be built from nothing is the escape apparatus ((K-tight), (K-pitch),
(K-slide), the collapse, (K-pure), (K-Λ)), and the reason is structural:
**KT never needed an escape, because KT had the panel-only freedom the pencil pin
removes.** The residue is not un-mined KT; it is definitionally the *complement*
of KT's technique. The pin was chosen as the smallest perturbation that breaks
KT's freedom, so the leftover is exactly what KT does not cover.

Calibration for planning: the *unpinned* version of this same question — rank on
the panel/molecular subvariety equals the ambient generic rank — stood open for
decades before Katoh–Tanigawa 2011, and its proof is the machine Phases 17–26
formalized. (The KT 2011 pointer is verified, `notes/Phase39.md` *Citations*; the
original Tay–Whiteley conjecture year is **not** verified — verify before citing
it.) The pencil pin then removes freedom that machine consumes. So the honest
unit for closing `hK` uniformly is *a research programme*, not *a few
dispatches*.

### 3.3 The phase's own extractable technique — obstruction-side

The generalizable yield is real but sits on the obstruction side, not the
construction side:

- **(PC-Z)/(Λ1)** — the isotropic-completion dichotomy, derived twice
  independently (classical α/β classification in §(K-pure); Witt in §(K-Λ)).
  Not pencil-specific: any body-hinge argument where a distinguished reciprocal
  twist's pitch matters can use "pitch vanishes iff the twist system meets one of
  two named isotropic 3-spaces", plus the bracket factorization.
- **(PC-OBS)** — a general theorem on *why degenerations kill pitch*: push chain
  lines through hub points, chords become legal bars, and bar-and-joint
  self-stresses of the **point** framework force pitch vanishing; the governing
  matroid is `R_3`. Applies to any attempt to degenerate body-hinge onto a
  smaller multigraph — a natural thing to try.
- **(S1)** — a reusable transfer pattern: one exact limit witness certifies
  non-vanishing on the whole chart, with the degeneration support a free
  parameter.
- **The locality/pitch trade** — the most transferable item, because it is what
  would save a successor from routes 1–5.

Mapping a method's boundary with proofs is a recognizable contribution. It is
simply not the conjecture.

## 4. Candidate stronger inductive invariants

Framing correction worth recording, because it is easy to get wrong: **the
induction is already the framework.** KT's proof is induction over a generation
theorem (Thm 4.9, Phase 20) plus an algebraic induction over the moves
(Thm 5.5/5.6) powered by a genericity device (Claim 6.4/6.9, Phase 21b); `hK`
sits *inside* that induction as the geometric content of the split step. So the
move is not "add induction" — it is **strengthen the inductive invariant** so the
escape is *carried* rather than re-proved at each shape. The phase has done this
once already: W5-L4's motive gained a **fourth conjunct** precisely because the
first three did not force what the induction needed.

### C1 — dominance of the `V_bc` map (**RUN 2026-08-05; NOT recommended**)

> **Status: the spike below was adjudicated, dispatched and run.** Verdict, in
> one line: **dominance holds (rank 9) at every class habitat probed, but both
> of the two reasons given below for preferring it are refuted, and it does not
> reach class uniformity.** The mathematics — the cap
> `rank ≤ min(9, 6k − 14)` in the companion length `k`, the far block
> `3(k−3)`, `hnoRigid ⟹ k ≥ 4`, the rank table, and the assessment of the two
> claims — is `notes/Pencil-informal.md` **§(K-dom)**, which is the canonical
> home; the *State of (K)* map carries the one-row status. The text below is
> kept as the pre-spike derivation it was, so the two paragraphs of "reasons
> this is attractive" can be read against their refutation.

Carry a statement about the *map* of §2.4 rather than a pointwise condition.
Since the bad locus is codimension 1, it suffices that the image is **not
contained in that hypersurface**; dominance would give it outright.

Two reasons this is attractive:

- **It is inductive in the right direction.** As the far graph grows by a
  generating move, parameters are *added*, so the image can only grow.
  "Dominance is preserved" is a far friendlier inductive statement than "some
  seed escapes".
- **It reframes route 1's refutation as an asset.** The 2026-07-30 locality gate
  is recorded as a negative: the escape's zero locus *moves with the far graph*,
  with sensitivity to a single distance-4 vertex move and stress supported on
  every edge. For a dominance argument that is exactly the wanted evidence — the
  map is highly non-constant. The arc has read that measurement as an obstacle
  for two months because it killed locality reuse.

**The spike (cheap, decisive either way, and nothing in the record does it).**
At one habitat, compute the **Jacobian of `V_bc` with respect to the far
realization parameters and measure its rank against `dim Gr(3,6) = 9`.** Rank 9
at one point proves dominance there; a persistent rank deficiency is itself a
sharp new obstruction. **No CAS needed:** `V_bc` is the solution space of a
linear system with polynomial entries, so each directional derivative comes from
implicit differentiation — a derived linear system solved at the base point in
exact ℚ, inside the existing harness. Scope it as one read-only dispatch with a
new driver under `notes/scripts/w4/`.

Caveat: dominance *at one habitat* is per-shape again. Uniformity still needs
either the induction above or §5's generic-point route.

### C2 — carry `V_bc` general position as a motive conjunct

The direct "carry the crux" move. Two honest problems:

- **Structural.** All four existing `IsNondegPencilRealization` conjuncts are
  **per-body and local** (`Motive.lean:110-115`), whereas `V_bc` is a global
  object of a *vertex-deleted subgraph*. The conjunct would quantify over
  subgraphs — a different and heavier kind of statement.
- **Satisfiability, with local precedent.** A stronger motive can be
  unsatisfiable: `PencilNondegFeasible` is refuted at `K4`, and L6b's
  `hcard`-only pin was refuted at first build contact (dispatch-log F10). **Run
  a satisfiability trace against the consumer's actual object before building
  anything on this** — the standing CLAUDE.md rule for deferred-hypothesis
  leaves.

### C3 — the mixed stratum: weaken the theorem so the hard case moves

Not an invariant; it changes which case is hard. Currently the target is
all-bodies-pencil, and `notes/Phase39.md` *The question* notes mixed versions
follow *from* it by semicontinuity. Run that backwards: pin only a subset `S` of
bodies to pencils, generic elsewhere. Then at each reduction step one may be able
to **choose the split vertex outside `S`**, where KT's full freedom is intact —
reducing the problem to *can the combinatorial reduction always avoid `S`?*, a
combinatorial question about the already-formalized generation theorem.

This is strictly weaker than the conjecture and follows from nothing already
proved. But it is the **chemically realistic** statement (real molecules have
*some* sp²/planar-bonded atoms, not all), and `S = V` recovers the full case. It
is not on the phase's candidate list. The obvious risk: the reduction consumes
vertices, so it may be forced into `S` — a "reduce avoiding `S`" theorem is the
thing to check first.

### Ruled out

`dim R_a ≥ 2`, and every other count-expressible invariant, by §2.5.

## 5. Methodology — symbolic computation

### 5.1 What the harness does today

`notes/scripts/` is **exact ℚ** (`fractions.Fraction`, no floating point
anywhere), **stdlib-only** Python. Verified 2026-08-05: no CAS has ever been used
in this repo — zero references to sympy / Macaulay2 / Gröbner / numpy / scipy in
`notes/` or `CombinatorialRigidity/`; sympy is not installed.

The only symbolic capability is **hand-rolled and univariate**: `pitch.py`'s
`lagrange_coeffs`, with `lambda.py`'s `poly_of` / `scal_poly_of` / `poly_deg` /
`vec_poly_deg` / `qpoly` on top. Exact polynomial arithmetic **in one variable**,
recovered by interpolation from rational samples — that is how `ω⁺(t)` gets
degree `≤ 3` along the `a`-line, how the placement quartic was found, and how
`Q(z(t)) ≡ 0` is certified. **No multivariate polynomial arithmetic, no ideals,
no elimination, no generic-point computation.**

### 5.2 What sampling can and cannot establish — and why that matters

Sampling exact rational points can **prove** `≢ 0` at a *fixed* shape (one
witness + chart irreducibility — this is why §(K-flank)'s per-shape results are
genuine proofs, not evidence) and can **refute** identical vanishing. It can
**never** establish a statement uniform over an infinite family.

> The methodological limit mirrors the mathematical one. The toolchain is
> perfectly matched to the per-shape results the arc produced, and structurally
> incapable of the uniform result the phase wants. §2.3's
> uniform-negatives/per-shape-positives table is the same fact seen from the
> mathematics side.

### 5.3 Where a CAS would buy something sampling cannot

**The concrete one, available now.** §(K-Λ)'s (Λ0) argument says each clause is
an open condition on the **local frame's** chart, "the same irreducible variety
for every class habitat carrying a length-4 companion", so exact witnesses across
finitely many strata certify (Λ0) generically for the whole class. That is the
one argument in the arc whose logical form is *generic-point computation per
stratum ⟹ uniform over the class* — implemented as **164 sampled rational
frames**. Treating the frame coordinates as indeterminates and computing the
spans over the function field would **turn that evidence into a proof, uniformly
over the class**. First place symbolic tooling reaches something sampling
structurally cannot.

**Others, in rough order of value.** (i) Is the pullback of the bad
hypersurface's equation identically zero on the image of the `V_bc` map? — an
elimination question, and the exact form of §2.4's open problem. (ii) Verify
(Λ1)'s 16-entry bracket identity symbolically rather than per-frame. (iii)
(K-chord)/`R_3` questions for parameterized families.

**Why this is plausible rather than fantasy:** Gröbner blowup makes whole-graph
symbolic work hopeless (a `|V| = 31` shape carries ~120 point coordinates), so it
is viable only on the **local frame** — 6 points, two panels, a meet line — which
is precisely where §5.3's first item lives.

### 5.4 Macaulay2 — availability and the conventions it would need

`M2` is on `PATH` and **runs in the sandbox today**: verified 2026-08-05 by a
`M2 --script` Gröbner computation from a temp directory. Only the
run-in-a-temp-dir pattern is confirmed; reading/writing inside the repo may need
sandbox directories added.

Introducing it is a **new harness layer** and needs its own conventions before
the first figure is quoted:

- **Status of its output.** Evidence for the workbook, at the same standing as
  the numerics — **never** a substitute for Lean. The project formalizes
  everything its argument uses (`DESIGN.md` *Formalize everything the argument
  uses*); "verified in Macaulay2" is not a proof the project may cite in place
  of a formalization.
- **Reproducibility.** `notes/scripts/README.md`'s *Hard rule — figures do not
  move* must extend to it: pin the M2 version, make every run deterministic and
  seed-printed, and add each invocation to §3's table. An external binary is a
  reproducibility surface the current rules do not cover.
- **Placement.** A `notes/scripts/m2/` directory with its own README, named in
  §2's layering map. The README's opening "stdlib-only Python" line needs
  amending, and the *Divergences* discipline should be extended to any primitive
  reimplemented on the M2 side.
- **Do not port existing drivers.** Figure invariance and the frozen invocation
  paths mean M2 is *additive* — for new questions only.

## 6. Hand-off

The phase direction was **awaiting user adjudication** when this was written;
`notes/Phase39.md` *Current state* is authoritative for the standing
adjudications (W4 parked; option B not commissioned; `hK`/`hbareSplit` carried).
Conditional first steps, so a fresh session can start immediately once the
direction is set:

- ~~**If the direction is C1 (dominance):** the §4-C1 Jacobian spike~~ —
  **DONE 2026-08-05** (adjudicated, dispatched, landed; driver
  `notes/scripts/w4/dominance.py`, mathematics in `notes/Pencil-informal.md`
  §(K-dom)). Rank **9** at every class habitat probed, **4** (a proven cap) at
  the `k = 3` (K-res) family; C1's inductive and locality-reframing claims both
  refuted, so C1 is **not** a route to uniformity and is not a live direction.
- **If the direction is the symbolic upgrade:** §5.3's first item — re-do
  §(K-Λ)'s (Λ0) spans at the generic point of the local frame in Macaulay2, and
  land §5.4's conventions in the same commit as the first M2 driver.
- **If the direction is C3 (mixed stratum):** first question is combinatorial and
  needs no geometry — can KT's reduction always avoid a prescribed vertex
  set `S`? Read Phase 20's generation theorem before scoping.
- **If the direction is to bank the buildable Lean:** W4 is fully decomposed;
  **W4-L4b** (`exists_degree_two_of_co1_rigid`) is the pinned next commit — see
  `notes/Phase39.md` *Hand-off*. This requires a fresh adjudication, since the
  2026-08-05 park is standing.
- **If the direction is to close the phase:** the conditional headline
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` plus this record is
  what ships; run `PHASE-BOUNDARIES.md` *When this commit closes a phase*.

## 7. Provenance

§§2–4 are a coordinator-authored synthesis (2026-08-05) of the three fan-out
returns plus the arc's prior record, produced in discussion with the user at the
end of the fan-out session. Every mathematical claim traces to a workbook section
or a landed commit named inline; the *diagnoses* (§2.3's asymmetry, §2.4's
Grassmannian framing, §2.5's saturation argument, §4's framing correction) are
new synthesis and carry no driver — they are arguments, and a successor should
attack them rather than assume them. §5's facts about the harness and Macaulay2
were verified against the tree and the sandbox on the day.

Classical facts named without a bibliographic pointer, per the project's
"classical" convention: Witt's theorem, the α/β classification of the Klein
quadric's maximal isotropics, the Schubert codimension count, Maxwell's count,
and the double banana. **One unverified lead**, recorded so it is not mistaken
for a route: conditions about *isotropic* subspaces and their intersections are
the subject of the Δ-matroid / orthogonal-matroid literature (Bouchet and
successors), which is the only place I know of where "combinatorics that sees a
quadric" is the topic. **No specific theorem there has been checked against this
problem** — treat it as a literature-recon question, not a candidate route, and
verify any citation before writing it into a chapter.
