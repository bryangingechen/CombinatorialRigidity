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

**Labels.** §4's **C1/C2/C3** (candidate invariants) and §4.6's **U1/U2/U3** are
this file's own family; `C1`–`C3` collide with two unrelated `(C·)` families in
the workbooks, which is why §4.6 minted `U1`–`U3` rather than continuing the
letter. The registry and the minting rule are **`notes/Pencil-labels.md`**.

**Nothing here is adjudicated.** The phase direction was with the user when this
was written. §4's candidates are *derivations*, not verified routes — each needs
a recon or a spike before it can be priced.

> **§4.6 was added later the same day** by a separately-commissioned broad recon
> on class uniformity itself — the phase's crux, untouched by all seventeen
> docs+scripts passes. It carries **six refutations** (`∀λ`, cluster structure on
> `Gr(3,6)`, moment-curve/positivity, a codimension comparison, definable choice,
> and a bonus sixth) and a **ranked three-entry live shortlist** (`U1`–`U3`), each
> with its cheapest decisive experiment and what would kill it. Start there
> before §4's C2/C3.

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

> **Confirmed from outside the subject, 2026-08-05.** The one literature where
> "combinatorics that sees a quadric" is the *topic* — Δ-matroids / orthogonal
> matroids — supplies ingredient 1 (the spinor variety) and ingredient 3 (parity
> min-max, jump systems, union/delta-sum) in quantity, and **still cannot supply
> ingredient 2**: its subset-indexed family `S ↦ Pf(A_S)` is indexed by the
> *ambient* `[n]`, never by the graph. So the sharper statement of this
> subsection is: **the missing ingredient is the ground set, not the min-max.**
> Verdict, hypotheses and sources: `notes/Pencil-informal.md` §(K-Δ).

**The recipe-vs-search framing, which is what §2.3's asymmetry costs in
practice.** KT discharges its per-case seed obligation with **recipes** —
eq. (6.3)'s block-triangular construction, the 1-extension normal form:
*formulas*, valid at every instance of a case, which is exactly why they are
automatically uniform. The pencil arc discharges the same obligation with a
**per-shape search** — §(K-flank)'s 8 named + 843 stratum witnesses, each a
genuine proof by chart irreducibility, and each found rather than written down.
**A search does not carry a reason.** In one line: *we can build any seed you
name; we cannot write the function that builds them.* Every "per-shape positive"
in the table above is a search result, and that is why none of them composes.

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

> **Four objects, and the conversation kept conflating them** (coordinator
> scrutiny, 2026-08-05; the mathematics and the connection it makes are
> `notes/Pencil-informal.md` §(K-ind) *Step I0*, which is the canonical home).
> **(1)** `V_bc(p)` is a **point** of `Gr(3,6)`, not a locus. **(2)** The
> graph-dependent object is the **map** `φ_G : chart(G) → Gr(3,6)` and its
> **image** — the thing this subsection says we have no description of.
> **(3)** The bad locus `B ⊆ Gr(3,6)` is the union of two Schubert divisors,
> each the *hyperplane class* in the Plücker embedding, so `B` is cut by a single
> degree-2 form **factoring into two hyperplanes** — and `B` is
> **graph-independent**. **(4)** `F = φ_G^{-1}(B) ⊆ chart(G)` is a hypersurface
> exactly when `hK` holds there, the whole chart when it fails. *The connection:*
> that global factorization is the shadow of §(K-Λ) **(Λ1)**'s local result
> (`Φ_loc` always rank 2, a product of two rational linear forms) — **the two
> computations are the same geometry at two scales.**

This also restates §(K-pure) *P7*'s locality/pitch trade as a fact about that
map: the degenerations that give combinatorial control **move `V_bc` onto the bad
hypersurface** — that is what (PC-OBS) proves — while the honest chart avoids it
(§(K-flank) F5(c)'s 16/16 `Q(r) ≠ 0` at `ε = 1`) but affords no combinatorial
handle. *Degenerate enough to compute, and you break the thing you are
computing.* §(K-pure)'s two unexplained residuals (`K222` and
`K4 (1,1,3,5,4,4)`, where `V_bc ∩ Λ²π̂ ≠ 0` with no chord stress) are the
sharpest available data on the map's image.

> **That wall now has a proof, in the one case where a symmetry looked like an
> escape from it** (2026-08-05; `notes/Pencil-informal.md` §(K-σ) *Step σ6*).
> A **σ-equivariant seed recipe** — build the seed as a fixed point of the
> polarity, so uniformity comes free — is dead: over `ℝ` with the project's
> *definite* polarity there is **no σ-fixed pencil configuration at all**
> (`normal_v ∝ point_v` plus the landed incidence conjunct forces
> `point_v · point_v = 0`), and for a general correlation the fixed locus is
> worse than empty, it is degenerate — a **null** correlation makes the incidence
> automatic but forces every hinge line into a **linear line complex**, giving a
> self-stress per independent cycle. Measured on tight `C₆`: **deficit exactly 1
> at 6/6**. Exactly this subsection's trade, with a witness. (The *candidate*
> route σ escapes it by applying `σ` **once**, to move to a different seed —
> it never asks for equivariance.)

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
  `screwComplementIso` for on-stratum self-duality — the last **only over `ℝ`**,
  which §(K-σ) *Field scope* records as an open gap against the field-general
  `hK`.
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

### 4.6 The broad class-uniformity recon (2026-08-05) — six refutations, three live successors

**Status: assessment only.** No mathematics is landed by this subsection, **no
driver was run**, and **no *State of (K)* row moves**. Commissioned to look
outside the arc's habits at the one thing seventeen docs+scripts passes never
touched — class uniformity itself — with four coordinator seeds explicitly
offered as unverified hypotheses. **All four seeds die**, as do the invited
definable-choice reading and a bonus sixth idea of this pass's own; the most
useful output is that two of them die for the *same* reason as §7's Δ-matroid
lead. Read the refutations first; the live shortlist that follows is short on
purpose, and its three entries **interlock** (one target, one machine, one
logical form) rather than being independent bets.

**The test every candidate must pass, stated once.** §2.2's missing ingredient,
sharpened by §(K-Δ)'s **(M3)**, is *a ground set that grows with the graph*.
Any proposed structure — literature or homegrown — is a MISS unless its index
set is `E(G)` or something derived from it. Applying that test up front is
cheaper than a hunt, and it is what the two completed hunts should be
remembered for.

#### Refuted or discharged this pass

**(R1) `∀λ` — make the far covector a free indeterminate.** *Refuted as a new
route, because it is already proven.* The `∀λ` statement is not merely true:
it **is** §(K-Λ)'s *Theorem (Λ-completeness at length-4 companions)*, and it is
already class-uniform — for every `λ ∈ P(S*)` outside **two named points** the
escape holds, and the statement names no graph, no habitat and no stratum. So
"class uniformity may contain no graph quantifier at all" is half right in a way
that is worth stating precisely: **the criterion has no graph quantifier and is
discharged; the graph quantifier lives entirely in the *realizability* of `λ`.**
That is §5.3's boundary restated, and the pattern is now a third instance —
C1 relocated the crux from `Q(z) ≢ 0` to `rank dV = 9`; `∀λ` relocates it to
"`λ ≠ p⁺` is realizable". *Sub-questions, both answerable from the record:*
`lambda.py --adv`'s failure to find `λ ∝ p⁺` is **non-realizability, not
non-existence** — `p⁺` is a covector that manifestly exists, and §(K-Λ) *Step 4*
already says a hit would be a **counterexample to the pencil conjecture** at
that habitat, i.e. `--adv` is a disproof hunt, not an existence question. And
the M2 feasibility question is **already answered by a landed run**:
`m2/lambda1.m2` block **(M4)** is the gauged local frame *with `λ` free*, and
it finishes; the 600 s kill is the *ungauged 28-point* expansion, not the
`λ`-indeterminate one. Nothing new to compute here.
*The residue is live and is entry **U1** below.*

**(R2) Cluster structure on `Gr(3,6)`.** *Refuted, and it is (M3) verbatim — a
third MISS for the Δ-matroid reason.* The literature is real and verified:
Scott, *Grassmannians and Cluster Algebras*, Proc. London Math. Soc. **92**
(2006) 345–380, DOI 10.1112/S0024611505015571, classifies the finite-type
Grassmannians; `Gr(3,6)` is the type-`D₄` case (6 frozen + 16 mutable cluster
variables). **Correct the seed's parenthetical:** `Gr(3,6)` is *not* the
smallest Grassmannian of finite cluster type — every `Gr(2,n)` is finite type
`A_{n−3}` — it is the smallest one **outside the `Gr(2,n)` series**. Three
independent failures, any one fatal:
- **Ground set (M3).** The cluster structure's index set is the ~22 cluster
  variables of the *ambient* `Gr(3,6)`, fixed by `dim Λ²K⁴ = 6`. It never grows
  with the graph. This is §(K-Δ)'s (M3) with a different subject line.
- **Wrong group.** The cluster structure is an `SL(6)`/Plücker structure; the
  geometry here is `PGL(4) ⊂ SO(6)` preserving the Klein form `B`. A mutation
  does not preserve `B`, so exchange relates quantities that are not
  simultaneously meaningful for the escape. The cluster labelling also depends
  on an *ordering* of a basis of `K⁶` that no part of the geometry supplies.
- **It re-derives what the arc already has.** Because `α_{pt(a)} ∩ β_{π_a} = T`
  is 2-dimensional, a basis `e₁,e₂` of `T` extended by `e₃ ∈ α`, `e₄ ∈ β`
  makes both Schubert conditions **single Plücker coordinates**
  (`V ∩ W ≠ 0 ⟺ p(V) ∧ p(W) = 0`), so the bad locus is the product of two
  Plücker coordinates. That *is* §(K-ind) *I0*'s "degree-2 form factoring into
  two hyperplanes" and §(K-Δ)'s (N1)/(N2) "two Wick coordinates nonzero", in a
  basis-dependent costume. No new information.

**(R3) Moment curve / total positivity.** *Refuted in one line, and the line is
worth keeping.* The pencil condition at a body of degree `d ≥ 3` says
`pt(v)` and its `d` neighbour points are **coplanar** — four or more points on
a plane. Four distinct points of a rational normal curve are **never** coplanar
(the bracket is a Vandermonde). So a moment-curve placement of the body points
is the *exact antipode* of a pencil realization: **the canonical
maximally-nondegenerate configuration is incompatible with the pin at every
hub.** That is §2.4's *degenerate-enough-to-compute* wall seen from the other
side, and it is a cleaner statement of it than the arc has. Two salvages
assessed and both declined: (i) placing only the **hubs** on a curve and
choosing branch interiors in the hub planes is compatible — but that is just
the chart's already-known tower structure (§(K-slide) *Step 1(e)*; (Λ0)'s
stratum discussion), and the escape's brackets involve the *constrained* points
`x₁ ∈ Π(b)`, `x₃ ∈ Π(c)`, not the free hub points, so the curve buys nothing
where it is needed; (ii) positivity has **already delivered everything it can**
— at `k = 3` the pitch is a subtraction-free **bracket monomial** (§(K-pitch)
*Step 5*), which is precisely a positivity recipe and precisely why `k = 3`
closes, while at `k = 4` (Λ1)'s factors are *linear in the far covector* and not
bracket monomials, so there is nothing for a sign argument to bite on.

**(R4) Codimension comparison of `D` against the pencil stratum.** *Refuted,
and it can never work — not "it fails asymptotically".* Two counts settle it.
- `codim D = 1` **exactly**. A tight class member is **isostatic**: with
  `5|E| = 6(|V|−1)` and `def = 0` the rigidity matrix has `5|E|` rows and target
  rank `6(|V|−1) = 5|E|`, i.e. it is square modulo the 6-dimensional trivial
  motions, so the deficient locus is the zero set of the **single** White–Whiteley
  pure condition (White–Whiteley 1987, the project-canonical source already
  verified in `notes/Phase39.md` *Citations*), non-vanishing on the panel
  stratum by KT. A hypersurface.
- `codim(pencil ⊂ panel) ≥ 2` at every class member. Panel data is one plane per
  body (`3|V|` parameters, each hinge then forced as `Π(u) ∩ Π(v)`); pencil adds
  a point per body on its own plane and forces `pt(v) ∈ Π(u)` per edge —
  `5|V| − 2|E|` parameters. The naive difference is
  `2(|E| − |V|) = 2(c − 1) = Σ_v max(0, deg v − 2)` (it is `0` on a bare cycle,
  which is the right answer — the pin does not bite there — and `≥ 1` per hub);
  the (K-tight) hard stratum has **both chain ends hubs**, so `≥ 2` wherever the
  question is even posed. Only the `≥ 1` half is load-bearing below; the
  `2(c − 1)` value assumes the `2|E|` incidence equations are independent and is
  flagged as a naive count.

So `dim(pencil) < dim D` at **every** class member. A dimension comparison could
only obstruct containment when `dim(pencil) > dim D`, i.e. when `codim D`
*exceeds* `codim(pencil)` — and `codim D = 1` is the smallest a proper closed
subvariety can have, so the inequality runs the wrong way everywhere, not
asymptotically. The only comparison with teeth would be degree/multiplicity,
which needs exactly the description of `Image(φ_G)` that §2.4 says is missing.

**(R5) Definable choice / quantifier elimination over real closed fields.**
*Refuted, but it points somewhere.* Semialgebraic definable choice does supply
"the function that builds the seeds" — §2.2's missing recipe — **for a fixed
number of variables**. The class has an unbounded number (a `|V| = 31` shape
carries ~120 coordinates), so there is no single formula to eliminate
quantifiers in. The only repair is a **bounded-dimensional intermediary** every
class member factors through, and (T5)/(D2) already supply one: at
`k ≤ 6` the far graph's *entire* footprint is the annihilator
`Λ ∈ Gr(k−3, S_P*)`. So the model-theoretic reading is not a route; it is an
argument for **U1**.

**(R6) Bonus refutation — "choose the split to force a length-4 companion".**
`hK` as landed is quantified `∀` over the split data
(verified at `Escape.lean:555`; the producer `pencilPair_of_splitOff_of_habitat`,
`Escape.lean:334`, in fact *chooses* the pair via
`exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`, so an `∃`-form looks
like it would suffice — **not verified**, and it would be a Lean refactor).
That raises the hope of choosing the split to control `k`. It
**fails at recorded shapes**: in the `K4` double subdivision every branch has
length 3, so every split's shortest companion is `3 + 3 = 6` — `k = 6` at every
available split, which is exactly the value §(K-dom) *D4* records. The
`∀`-vs-`∃` observation itself stands and is Lean-facing; it is **not pinned
here** (the Lean hold is standing) and it is recorded only so a successor does
not re-derive it.

#### The ranked live shortlist

Three entries, labelled **U** (uniformity) rather than continuing the `C`
sequence — the workbook already owns `(C6)`/`(C7)` and the collision would be
real. They are **one object seen three ways** — U1 the target, U2 the machine,
U3 the logical form — and the ranking is by expected value toward *uniformity*,
not by how much is already known.

**U1 (rank 1) — retarget §2.4's image problem from `Gr(3,6)` to the
annihilator, and read the failure off its support.**

*The statement it would prove.* For a class (shape, split) of companion length
`k ∈ {4,5,6}`, let `A(G) ⊆ Gr(k−3, S_P*)` be the image of the far chart under
`p ↦ Λ(p)` in the (D0) FIXED scoping. Then `hK` there is exactly
`A(G) ⊄ Bad_Λ`, where `Bad_Λ` is **graph-independent** and proper. At `k = 4`,
`Bad_Λ` is **two points of `P³`** ((Λ2)), one of which is the route-A escape,
so the target is: *`λ` is not the constant map `p⁺` on the far chart.*

*Why §2's diagnosis does not already refute it.* It is strictly weaker than
(K-dom): dominance asks `rank dV = 9`; the far block attaining its (D2) cap
asks `rank = 3(k−3)`; **this asks `rank ≥ 1` at `k = 4`.** Three nested targets,
and the arc has only ever attacked the strongest. And "non-constant" is not a
determinantal condition — it is the negation of an identity, which is the one
shape a *single named chart move with a bracket formula for `dλ`* can settle,
i.e. a recipe in §2.2's sense rather than a search.

*The concrete criterion it produced — **(OUT)**, whose canonical home is the
workbook.* Because `p⁺` and `q` have their outer entries vanishing
*structurally*, the whole (Λ2) bad set lies on **one line** of `P(S*)`, so the
escape holds by pitch as soon as **one outer companion line is not a relative
twist**. Statement, derivation, the hinge-rate and contracted-graph readings,
the conditionality on (Λ0d) + the widened (Λ0f′), and the confidence verdict:
**`notes/Pencil-informal.md` §(K-Λ) *Step 5a*** — migrated there 2026-08-05 and
**not restated here**, per this file's charter (strategy, not mathematics). The
*State of (K)* map's **(K-wit)** row carries it in its *what would close it*
cell. Two things to keep in view when quoting it in one line: it is
**sufficient, never necessary**, and its hypothesis is a **rank lower bound**,
so §2.3's asymmetry is relocated onto a smaller contracted graph, not evaded.

*And it hands §4-C3 a consumer it did not have.* (OUT)'s sufficient condition is
a **rigidity fact about a contracted framework** — and by §(K-ind) *I6* the
contracted body is *not* a pencil body, so the fact needed lives on the **mixed
stratum**. C3 was recorded as "strictly weaker than the conjecture and follows
from nothing already proved", with no consumer. It now has one.

*Cheapest decisive experiment.* Not another measurement of the *differential*:
that per-shape content is **already measured** (`dominance.py --far`: the far
block attains `3(k−3)` at 5/5 class habitats, so `λ` is not even locally
constant there). What is missing is a *mechanism*, and the concrete deliverable
is **one named far-chart move with a bracket formula for `dλ` valid at every
class member**. Two cheap probes rank ahead of prose, both new driver modes:
report `λ₁, λ₄` (equivalently `C₁, C₄ ∈ V_bc`) over the existing
length-4-companion frames — (OUT)'s hypothesis is **unmeasured anywhere in the
arc** (§(K-Λ) *what would change this* (viii)) — and compute
`deficiency(H/{e₂,e₃,e₄})` over the enumerated length-4-companion class shapes
with the harness's existing `nogood_subdiv.deficiency`, mapping where (OUT) is
even generically available.

*What would kill it.* A class shape at which `λ` is constant on the far chart —
a genuine surprise against (D2)'s attainment, and a sharp new obstruction. Or a
proof that no single move works class-wide, which would make U1 a fourth
relocation. **Honesty flag:** if the move can only be exhibited per shape, this
is another per-shape positive and must be recorded as one. *Scope:* the `k = 4`
reduction to two points is (Λ2), so it needs (Λ0f′) and (Λ0d); at `k = 5` the
bad set is 3-dimensional in a 6-dimensional Grassmannian (§(K-Λ) *Step 7*) and
at `k = 6` the target is `Gr(3,6)` again, so U1's *gain* is graded by `k` and
disappears at `k ≥ 6`.

*One calibration this pass owes the record.* **`k = 4` is exactly the case where
`hnoRigid` is tight.** (D3) proves the split chain plus a shortest companion
close a proper cycle `C_{3+k}`, rigid iff `3 + k ≤ 6`, so `hnoRigid` gives
`k ≥ 4` — and `k = 4` is the *equality* case, the shortest cycle the hypothesis
permits. So the one companion length at which the arc has a complete local
theory (Λ-completeness) is the extremal boundary of the class hypothesis, and
the interior (`k ≥ 5`) is where §(K-Λ) *Step 7* refutes the (T5) frame. Both
populations are non-empty in the arc's own habitat table (`k = 4`: θ(3,4,5),
NT21; `k = 6`: both double subdivisions), which is why **no `k`-graded mechanism
can close the class**, whatever the distribution. A cheap combinatorial census
of `k` over the enumerated class families (877 `K4` shapes, 210 `K5` all-`{3,4}`
shapes, the θ level sets) would refine the distribution; it would **not** change
that verdict, which is why this pass did not run it.

**U2 (rank 2) — the hinge-rate / cycle-space presentation: a ground set that
grows with the graph.**

*The statement it would prove.* Writing a body-hinge motion in **hinge rates**
(`m(u) − m(w) = ω_e C_e` per hinge — the identity §(K-ind) *I3*'s proof already
uses), `mot(H)` modulo the trivial screws is
`Z(H) = {ω ∈ K^{E(H)} : Σ_{e∈Z} ±ω_e C_e = 0 for every cycle Z}`, and
`V_bc = π_P(Z(H))` for any `b`–`c` path `P`. Then `λ` spans
`W ∩ (K^P)*` where `W := Z(H)^⊥` — i.e. **`λ` is the (essentially unique)
element of a linear space on the ground set `E(H)` whose support lies inside the
companion**, so `supp(λ)` is a **cocircuit** of the corresponding linear matroid
on `E(H)`. **(OUT)** (§(K-Λ) *Step 5a*) then reads: *the escape can only fail if
the two **middle** companion edges `{e₂,e₃}` contain a cocircuit.* The target: a combinatorial
obstruction to that, class-wide.

*Why §2's diagnosis does not already refute it.* This is the first candidate in
the arc whose index set is `E(H)` — it **passes (M3)**, which is exactly what
killed the Δ-matroid lead and (R2) above. §2.2's sharper complaint ("the
polynomials are not subset-indexed determinants of one fixed matrix") is also
answered: `W` is the row space of **one** matrix, indexed by (cycle, coordinate)
against `E(H)`. §2.5's counting saturation does not apply: `W` is
realization-dependent, not count-expressible.

*Cheapest decisive experiment.* **The machinery is already committed**:
`dominance.py:cycle_data` builds exactly this `N` (`6c × |E|`, block entry
`(cycle, e) = ± C_e`, `Z = ker N`), currently used only as an independent
cross-check of the differential and **never as a structural lever**. A new
driver (pure addition, so the figure gate discharges by the no-driver-modified
check) computes `λ` in `ω`-coordinates directly and reports `supp(λ)` at every
recorded length-4-companion habitat. A single habitat with
`supp(λ) ⊆ {e₂,e₃}` would be a near-counterexample and the most valuable single
datum available.

*What would kill it.* Two named ways, and the first is serious. **(i)** §(K-pure)
*P5*'s invariant mismatch survives the reformulation: (OUT) factors the failure
into a *support* half (matroid-visible) and a *ratio* half
`p⁺₃λ₂ = p⁺₂λ₃` (Klein-form data, invisible to any matroid). The support half
alone is sufficient for the escape, which is why the entry is live — but if the
support condition turns out **satisfiable** at some class shape, the quadric
half is needed and P5 applies verbatim. **(ii)** If the matroid degenerates to
the 6-fold graphic union, that is the workbook's **(C6)** and §(K-pure) *P6* already says it is the
wrong matroid. **Honesty flag:** "`{e₂,e₃}` contains no cocircuit" is a rank
*lower* bound, so §2.3's asymmetry has **not** been evaded — only relocated onto
a smaller, contracted graph.

**U3 (rank 3) — restate `hK` as a non-existence, so §2.3's asymmetry works for
it instead of against it.**

*The statement it would prove.* For every class (shape, split): the framework
`H` together with a bar along the meet line `M` joining `b` and `c` admits **no
chart-wide self-stress with the bar in its support**. This is (T3) in
contrapositive: the escape fails at *every* seed iff that stress exists at every
seed, and on an irreducible chart Cramer makes its coefficients rational
functions with a **constant support** on a dense open set.

*Why §2's diagnosis does not already refute it.* §2.3's whole content is that
*uniform results in this arc are negatives* — "every negative is uniform; every
positive is per-shape". U3 is the first statement of the target **in negative
form**, so for the first time the target's logical shape matches the shape the
record says is attainable. And the object it denies (a stress with a support)
is subset-indexed, so it inherits U2's ground set.

*Cheapest decisive experiment.* Enumerate the possible constant supports. The
stress lives on `E(H) ∪ {bar}`; because the pencil realization is a *weak-map
specialization* of the generic one, the support need not be a generic circuit —
that is precisely §(K-pure) *P6*'s `P21` exhibit — so the honest first step is
prose, not a driver: characterize which supports can carry a chart-wide (rather
than pointwise) stress.

*What would kill it.* If chart-wide stresses turn out to have no more structure
than pointwise ones, U3 is only a change of wording. It is also **adjacent to
the un-commissioned option B** (`[r]` as a chart rational function) and must not
be allowed to become it: U3 is an informal argument about supports, not Lean
infrastructure, and the standing 2026-07-30 NO-GO on option B is unaffected.

#### On a third literature hunt

**Not recommended, and the reason is a theorem-shaped one.** Both completed
hunts (2026-07-30 rigidity-side; 2026-08-05 Δ-matroid-side) fail the (M3)
ground-set test, (R2) makes it three, and the *only* index sets a graph supplies
are `E(G)` and its derivatives — which is rigidity theory, i.e. hunt 1. A fourth
subject would have to be **graph-indexed matroid *deformation*** (weak maps /
specialization-stability of a designated element), which does pass (M3); this
pass could **not name a specific theorem there**, so it is recorded as a lead
with no verified pointer, explicitly weaker than §7's screw-theory pointer and
subject to the same "verify from scratch" rule. §7's standing verdict — *the
right pointer for a successor is "Coxeter matroids, and the reason they don't
apply"* — is unchanged.

## 5. Methodology — symbolic computation

### 5.1 What the harness does today

`notes/scripts/` is **exact ℚ** (`fractions.Fraction`, no floating point
anywhere), **stdlib-only** Python. Verified 2026-08-05: no CAS had ever been
used in this repo — zero references to sympy / Macaulay2 / Gröbner / numpy /
scipy in `notes/` or `CombinatorialRigidity/`; sympy is not installed.

> **Superseded the same day, in one direction only.** The Macaulay2 layer
> `notes/scripts/m2/` now exists (§5.4). Everything above still describes the
> **Python** harness, which is unchanged and whose figures are frozen; `m2/` is
> the single stated exception and is *additive*.

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

**The concrete one — RUN 2026-08-05, and it delivered.** §(K-Λ)'s (Λ0) argument
says each clause is an open condition on the **local frame's** chart, "the same
irreducible variety for every class habitat carrying a length-4 companion", so
exact witnesses across finitely many strata certify (Λ0) generically for the
whole class. That is the one argument in the arc whose logical form is
*generic-point computation per stratum ⟹ uniform over the class* — implemented
as **164 sampled rational frames**. `M2 --script notes/scripts/m2/lambda0.m2`
executes it instead: every (Λ0) clause is now a nonzero polynomial on one
irreducible variety, the containments and `t`-degrees are identities, and the
38 strata are shown *irrelevant at the generic point* (each maps onto a dense
subset of that variety). Mathematics in `notes/Pencil-informal.md` §(K-Λ).

Three things to carry forward from it:

- **It is genuinely class-uniform**, not 38 symbolic strata: the proof names no
  habitat, no stratum, no sample, and a dominant map pulls the dense open
  conclusion back to *every* class habitat's chart.
- **It found a missing hypothesis.** The span criterion is
  `p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0`; the recorded (Λ0f) carries only the first two
  factors, and `g₁₄ = [b,x₁,x₃,c] ≠ 0` is asserted nowhere in the Python
  harness. It is generic, so no sampled frame ever saw it fail — the exact
  failure mode sampling cannot detect.
- **It also marks the method's boundary, and confirms §2.3.** The upgrade works
  because (Λ0) is a statement about the **local frame alone**, where the far
  graph does not appear. (K-wit) — the escape's uniformity — quantifies over the
  far covector `λ`, which the frame deliberately leaves free, so it is not a
  statement on this variety and no generic-point computation on the frame
  reaches it. The symbolic route can make every *far-graph-free hypothesis
  package* uniform and stops exactly where the far graph enters.

**Others, in rough order of value.** (i) Is the pullback of the bad
hypersurface's equation identically zero on the image of the `V_bc` map? — an
elimination question, and the exact form of §2.4's open problem. ~~(ii) Verify
(Λ1)'s 16-entry bracket identity symbolically rather than per-frame.~~ —
**DONE 2026-08-05**, and it was the layer's deliberate first consumer precisely
because its answer was already known, so a mis-configured M2 layer would show
up immediately (`M2 --script notes/scripts/m2/lambda1.m2`; mathematics in
`notes/Pencil-informal.md` §(K-Λ) *Step 2*). It verified, and it came with two
things the per-frame battery could not give: (Λ1) needs **none** of (Λ0) and
none of the panel data, and `rank Φ_loc = 2` is now generic rather than
observed. (iii) (K-chord)/`R_3` questions for parameterized families.

**One measured feasibility datum, from that first driver.** The **ungauged**
end-to-end (Λ1) expansion — all 28 point coordinates indeterminate, degree 52 —
does **not** finish (killed at 600 s). The gauge slice (fix `b, x₁, x₂, x₃` to
the standard basis; `g = [b|x₁|x₂|x₃]⁻¹` is the unique GL(4) element doing so,
so the slice meets every orbit once and the identity transports) runs in ~1 s.
The margin between those two is the practical boundary of this layer, and it
confirms the paragraph below: budget for the *local frame*, never the whole
graph.

**Why this is plausible rather than fantasy:** Gröbner blowup makes whole-graph
symbolic work hopeless (a `|V| = 31` shape carries ~120 point coordinates), so it
is viable only on the **local frame** — 6 points, two panels, a meet line — which
is precisely where §5.3's first item lives.

### 5.4 Macaulay2 — the layer, and its conventions (**LANDED 2026-08-05**)

**The layer exists.** `notes/scripts/m2/`, opened 2026-08-05 together with its
first driver `lambda1.m2` (§5.3 item (ii)); its own README carries the four
conventions below in binding form, and `notes/scripts/README.md` names it in
§2's layering map and §3's invocation table. This section is now a pointer plus
the sandbox record; **read `notes/scripts/m2/README.md` before touching it.**

**Sandbox mechanics — established, not assumed.** The earlier note recorded only
the run-in-a-temp-dir pattern as confirmed and flagged repo-internal I/O as
possibly needing sandbox directories added. Re-verified directly on 2026-08-05,
and it is better than that: `M2` is on `PATH` (version **1.26.06**), a
`M2 --script` on a path *inside* the repo runs with `currentDirectory()` = the
repo root, and M2 can both **read and write** files inside the repo (probed by a
write / read-back / `removeFile` round trip and by reading a tracked file). No
sandbox directories had to be added, and M2 does not need its application
directory to exist. A failing `assert` exits **non-zero**, so an M2 driver
satisfies the harness's "non-zero exit or missing verdict line = failure" rule
directly.

The four conventions, as landed (full text: `notes/scripts/m2/README.md`):

- **Status of its output.** Evidence for the workbook, at the same standing as
  the numerics — **never** a substitute for Lean. The project formalizes
  everything its argument uses (`DESIGN.md` *Formalize everything the argument
  uses*); "verified in Macaulay2" is not a proof the project may cite in place
  of a formalization, and no blueprint node may take `\leanok` on the strength
  of an M2 run. Written first in that README because it is the convention most
  likely to erode: M2 output *reads* like a proof in a way a table of sampled
  ranks does not.
- **Reproducibility.** The M2 version is **pinned (1.26.06) and printed as every
  driver's second output line**, so it is part of the figure and an upgrade
  shows up as a diff rather than as a silent change of meaning; every run is
  deterministic and prints `randomness: none`; each invocation is in
  `notes/scripts/README.md` §3. The re-baselining procedure after an M2 upgrade
  is spelled out there (re-run, require every line but the version line
  byte-identical, move the pin in the same commit; any other moved line is a
  genuine figure change and goes through the workbook).
- **Placement.** `notes/scripts/m2/` with its own README; the harness README's
  opening "stdlib-only Python" line now names it as the single exception. The
  *Divergences* discipline is extended across the language boundary: an M2
  driver cannot import a §1 primitive, so every re-derivation is a divergence
  *candidate* and must name its Python home and be pinned by an in-driver check
  (`lambda1.m2`'s (M0) and its `cross4` argument-order check).
- **Do not port existing drivers.** M2 is *additive* — for new questions only.
  `lambda.py --witt` keeps its 23 frames and its figures unchanged; the M2
  result is recorded as an **upgrade of the confidence verdict**, with both
  cited.

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
- ~~**If the direction is the symbolic upgrade:**~~ **DELIVERED 2026-08-05.**
  §5.4's conventions plus `lambda1.m2` ((Λ1), item (ii), the deliberately
  low-risk first consumer) landed first; `lambda0.m2` then closed §5.3's *first*
  item — (Λ0) and the `a`-line spans at the generic point, class-uniform, plus
  the missing `g₁₄` clause. The feared cost did not materialize: the `a`-line
  parameter `t` never joins the indeterminates, because `ω⁺(t)`, `ω⁻(t)` are
  *structurally* cubic and quadratic in `t`, so their coefficient vectors come
  from finite differences of integer evaluations and the whole run is ~0.1 s.
  **What remains of §5.3** is item (i) — the elimination question, "is the bad
  hypersurface's pullback identically zero on the image of the `V_bc` map?",
  which is §2.4's open problem and is *not* far-graph-free — and item (iii),
  (K-chord)/`R_3` for parameterized families.
- **NEW, 2026-08-05 — if the direction is to verify route σ:** the single
  concrete commit is **σ-nondegeneracy of the transported seed**
  (`notes/Pencil-informal.md` §(K-σ) *Step σ5* obligation 1) — the one crux the
  candidate rests on, with a named repair against landed machinery
  (`exists_common_seed_pencilRow_and_polynomials`, `Engine.lean:476`, whose own
  docstring already names this consumer shape). **Its numerics half landed the
  same day** (`sigma.py --hunt`, §(K-σ) *Step σ4b*): the dual conjuncts are
  **not** implied — 53 constructed hard-stratum, primally-nondegenerate
  counterexamples — but two of the four are free **at `ℝ`**, one is the
  already-named (Λ0d), and the steering is exhibited exactly. What is left is
  **Lean**, and it is held by the standing Lean-hold adjudication.
  **Before picking this direction, read §(K-σ) *Field scope*:** `σ` exists in
  tree only over `ℝ` while `hK` is quantified at general `[Infinite K]`, so the
  Lean half carries a second design decision — discharge at `ℝ` (instantiate the
  headline first) or build a general-`K` polarity. Route σ is a **candidate**,
  not a settled closure; it moves no gap-map row, and whether the rest of it
  should **preempt the mechanisms pass** is an open user adjudication.
- **NEW, 2026-08-05 — if the direction is a class-uniformity attack:** read
  **§4.6** first. Its five refutations are settled (do not re-run `∀λ`, the
  cluster reading, a moment-curve/positivity recipe, a codimension comparison,
  or definable choice), and its three live entries are ranked with the cheapest
  decisive experiment named per entry. The single smallest concrete next step is
  **U2's**: a new driver (pure addition) computing `λ` in hinge-rate
  coordinates from the already-committed `dominance.py:cycle_data` and reporting
  `supp(λ)` at every recorded length-4-companion habitat. **U1** carries the
  pass's one new derivation, **(OUT)** — the escape holds as soon as one *outer*
  companion line is not a relative twist — whose canonical home is
  `notes/Pencil-informal.md` §(K-Λ) *Step 5a*; §4.6 keeps only the strategic
  readings.
- **If the direction is C3 (mixed stratum):** first question is combinatorial and
  needs no geometry — can KT's reduction always avoid a prescribed vertex
  set `S`? Read Phase 20's generation theorem before scoping. **§4.6-U1 gives
  C3 the consumer it lacked:** (OUT)'s sufficient condition is a rigidity fact
  about a *contracted* framework, whose merged body is not a pencil body
  (§(K-ind) *I6*), so it is a mixed-stratum statement.
- **If the direction is to bank the buildable Lean:** W4 is fully decomposed;
  **W4-L4b** (`exists_degree_two_of_co1_rigid`) is the pinned next commit — see
  `notes/Phase39.md` *Hand-off*. This requires a fresh adjudication, since the
  2026-08-05 park is standing.
- **If the direction is to close the phase:** the conditional headline
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` plus this record is
  what ships; run `PHASE-BOUNDARIES.md` *When this commit closes a phase*.

## 7. Provenance

**§4.6 is a later, separately-commissioned recon (2026-08-05), read against the
same record; it ran no driver and moved no gap-map row.** Its refutations (R1)–(R6)
are arguments, not measurements, and each names the landed fact it turns on:
(R1) on §(K-Λ) *Steps 3–5* and `m2/lambda1.m2` (M4); (R2) on §(K-ind) *I0* plus
the Scott citation below; (R3) on the Vandermonde bracket and §(K-pitch)
*Step 5*; (R4) on the isostatic count `5|E| = 6(|V|−1)` with `def = 0`, plus
White–Whiteley's pure condition; (R6) on the `K4` double subdivision's `k = 6`
in §(K-dom) *D4* and on `hK`'s `∀`-quantified split data (`Escape.lean:555`).
Its one *new* derivation, **(OUT)**, was migrated the same day to its canonical
home `notes/Pencil-informal.md` §(K-Λ) *Step 5a* (statement, derivation,
conditionality, confidence verdict, and a *what would change this* item), so
this file states no mathematics of its own — attack (OUT) there, do not assume
it here.

**Project-new source verified this pass** (publisher metadata + the arXiv
preprint listing; **no section pointer is asserted**, per the project's
"classical / no guessed §N" rule): Scott, *Grassmannians and Cluster Algebras*,
Proc. London Math. Soc. **92** (2006), no. 2, 345–380, DOI
10.1112/S0024611505015571 (preprint arXiv:math/0311148) — the classification of
the finite-type Grassmannians. The `D₄` label for `Gr(3,6)`, and
`A_{n−3}` for `Gr(2,n)`, are standard readings of that classification and are
used in §4.6 (R2) only to state what the seed proposed, never as a load-bearing
step.

§§2–4 (excluding §4.6) are a coordinator-authored synthesis (2026-08-05) of the
three fan-out returns plus the arc's prior record, produced in discussion with
the user at the end of the fan-out session. Every mathematical claim traces to a workbook section
or a landed commit named inline; the *diagnoses* (§2.3's asymmetry, §2.4's
Grassmannian framing, §2.5's saturation argument, §4's framing correction) are
new synthesis and carry no driver — they are arguments, and a successor should
attack them rather than assume them. §5's facts about the harness and Macaulay2
were verified against the tree and the sandbox on the day.

Classical facts named without a bibliographic pointer, per the project's
"classical" convention: Witt's theorem, the α/β classification of the Klein
quadric's maximal isotropics, the Schubert codimension count, Maxwell's count,
and the double banana. `deg Gr(3,6) = 42` (§2.4's pointer into §(K-ind) *I0*) is
likewise classical; **the class of the discriminant hypersurface in `Gr(3,6)` is
NOT verified and must not be asserted.**

**The one recorded unverified lead is now CHECKED AND REFUTED (2026-08-05), with
the reason.** It read: conditions about *isotropic* subspaces and their
intersections are the subject of the Δ-matroid / orthogonal-matroid literature
(Bouchet and successors), the only place where "combinatorics that sees a
quadric" is the topic. The literature is real and the *shape* of statement the
phase wants genuinely exists in it — but **two of its three standing hypotheses
fail on `V_bc`, each independently fatally**: its objects are *totally isotropic*
subspaces and `V_bc` never is (an `O(6)`-invariant, not a frame choice), and its
ground set is `[3]`, fixed by `dim Λ²K⁴ = 6`, never growing with the graph.
Full verdict, dictionary, the two readings it does buy ((N1)/(N2)), the
corroborating negative from the current rigidity survey, and a fully verified
bibliography: `notes/Pencil-informal.md` **§(K-Δ)**. Two consequences for this
document: §2.2 is sharpened (*the missing ingredient is the ground set, not the
min-max*), and the right pointer for a successor is **"Coxeter matroids, and the
reason they don't apply"** — a theorem (Witt: `SO₆` has four orbits on
`Gr(3,6)`), not a gap in the literature. One *new* unverified pointer replaces
it, flagged as such: `V_bc` is a **three-system of screws**, and the classical
screw-theory literature (Ball; Hunt; Gibson–Hunt) studies the `O(6)`-geometry of
such systems. It is geometric, not combinatorial, so it would not supply
ingredient 2 either — **verify every citation from scratch before using it.**
