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

**Labels.** §4's **C1/C2/C3** (candidate invariants — C1 and C2 both struck,
C2 on 2026-09-03) and §4.6's **U1/U2/U3** are
this file's own family; `C1`–`C3` collide with two unrelated `(C·)` families in
the workbooks, which is why §4.6 minted `U1`–`U3` rather than continuing the
letter. §9's **(ZH-1)–(ZH-6)** are the third, minted 2026-08-21 and topic-tagged
per clause (L5). The registry and the minting rule are
**`notes/Pencil-labels.md`**.

**Nothing here is adjudicated.** The phase direction was with the user when this
was written. §4's candidates are *derivations*, not verified routes — each needs
a recon or a spike before it can be priced.

> **§4.6 was added later the same day** by a separately-commissioned broad recon
> on class uniformity itself — the phase's crux, untouched by all seventeen
> docs+scripts passes. It carries **six refutations** (`∀λ`, cluster structure on
> `Gr(3,6)`, moment-curve/positivity, a codimension comparison, definable choice,
> and a bonus sixth) and a once-**ranked three-entry shortlist** (`U1`–`U3`), each
> with its cheapest decisive experiment and what would kill it — **of which
> only `U1` survives as of 2026-09-03** (`U2` struck, `U3` retired by OBAR).
> Start there before §4's C3 — and **not** before C2, which is struck as a
> uniform carry (2026-09-03, direction DSAT; §8.6).

> **Start at §8 (the option board, 2026-08-20)** if you are choosing a
> direction. It prices every live route in one table set — including the two
> filters that kill most candidates on sight — and points back here for the
> mathematics. §§2–5 are the diagnosis and methodology it rests on. **§9 is a
> separate unpriced shelf** (external-technique transfer, 2026-08-21) and is
> deliberately *not* part of the board.

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

> **The wall is structural, not a property of either route — two independent
> passes hit the same object from different directions** (coordinator
> observation, 2026-08-06; neither pass could see this, because neither could
> see the other's residual). The 2026-08-06 fan-out ran directions A and B with
> **no shared machinery** and unrelated targets — A a class-uniform bracket
> formula for `dλ` (`§(K-ann)`), B the outer-line criterion (`§(K-out)`). Both
> terminated on a residual of the *same* shape, and the coincidence is tighter
> than "both are rank lower bounds", which would be generic:
>
> - **(ANH-R1)** `τ_β ≠ 0` at the pencil placement, i.e. `H/P − β` is
>   pencil-rigid — a contraction of the far graph `H` by the welded companion.
> - **(OC-8)** `L_b ⊄ R₁` (or the `c`-mirror) on the pencil chart of
>   `H/{e₂,e₃,e₄}` — a contraction of the far graph `H` by three companion
>   edges.
>
> Both are **pencil-rigidity of a contraction of `H`**, and both are the *lower*
> bound direction of this subsection's asymmetry. So the residual is not an
> artifact of how either route was set up: §2.3's wall has been **relocated and
> weakened twice, from two directions, and crossed neither time**.
>
> **A prediction, recorded so it can be checked rather than admired.** A third
> independent route should terminate the same way. If the next pass's residual
> *is* again a rank lower bound on a contraction of `H`, stop looking for routes:
> the productive target becomes the wall itself — *why do rank lower bounds at
> pencil placements resist on contracted far graphs?* — which is a question about
> one object, not a survey of approaches. If the next residual is **not** of that
> shape, that is the genuinely informative outcome and it deserves the attention
> a surprise deserves.

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
>
> **Scoping clause, added 2026-09-03.** The two sentences above read as
> self-contradictory — a 4-fold cannot be dense in the 9-fold `Gr(3,6)` — and
> that apparent contradiction cost direction GELIM its opening. They are not:
> **every *class* habitat has `k ≥ 4`** by (D3)'s `hnoRigid ⟹ k ≥ 4`, where
> `min(9, 6k−14) = 9` and the cap is **vacuous**; the 4-fold `k = 3` images are
> **(K-res)** residuals, outside the pinned class. §(K-dom)'s own words:
> *"(D1) is vacuous on the pinned `hK` class and bites exactly on the (K-res)
> half."* And do **not** read the `k = 3` containment as bearing on `B`: it is
> containment in the **discriminant** `{det Gram_B = 0}` (a serial chain has
> `rank B|_{V_bc} = 2` identically), a *different* degree-2 Plücker form — at
> `k = 3` the image lies in `D` **always** and in `B` **never** (6/6, (D4)).

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
>
> > **That last sentence is an ASSERTED identification, not a proved one** (flagged
> > 2026-09-03, direction GELIM). The claim it makes precise is that the two linear
> > factors of `Φ_loc(λ)`, `(λ·ω⁺)` and `(λ·ω⁻)`, **are** the pullbacks of the two
> > Schubert hyperplane forms cutting `B`. **No driver or workbook step proves it** —
> > §§2–4 of this file are coordinator-authored synthesis and carry no driver
> > (§(K-dom)'s opening says so). It is **cheap** to settle: a gauge-sliced identity in
> > exactly `m2/lambda1.m2` block **(M4)**'s regime, which finishes. It is also **worth
> > nothing to status**: proving it upgrades an analogy to an identity and leaves
> > realizability untouched on both sides. Recorded so a successor neither *inherits* it
> > as a fact nor spends a dispatch *proving* it expecting a gap-map move.

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

> **GATE ON THIS WHOLE SECTION, added 2026-09-03 (RESEARCH-ARC §8 liveness
> sweep).** *Kill condition: no move of the phase's induction relates two class
> members, so there is nothing along which to carry an invariant.* **It has
> fired.** §(K-ind) **(I1)/(I2)/(I4)** prove exactly that — tight ⟺
> `(|V|,|E|) = (5c+1, 6c)`, so two tight graphs of equal cycle rank have equal
> size and **no arm of `pencil_reduction` can relate them**; the *Shared
> dictionary* carries it as a do-not-re-open. So a C-entry is dispatchable only
> if it **first exhibits such a move**, or abandons *"carried along the
> induction"* for *"true at every member independently"*. C1 and C2 are read
> against that gate below — and **both are now dead on more than the gate**:
> C1 by (D1)'s cap, C2 by its satisfiability trace (2026-09-03, §(K-dom)
> *Steps D8–D14*), each provably false off the class. *Row that decides it: gap-map **(K-ind)**.*
>
> **Re-openability (user ruling, 2026-09-03).** Everything in §4 that is
> recorded as *declined* or *not recommended* is **a past priority call under
> past evidence, not a permanent prohibition** — re-opening one needs a
> **mathematical reason, not permission**. Where an entry is barred by a
> *proof* instead (the gate above; §2.5 for the *Ruled out* family; (AV-3) for
> C3-as-crux-avoidance), it stays barred until that mathematics changes, and
> each such bar names its own kill condition so a successor can see which kind
> it is.

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

Caveat: dominance *at one habitat* is per-shape again. Uniformity needs §5's
generic-point route — **not** "the induction above": §(K-ind) **(I1)/(I4)**
prove no move of `pencil_reduction` relates two class members, so there is
nothing to carry dominance along (liveness sweep, 2026-09-03).
*Kill condition:* a class habitat with `rank dV < 9` at every seed — **none
found**, and gap-map **(K-dom)** *close-it* still names it — or a mechanism
making `rank dV = 9` combinatorially certifiable class-wide. *Row: **(K-dom)**.*
One update the status box above predates: since 2026-08-06 (D2)'s `3(k−3)` has
a **mechanism** rather than a measurement — §(K-ann) **(ANH-1)**, the
annihilator is the self-stress space of the contracted framework `H/P`.

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

> **SUPERSEDED IN PART, 2026-08-06 — §(K-ind) *Step I6* is the canonical home**
> (recorded here by the 2026-09-03 liveness sweep; C2 was the one C-entry
> carrying no status line at all). The first bullet is not the binding
> obstruction. `hcontract` is the only arm that can return to the tight locus,
> and *Step I6* proves the contraction relates `Chart(G)` and `Chart(G/H₀)` by
> **no morphism in either direction** — *"the obstruction is not only that the
> conjunct would quantify over subgraphs — it is that the arm which would have
> to re-establish it has no map to pull it back along."* So C2 is **not
> dispatchable as a transport argument**. What survives is *"prove `Inv` at
> `G/H₀` outright"*, which is a new problem rather than a strengthened
> invariant — **declined, not refuted**, and re-openable on a mathematical
> reason. *Kill condition:* the contraction arm admits no chart morphism
> (**FIRED**, §(K-ind) I6), or the strengthened motive is unsatisfiable at the
> consumer's object (**FIRED TOO, 2026-09-03, direction DSAT** — see the box
> below). *Row: gap-map **(K-dom)**, repointed 2026-09-03 from (K-ind), which
> is where the mathematics now lives.*

> **AND THE SECOND KILL CONDITION HAS FIRED — the trace is RUN, 2026-09-03
> (direction DSAT); §(K-dom) *Steps D8–D14* is the canonical home.** The
> strengthened motive is **UNSAT off the class and SAT on it**, so **C2 is dead
> as a *uniform* carry**. The mechanism: at a degree-2 vertex `a` with
> `N(a) = {b, c}`, `dim V_bc = dim mot(G−a) − dim mot(G) ≥ def₃(G−a) − def₃(G)`
> at every rank-target realization (**(DM-6)**, proven), so
> `def₃(G−a) − def₃(G) ≥ 4` forces `dim V_bc ≥ 4` and hence a nonzero meet with
> both isotropic 3-spaces (**(DM-7)**, proven) — and that trigger fires at both
> (K-res) habitats, which `hK` carries, and at none of the five class habitats
> (**(DM-8)**). **The (K-res) half is PROVED; the class half is MEASURED at
> five shapes.** So the *"prove `Inv` at `G/H₀` outright"* residue this box
> named is **not** refuted, and neither is a class-restricted conjunct — both
> stay blocked by *Step I6* instead. Two corrections this box owed: the
> parenthetical *"never tested … and the 2026-08-05 Lean hold blocks it"* was
> **wrong twice** — the trace is numerics plus a source read, so the hold never
> reached it; and the first bullet's *"quantify over subgraphs"* is now exact —
> the index set is the **degree-2** triples, i.e. adjacent edge pairs, which
> **passes** §4.6's growing-ground-set filter ((DM-5)); what is non-local is the
> conjunct's *value*, `V_bc` being a global object of `G − a`.

### C3 — the mixed stratum: weaken the theorem so the hard case moves

Not an invariant; it changes which case is hard. Currently the target is
all-bodies-pencil, and `notes/Pencil-structure.md` *The question and the opening recon*
(relocated from `notes/Phase39.md` 2026-08-28) notes mixed versions
follow *from* it by semicontinuity. Run that backwards: pin only a subset `S` of
bodies to pencils, generic elsewhere. Then at each reduction step one may be able
to **choose the split vertex outside `S`**, where KT's full freedom is intact —
reducing the problem to *can the combinatorial reduction always avoid `S`?*, a
combinatorial question about the already-formalized generation theorem.

This is strictly weaker than the conjecture and follows from nothing already
proved. But it is the **chemically realistic** statement (real molecules have
*some* sp²/planar-bonded atoms, not all), and `S = V` recovers the full case.
The obvious risk it names itself: the reduction consumes vertices, so it may be
forced into `S`.

> **GATE PRICED, 2026-08-24 (probe C3-AVOID) — §4.7 below is the canonical
> home.** The risk is real and sharper than expected. The *local* gate never
> fails (**(AV-1)**: more than half of every Case-II node's vertices are legal
> split choices), but a **conservation law** (**(AV-2)**/**(AV-4)**) caps
> avoidance at `2 μ(G)`, `μ = |E| − |V| + 1`: the universal threshold is
> **exactly `|S| ≤ 2`** (**(AV-3)**), no structural hypothesis on `S` lifts it
> (**(AV-5)**), and the `|S| = 3` counterexamples are exactly the cycles
> `C_3 … C_6` (**(AV-6)**). C3 is therefore **NO-GO as a crux-avoidance route**
> and stays on the board only **re-scoped**, `μ` measuring how much it buys
> (**(AV-8)**) — and even a passed gate is necessary, not sufficient
> (**(AV-7)**).
>
> **And its consumers are now named and worked** (liveness sweep, 2026-09-03;
> the entry above still says C3 *"follows from nothing already proved"* and has
> *"no consumer"*). The mixed-stratum rigidity facts (OUT) and (ANH-R1) need
> are §(K-out) **(OC-18)** — `H/X` infinitesimally rigid at one chart point ⟹
> (OUT)'s first disjunct, degree-free, at both ends of every class pair
> (5226/5226) — and §(K-ann) **(ANH-R1)** — `H/P − β` pencil-rigid. Both are
> facts about a **contracted, non-pencil** body, i.e. the mixed stratum, and
> both are **pointwise available and neither class-uniform** ((OC-3),
> (ANH-12)). *Kill condition for the re-scoped C3:* a proof that Case-I gluing
> re-imposes the pencil condition on the glued body class-wide — that is
> **(AV-7)**'s open arm. *Deciding surface: §4.7 (no gap-map row, by design)
> plus gap-map **(K-out)** and **(K-wit)** u10.*

### Ruled out

`dim R_a ≥ 2`, and every other count-expressible invariant, by §2.5.
*Kill condition: a count-expressible invariant separating §(K-flank) F5(d)'s
five failing seeds from the thirty escaping ones at the same graph and split —
none found; deciding surface §(K-flank) *Step F5(d)*.* Two sharpenings landed
after this entry was written and are the forms to quote (2026-09-03 sweep):
§(K-shear) *Secondary deliverable* gives the **operative** version — *any
invariant that is a function of the combinatorial data alone is constant where
it must vary, and the count is provably blind to the discriminating
phenomenon* — and §(K-ind) *Step I5*(1) shows a **Jacobian rank** evades the
ruling in form and re-enters it in substance: count-predicted and measured
values coincide at all seven §(K-dom) habitats, so the count is *"saturated as
a predictor and useless as a certificate"*. This bar is **mathematical, not a
priority call**: it lifts only if such an invariant is exhibited.

### 4.6 The broad class-uniformity recon (2026-08-05) — six refutations (permanent), and three successors that are NO LONGER LIVE AS WRITTEN (U1/U3 pursued since 2026-08-06/19, U2 struck 2026-09-03)

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

> **LIVENESS BANNER, added 2026-09-03 — the refutations below are permanent;
> the shortlist below is NOT current.** §(K-out) and §(K-ann) both opened
> **2026-08-06, the day after this subsection was written**, and both are the
> shortlist's own subject matter; §(K-out) has since run to **51 steps across 8
> directions** (O, OCON, ZNEQ, OSCHU, SIGZ, OQRANK, OGEOM, OWALL — the last
> 2026-09-02) and §(K-ann) to **17 steps across 3 waves**. Per entry:
> **U1 ALREADY-PURSUED** (its criterion (OUT) is §(K-out), its retarget is
> §(K-ann), both its named probes ran 2026-08-06); **U2 DEAD** (its own kill
> clause (i) fired at (OC-4) + (OC-3), 2026-08-06); **U3 STRUCK 2026-09-03** (its
> named first step is §(K-out) *Steps O31–O36*, and direction **OBAR** then
> answered its one residue's gate **NEGATIVE** — §(K-out) *Steps O52–O57*). Read *"assessment only"* as a
> statement about **this subsection's own commit**, never about whether its
> entries are unrun. Nothing below is deleted: dead entries are struck with
> cause and date, and the six refutations stand verbatim.

**The test every candidate must pass, stated once.** §2.2's missing ingredient,
sharpened by §(K-Δ)'s **(M3)**, is *a ground set that grows with the graph*.
Any proposed structure — literature or homegrown — is a MISS unless its index
set is `E(G)` or something derived from it. Applying that test up front is
cheaper than a hunt, and it is what the two completed hunts should be
remembered for. *Kill condition: a class-uniform mechanism whose index set does
**not** grow with the graph. Rows: gap-map **(K-Δ)**; workbook §(K-shear),
§(K-jac).* **The test has fired twice more since** (2026-08-26): §(K-jac)
records that the classical bounds on heights of ideals of minors evaluate on
our shapes to the **graph-independent constant `7`**, *"so §4.6's filter fires
too"*; and §(K-shear) records that (ZH-1) died for a **stronger** reason than
the predicted growing-ground-set one — `so₃(k)` is fixed-dimensional, but the
shear turned out to be a *gauge* transformation, so the mechanism is vacuous
rather than merely blind.

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
*The residue is entry **U1** below — **ALREADY-PURSUED since 2026-08-06**
(2026-09-03 sweep): its criterion is §(K-out), its retarget §(K-ann), and what
is left of it is **(OW)** and **(ANH-R1)**, not a fresh dispatch.*

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

*Kill condition (added 2026-09-03): a `Gr(3,6)` cluster structure whose index
set grows with the graph and whose mutations preserve the Klein form `B`. Row:
gap-map **(K-Δ)** — unmoved since; this refutation stands.*

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

*Kill condition (added 2026-09-03): a curve placement compatible with the pin
at a hub, or a positivity certificate at `k = 4`. Deciding surfaces: §(K-pitch)
*Step 5* (the `k = 3` bracket monomial, which is why `k = 3` closes) and §(K-Λ)
(Λ1) (the `k = 4` factors, linear in the far covector). Neither has moved; this
refutation stands.*

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

*Kill condition (added 2026-09-03): a count running the other way, i.e.
`codim D > codim(pencil)` — impossible, `codim D = 1` is the minimum. Cross-check
2026-08-26: the same wall was reached independently from the codimension side by
**(ZH-3)** and from the scheme side by **(ZH-4)**, both recorded **circular as
posed** (§(K-shear) *Secondary deliverable*; §(K-jac) *Steps JC1–JC5*) — so
"degree/multiplicity" is not a cheaper door into `Image(φ_G)`. Deciding surface:
§2.4 and §(K-ind) *I0*; neither route opened a gap-map row.*

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

*2026-08-06 (recorded by the 2026-09-03 sweep): the bounded-dimensional
intermediary this refutation calls for is now **identified**, not merely
posited — §(K-ann) **(ANH-1)**, `Λ` is the self-stress space of the contracted
framework `H/P`, of dimension exactly `k−3` forced by a count. The pointer
still lands on U1, which is ALREADY-PURSUED. Row: gap-map **(K-ann)**.*

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

*Kill condition (added 2026-09-03): a Lean check of whether `hK`'s `∀` over the
split data can be weakened to `∃`. Deciding surface: `Escape.lean:334`/`:555` —
**no gap-map row**, and the standing 2026-08-05 Lean hold blocks the check, so
this item cannot move until the hold lifts. Its premise was **strengthened**
2026-08-06: §(K-ind) *Verification* records the coordinator-confirmed
correction that the pencil side runs `Graph.pencil_reduction`, not KT Thm 4.9,
and that "`hK` enters **only** through `pencilPair_of_splitOff_of_habitat`
(`Escape.lean:334`), i.e. only in the split arm". The `k = 6`-at-every-split
half stands (§(K-dom) *D4*).*

#### The ranked live shortlist

Three entries, labelled **U** (uniformity) rather than continuing the `C`
sequence — the workbook already owns `(C6)`/`(C7)` and the collision would be
real. They are **one object seen three ways** — U1 the target, U2 the machine,
U3 the logical form — and the ranking is by expected value toward *uniformity*,
not by how much is already known. **That interlock is why the shortlist's
collapse matters: with U2 struck and U3 retired (both 2026-09-03), U1 does not
inherit one third of the weight but all of it.**

> **U1 — ALREADY-PURSUED SINCE 2026-08-06; NOT A DISPATCHABLE ENTRY**
> (liveness sweep, 2026-09-03). Both halves were taken up **the day after this
> was written**: the criterion **(OUT)** became **§(K-out)** (51 steps, 8
> directions, to 2026-09-02) and the retarget became **§(K-ann)** (17 steps, 3
> waves). *Kill condition:* a class shape at which `λ` is constant on the far
> chart — **settled negative** ((ANH-1) + (D2)); or no single move works
> class-wide — **settled positive**, (ANH-2)/(ANH-3) deliver a class-uniform
> move *and* formula. *Row: gap-map **(K-ann)** — "U1 is **half** delivered,
> the move and the formula but not the inputs" — and **(K-out)**.* **What is
> left is not U1**: it is **(OW)** (§(K-out) *Steps O47–O51*, direction OWALL)
> and **(ANH-R1)** (§(K-ann) *Step A8*, relocation #4). The text below is
> preserved as the 2026-08-05 pitch.

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
class member**. Two cheap probes ranked ahead of prose, both new driver modes:
report `λ₁, λ₄` (equivalently `C₁, C₄ ∈ V_bc`) over the existing
length-4-companion frames, and compute `deficiency(H/{e₂,e₃,e₄})` over the
enumerated length-4-companion class shapes, mapping where (OUT) is even
generically available. **BOTH ARE DONE (2026-08-06, `outerline.py`; canonical
home workbook §(K-out), not restated here), and the answer is not the one this
paragraph expected:** the availability map is *uniform* but **ambient**-generic
((OC-2)), and on the pencil chart the bad locus is **nonempty at every class
shape** ((OC-3)) — so (OUT)'s hypothesis is *available* pointwise (356/357,
270/270) yet **never deliverable by a count**. The move-and-formula deliverable
itself was **delivered in full** by §(K-ann) **(ANH-2)/(ANH-3)** —
class-uniform, no genericity hypothesis, local at the moved vertex, one Klein
pairing at the named move, verified at 276 far-chart directions × 828 motions
against an independent implicit differentiation. What is *not* delivered is the
pair `(τ, ω)` it pairs against, which is **(ANH-R1)**. **This experiment is
DEAD as a recommendation; do not re-run it.**

*What would kill it.* A class shape at which `λ` is constant on the far chart —
a genuine surprise against (D2)'s attainment, and a sharp new obstruction. Or a
proof that no single move works class-wide, which would make U1 a fourth
relocation. **Honesty flag:** if the move can only be exhibited per shape, this
is another per-shape positive and must be recorded as one.

*What would kill it — **SPENT**, 2026-09-03.* Neither kill fired and both are
now settled: `λ` is never constant on the far chart at `k ≥ 4` ((ANH-1) makes
the annihilator a `(k−3)`-dimensional stress space, (D2)'s `3(k−3)` attained),
and a single class-wide move **does** exist ((ANH-3)). The honesty flag fired
in a third direction nobody listed: the **move** is class-uniform and the
**inputs** are per-shape, so U1's outcome is **relocation #4** — §(K-ann)
*Step A8*, and gap-map (K-wit) u12 records that *"whether it is easier than its
parent or merely smaller is OPEN"*. *Scope:* the `k = 4`
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
that verdict, which is why this pass did not run it. *(2026-09-03: a `k`-census
of this kind is now largely a **by-product** — §(K-out)'s 174 classes and 4296
length-4-companion triples, §(K-ann) (ANH-7)'s 3820/4296 — and the verdict is
unchanged, as predicted. §(K-ann) (ANH-4)/(ANH-8) confirm the calibration
independently: (ANH-4) is provably `k = 4` only, from the same `5k+10 ≤ 6k+6`
equality case, and gap-map (K-ann) u8 states "no `k`-graded mechanism including
this one can close the class — the verdict `Pencil-strategy.md` §4.6 already
carries".)*

> **U2 — STRUCK 2026-09-03 (liveness sweep): DEAD, and it was dead the day
> after it was written. Its own kill clause (i) fired.** The support condition
> `supp(λ) ⊆ {e₂,e₃}` — i.e. `λ₁ = λ₄ = 0` — is **satisfiable at every
> certified class habitat**, constructed exactly and legally by §(K-out)
> **(OC-4)** (*Step O6*, `outerline.py --build`, 2026-08-06): sliding `pt(x₁)`
> and `pt(x₃)` onto their two marked directions simultaneously gives an exact
> chart point with `λ₁ = λ₄ = 0` — **(OUT) SILENT** — still at target rank,
> `dim R_a = 1`, all four `IsNondegPencilRealization` conjuncts holding, and at
> 3 of the 4 habitats with **no** coincident hinge line. And the class-wide
> target is impossible in principle: **(OC-3)** proves `dim(R₁ ∩ L_b) ≥ 1`
> **structurally**, so §(K-out) *Step O3*'s own conclusion applies — *"a
> class-uniform proof of (OUT)'s hypothesis cannot be a count, **a matroid
> statement**, or any argument that does not see the placement"* — and U2's
> target **is** a matroid statement. **Its predicted near-counterexample is not
> one:** at (OC-4)'s point the escape still holds (`λ ∦ p⁺`, `λ ∦ q`,
> `deg_t Q(z(t)) = 4`); what the point actually shows is that (OUT) is strictly
> weaker than (Λ2). *Rows: gap-map **(K-out)** u2–u6, **(K-wit)** u7–u9.*
>
> **What survives, and it is in service.** U2's *premise* is **confirmed and
> landed** — §(K-ann) *Step A1*(ii): *"U2's ground set survives contact …
> `E(H)` really is the index set, and the matroid really has exchange (it is
> linear)"*, with generic rank `r(A) = |A| − dof(H/(E∖A))` combinatorial by
> Tay — and the hinge-rate identity is §(K-out) **(OC-1)** (*Step O1*, "the
> hinge-rate reading, made exact"). **One correction:** *"What U2 named is the
> **cocircuit** `supp(λ)`; the recipe turns on the **circuit** `supp(τ)`"*
> (§(K-ann) *Step A1*(ii); gap-map (K-ann) u7). Kill clause **(ii) never fired
> and is superseded**: the matroid is the generic Tay matroid, and (ANH-4)
> makes `E(H/P)` a **circuit** of it at `k = 4`, not the 6-fold graphic union.
>
> **Cross-surface reconciliation, 2026-09-03.** The dispute was three-way and
> is settled: §8.2's "live, rank 2" row is **struck with cause (OC-4) + (OC-3)**;
> §8.6's *delivered* verdict is **kept**, with its cause repaired off
> **(GR-16)**, which is a different object (an exact `3c × 3c` system on `G°`,
> gap-map (K-grid) u8). The pitch below is preserved as written.

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

> **U3 — STRUCK 2026-09-03 (direction OBAR): its named first step was DONE and
> its one residue's GATE IS NEGATIVE.** *Kill condition:* chart-wide stresses
> have no more structure than pointwise ones — **it FIRES, and by a cheaper
> mechanism than this clause names** (§(K-out) (OC-58)): the residue's object is
> a **one-row** extension of `R(H)` whose stress-support question is *pointwise*
> equivalent to (T3), so there is no chart-wide/pointwise gap to compare in the
> first place. The clause's original ground — *"(OC-35) is a structure
> theorem"* — stands and is not what killed it. §(K-out) **(OC-35)** is a structure theorem (the self-stress
> space of **any** min-degree-≥2 subgraph at **any** pencil placement is a
> Kirchhoff flow on its topological paths, valued in the chain-span perps),
> **(OC-36)** a three-term ledger, **(OC-37)** a class-shape floor
> `slack(F) ≥ 0` with equality **iff** `F` is a cycle or bouquet (2614 shapes,
> 215 906 supports, zero violations). So the support-enumeration this entry
> asked for landed in a **more general** form than requested — direction SIGZ,
> *Steps O31–O36* — and was extended by OGEOM (*Steps O42–O46*); the weak-map
> framing it invokes landed as §(K-ann) **(ANH-9)**, and §(K-ann) **(ANH-11)**
> adds the constructive converse (the common-transversal mechanism producing a
> stress with prescribed support). *Row: gap-map **(K-out)** u13/u14/u26.*
>
> **The residue is RETIRED, and the flag that gated it is ANSWERED (direction
> OBAR, 2026-09-03, §(K-out) *Steps O52–O57*).** SIGZ and OGEOM spent the ledger
> on `σ = corank R(H)` — **`H` alone**, the *necessary* half of input (a)
> ((OC-23)/(OC-24)) — **never** on `F = H ∪ {bar along M}`, U3's own object.
> The flag this entry carried — *"whether the arc admits `M` as a hinge of `H`
> in that construction is UNVERIFIED"* — is now **answered NEGATIVE three
> independent ways** ((OC-56)): `bc ∉ E(G)`, so the object is no subgraph of
> `G`; a **bar is one row** where (OC-36)'s ledger counts five; and a *hinge*
> along `M` would need **both** halves of (Λ0d) to fail, which §(K-σ) **(σ7)**
> rules out — on (σ7)'s own basis, conjunct 4's argument plus 39/39 witnesses,
> so chart-wide only as far as (σ7) is. And the ledger had **nothing to
> compute**: a `b`–`c` attachment adds no topological path, its whole increment
> being `dim(A ∩ V_bc^{⊥_E})` ((OC-57)), so the bar is in a support **iff**
> `V_bc ⊥_B C(M)` — **(T3) verbatim** ((OC-58)). Read as a *hinge* instead, the
> statement U3 wanted is **FALSE** at every chart point ((OC-59)). *"Unrun"*
> was a true observation about what was run and a false inference about what
> was left undone. (§8's U3 entry carried the same flag and moves in the same
> commit; the two agree.) The option-B adjacency this entry flags was
> checked and separated at §(K-ann) (gap-map (K-ann) u7: *"option B and U2 are
> **not** the same object"*); the 2026-07-30 NO-GO on option B stands.

**U3 (~~rank 3~~ — STRUCK 2026-09-03, direction OBAR) — restate `hK` as a
non-existence, so §2.3's asymmetry works for it instead of against it. Kept as
the dated record; the entry's own diagnosis below is what turned out false.**

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
than pointwise) stress. **RUN 2026-09-03 (OBAR), and the enumeration is
one line long:** the support in question is a **single coordinate**, the bar's,
and its vanishing is (K-wit) — §(K-out) (OC-57)/(OC-58).

*What would kill it.* If chart-wide stresses turn out to have no more structure
than pointwise ones, U3 is only a change of wording. **IT IS: STRUCK 2026-09-03
(direction OBAR, §(K-out) *Steps O52–O57*), and the kill needed no
chart-wide-versus-pointwise comparison at all.** By rank–nullity the bar's
support question is *pointwise* equivalent to (T3) at **every** chart point
((OC-58)), so this paragraph's *"Why §2's diagnosis does not already refute
it"* is the clause that fails: the non-existence U3 states **is**
`V_bc ⊄ C(M)^{⊥_B}`, a rank **lower** bound, so §2.3's asymmetry was never
evaded — the negative form is grammar, not logical form. The object is
moreover not an admissible (OC-35) subgraph at all ((OC-56)), and read as a
*hinge* the statement is outright **FALSE** ((OC-59)). It is also **adjacent to
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

**The named lead is no longer un-pointed (2026-08-06; recorded 2026-09-03).**
§(K-ann) *Step A10* **(ANH-9)** supplies the precise statement this paragraph
said it could not: (i) every `M_pen(p)` is a weak-map image of `M_gen`;
(ii) `M_pen^gen` is well-defined on the irreducible chart and is the
weak-map-maximal one; (iii) (ANH-R1) is decidable per triple by **one exact
rank computation at one rational point**. The workbook says so in as many
words — *"the weak-map / specialization-stability lead of `Pencil-strategy.md`
§4.6 now has its precise statement … which is what that subsection said it
could not supply."* So the fourth subject is an **internal** object with a
landed formulation, not a literature target, which **strengthens** *"not
recommended"* rather than weakening it. *Kill condition: a fourth subject with
a graph-growing index set and a verified theorem pointer. Row: gap-map
**(K-Δ)** and **(K-ann)**.* Note the bar here is **mathematical** — the
(M3) argument plus (ANH-9) — not a priority call, so the 2026-09-03
re-openability ruling does not loosen it.

### 4.7 C3's gate PRICED — probe C3-AVOID (specced 2026-08-20, LANDED 2026-08-24)

**Status: the gate is DECIDED, with a sharp threshold and a clean parameter.**
This subsection is the canonical home for the mathematics; `notes/Pencil-fanout.md`
§"Probe C3-AVOID" carries the dispatch record only, and the C3 entry above is a
pointer. Labels **(AV-1)–(AV-8)**, ***Steps AV1–AV6***; driver
`notes/scripts/w4/avoidgen.py`. **Purely combinatorial** — no rank is computed,
no realization placed, `hK` / `hbareSplit` untouched, no Lean edited. The
reserved workbook section **§(K-avoid) was NOT opened**: this is strategy about
the *generation theorem*, not kernel-(K) mathematics, so it has no gap-map row.

**The question, verbatim from the spec.** C3 pins only a subset `S ⊆ V` of
bodies to pencils. *If at each reduction step the split vertex can be chosen
outside `S`, KT's full freedom is intact there and the geometric crux never
arises.* So: **can the reduction always avoid a prescribed `S`, and up to what
`|S|`?**

#### *Step AV1* — the reduction, restated from the landed Lean (not from prose)

`Graph.minimal_kdof_reduction` (KT Thm 4.9, Phase 20,
`Molecular/Induction/ForestSurgery/Reduction.lean`) dispatches a minimal
`0`-dof-graph `G` with `2 ≤ |V|` three ways, at `D = bodyBarDim n ≥ 3`:

* `|V| = 2` — **BASE**, the two-vertex double edge;
* `|V| ≥ 3` with a proper rigid subgraph — **CASE I**, `hcontract`; the landed
  docstring records that Case I *"genuinely consumes the IH at two objects, the
  block and the contraction"*, i.e. the consumer recurses on `H` **and** on
  `G/H`;
* `|V| ≥ 3` with none — **CASE II**, `hsplit` at a vertex of degree exactly `2`
  (`exists_degree_eq_two`, KT Lemma 4.6).

Two facts read off the **definition bodies**, not the docstrings.
`splitOff v a b e₀` has `vertexSet = V(G) \ {v}` and edge relation *"every edge
of `G` missing `v`, plus one fresh `e₀` joining `a` and `b`"*
(`Molecular/Induction/Operations.lean:770`) — so a split removes **exactly one
vertex and exactly one edge**, and **every degree except `v`'s is preserved**.
`IsProperRigidSubgraph H G n := H ≤ G ∧ H.IsKDof n 0 ∧ 2 ≤ |V(H)| ∧ V(H) ⊂ V(G)`
(`Molecular/Deficiency.lean:483`) — so the Case-I test is *"some `W` with
`2 ≤ |W| < |V|` and `def(G[W]) = 0`"*, `H` induced without loss (extra induced
edges only lower the deficiency).

#### *Step AV2* — **(AV-1)** the supply lemma: the LOCAL gate is never the obstruction

**(AV-1).** At every Case-II node, writing `t = #{v : deg v = 2}`,
`t ≥ ⌈((D−3)|V| + 4)/(D−1)⌉`; at the molecular `D = 6` that is
**`t ≥ ⌈(3|V|+4)/5⌉ > |V|/2`**.

*Proof.* `no_rigid_edge_count` (KT 4.5(i), landed, and it is exactly the
no-proper-rigid-subgraph branch) gives `(D−1)|E| < D(|V|−1) − k + (D−1)`, so at
`k = 0`, `(D−1)|E| ≤ D|V| − 2`. `twoEdgeConnected_of_isKDof_zero` plus
`two_le_degree_of_twoEdgeConnected` put every degree at `≥ 2`, so the handshake
gives `2|E| = Σ deg ≥ 2t + 3(|V| − t)`, i.e. `t ≥ 3|V| − 2|E|`. Substitute. ∎

So **more than half** the vertices of a Case-II node are legal split choices,
and a step can dodge any `S` with `|S| < t`. Verified `0` violations over the
**140** Case-II nodes of the `μ ≤ 3` census (`--supply`), tight at 6 of them
(`|V| = 2, 3, 4` and the three `|V| = 14` shapes). **The gate does not fail
locally** — which is why the risk C3 names itself needed a different answer than
"the reduction may run out of choices".

#### *Step AV3* — **(AV-2)** the conservation law, and **(AV-4)** the capacity ceiling

Every reduction *tree* ends at 2-vertex leaves. Track the vertex budget:

**(AV-2) CONSERVATION LAW.** For every reduction tree of `G` (any strategy
consistent with the dispatch),

    #leaves = μ(G) := |E(G)| − |V(G)| + 1,   #contractions = μ − 1,
    #splits = |V| − μ − 1.

*Proof.* `μ` is invariant under a Case-II split (one vertex and one edge go).
`μ` is **additive** at a Case-I node: `|V(G/H)| = |V| − |V(H)| + 1` and
`|E(G/H)| = |E| − |E(H)|` (`H` induced), so `μ(H) + μ(G/H) = μ(G)`. The base has
`μ = 1`. Induct. ∎

**(AV-4) CAPACITY CEILING.** An original vertex avoids being a split vertex iff
it survives at some leaf, and a leaf holds 2 vertices, so

    capacity(G) := max{ |S| : some reduction of G avoids S } ≤ 2 μ(G).

The **parameter** of the whole question is therefore the **cyclomatic number
`μ = |E| − |V| + 1`** — equivalently, by (AV-2), the number of rigid blocks the
reduction's laminar Case-I family cuts `G` into. Verified: `0` violations of
both statements over the named pool **and** exhaustively over all **476** simple
2-edge-connected minimal `0`-dof graphs on `|V| ≤ 6`, with **451** of the 476
attaining `capacity = 2μ` (`--betti`). Equality is *not* universal — the
`|V| = 6`, `|E| = 8`, `μ = 3` graphs top out at capacity `4 < 6`, and one
`|V| = 5`, `μ = 2` class at `3 < 4`.

#### *Step AV4* — **(AV-3)** the threshold: GO at `|S| ≤ 2`, NO-GO from `|S| = 3`

**(AV-3) THRESHOLD THEOREM.** For `D ≥ 4` (so for the molecular `n = 3`):

* **GO, `|S| ≤ 2`, unconditionally.** For every minimal `0`-dof-graph `G` and
  every `S` with `|S| ≤ 2`, a reduction avoiding `S` exists. *Proof.* The
  invariant `|S ∩ V(node)| ≤ 2` is preserved (Case I sends `S ∩ V(H)` to the
  block and `S \ V(H)` to the contraction; the merge vertex is never in `S`). At
  a Case-II node with `|V| ≥ 3`, (AV-1) gives `t ≥ 3`, so some degree-2 vertex
  lies outside `S`. Leaves need no choice. ∎
* **NO-GO from `|S| = 3`.** `C_3, C_4, C_5, C_6` are minimal `0`-dof-graphs with
  `μ = 1`, hence capacity `2`; **every** 3-element subset fails
  (`0/1`, `0/4`, `0/10`, `0/20` respectively, `--avoid`).

So the threshold the spec asked for is **exactly `|S| ≤ 2`**, and it is *the
weak end* of the spec's own calibration — nearer *"only `|S| = 1`"* than
*"any independent `S`"*.

#### **(AV-5)** — no structural hypothesis on `S` lifts it, and what *does*

**(AV-5).** The obstruction is a **cardinality conservation law**, so
independence, spread, or any other property of `S` buys nothing: at `C_6` the
independent triples `{0,2,4}` and `{1,3,5}` are as unavoidable as `{0,1,2}`
(`--avoid`, explicit). What *does* lift the threshold is a hypothesis on the
**graph**: capacity is graded by `μ`, and above `|S| = 2` the surviving
statement is per-graph, not universal —

    a reduction avoiding S exists  ⟹  |S| ≤ 2 μ(G),
    and S must spread ≤ 2 per block of the laminar Case-I family.

Measured shape of the failure above the threshold: at the `μ = 2` members most
larger `S` still work but a positive fraction does not — `Θ(3,4,4)` avoids
`114/120` triples and `117/210` 4-sets; `Θ(3,3,4)` only `63/84` and `45/126`;
the `C_6` cactus `145/165` and `200/330`. All `|S| ≥ 5` fail at every `μ ≤ 2`
member, as (AV-4) forces.

#### *Step AV5* — **(AV-6)** where the ceiling is 2, exactly

**(AV-6).** A reduction that never contracts exists **iff `μ(G) = 1`**, i.e.
**iff `G` is a cycle**; and the `0`-dof cycles at `D = 6` are exactly
`C_2 … C_6` (`5L ≥ 6(L−1) ⟺ L ≤ 6`, driver-confirmed: `def(C_L) = 0` for
`L ≤ 6`, `1` at `L = 7`, `2` at `L = 8`). *Proof.* `μ` is split-invariant and
the base has `μ = 1`; conversely a `μ = 1` two-edge-connected graph is a cycle
and every cycle `C_L`, `L ≤ 6`, has no proper rigid subgraph, so its whole
reduction is Case II. ∎ So the `|S| = 3` counterexamples are **exactly the
cycles**, and for every *other* minimal `0`-dof-graph Case I must fire at least
once and the ceiling is already `≥ 4`.

**A guess this pass had to refute, recorded rather than smoothed over.** The
Case-II count of (AV-1) suggests `5|E| ≤ 6(|V|−1) + 4` in general, which would
cap `μ ≤ (|V|+3)/5` and give the quotable headline *"at most ~40 % of the bodies
can be pinned"*. **That is FALSE without the no-proper-rigid-subgraph
hypothesis:** exhaustively over `|V| ≤ 6` the count reaches `s = 10`
(`|V| = 6`, `|E| = 8`, `μ = 3`), and capacity reaches `4/5 = 80 %` of the bodies
at `|V| = 5`, `|E| = 6` (`--count`). So `μ` is **not** bounded by the Case-II
arithmetic, and the honest ceiling is the exact `2μ` of (AV-4) with no `|V|`-
relative headline attached.

#### *Step AV6* — **(AV-7)** the gate is NECESSARY, not sufficient

**(AV-7).** Passing the gate does **not** establish that *"the geometric crux
never arises"*. From `splitOff`'s definition body: re-inserting `v` deletes the
fresh edge `e₀ : a–b` and adds `eₐ : v–a`, `e_b : v–b`, so the **incidence sets
of both neighbours `a` and `b` change at every step**, `v`'s freedom
notwithstanding. Being a pencil is a condition on a body's *whole* hinge-line
set, so an `S`-body adjacent to a split vertex has its pencil condition
**re-imposed** at that step. Two further arms the gate says nothing about: the
two `S`-bodies that reach the base still need a pencil realization *there*, and
every capacity unit above 2 is bought by a **Case-I gluing**, whose
pencil-compatibility is exactly the geometry this probe is barred from. **(AV-7)
is combinatorial; its geometric consequence is OPEN and out of this probe's
scope** — flagged, not forced.

*Kill condition (added 2026-09-03): a proof — or refutation — that Case-I
gluing re-imposes the pencil condition on the glued body class-wide, together
with pencil realizability for the two `S`-bodies that reach the base.
**Deciding surface: none — this item has NO gap-map row** (see *Step AV1*:
§(K-avoid) was deliberately not opened), which is precisely why only a liveness
sweep can check it. The nearest surfaces are §(K-ind) *I6* (the contraction arm
has no chart morphism, so this arm has no transport) and the mixed-stratum
rigidity facts §(K-out) **(OC-18)** / §(K-ann) **(ANH-R1)**. This is the only
genuinely open item §4.7 leaves.*

#### **(AV-8)** the verdict for the option board

**(AV-8).** **C3's gate is priced, and the price is high.** As a *crux-avoidance*
route C3 is **NO-GO**: the universal statement stops at `|S| ≤ 2`, a threshold
that pins two bodies out of `|V|` and is nowhere near the *"real molecules have
some sp²-planar atoms"* motivation the option was promoted on. What survives,
and is worth carrying, is **(AV-4)'s parameter**: C3's gate passes exactly to
`2μ(G)`, so C3 is viable only on **Case-I-rich** graphs and only for `S` spread
`≤ 2` per rigid block — and on exactly those graphs (AV-7)'s Case-I arm is the
unpriced half. C3 therefore **stays on the board, re-scoped**: not as "relocate
the hard case", but as *"the hard case relocates into Case-I gluing, at a rate
`μ` measures"*. **Nothing here touches `hK`, `hbareSplit`, (GR-15) or class
uniformity, and no gap-map status moves.**

*Liveness clause, 2026-09-03.* C3-as-crux-avoidance is barred by a **proof**
((AV-3)'s threshold), not by a priority call, so the re-openability ruling does
not lift it; the **re-scoped** C3 is a live, unpriced option whose consumers now
exist and are worked — §(K-out) **(OC-18)** and §(K-ann) **(ANH-R1)**, both
pointwise available and neither class-uniform. *Kill condition for the
re-scoped form: (AV-7)'s Case-I arm settles either way. Deciding surface: §4.7
itself — no gap-map row — plus gap-map **(K-out)** and **(K-wit)** u10.*
Whether §8's board still carries the C3 row is §8's business, not this
subsection's.

**Caps, disclosed.** The Case-II census is exhaustive **only for `μ ≤ 3`**
(hence `|V| ≤ 16`); `μ ≥ 4` was not searched and an exhausted cap is not a
nonexistence claim. The `--betti` / `--count` exhaustive sweeps are **simple
2EC graphs on `|V| ≤ 6`**. The per-`S` avoidance sweep runs to `|V| ≤ 12`;
larger pool members report the DP capacity only. Everything at `D = 6`
(`n = 3`); (AV-1) and (AV-3) are stated and proved for general `D` and are the
only claims here that are.

*Kill condition (added 2026-09-03): a `μ ≥ 4` counterexample to (AV-2)/(AV-4),
or a `|V| ≥ 7` violation of the exhaustive `--betti`/`--count` sweeps.
Deciding surface: `notes/scripts/w4/avoidgen.py` — **no gap-map row**. An
exhausted cap is not a nonexistence claim, and these caps are the disclosure of
exactly that.*

**Verification.** `python3 notes/scripts/w4/avoidgen.py --all` (~36 s, seven
modes: `--supply --census --betti --forced --avoid --count --validate`),
byte-identical under `PYTHONHASHSEED` 0 and 12345. `--validate` cross-checks the
`(6,6)` pebble-game deficiency against `kbare_common.exact_deficiency`
(0 mismatches) and the branch enumeration of rigid vertex sets against the
brute-force subset sweep (0 mismatches). Per-mode rows in
`notes/scripts/README.md` §3.

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

**A sharper failure mode than "not yet uniform"** (GUNIF, §(K-grid) *Steps
G34–G35*): a sweep can be exhaustive over a stratum that structurally
**cannot exhibit the failure** — indistinguishable from uniformity until
proven; CFLANK's *Step G28* item (iv) had already flagged the tell in
advance (`n_hub ≥ 8` unreachable), exactly where (GR-28)(iv) fails.

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
  factors, and `g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere in the Python
  harness **at the time**. It is generic, so no sampled frame ever saw it fail —
  the exact failure mode sampling cannot detect. **CLOSED the same day, and this
  clause is now a settled record, not a job:** §(K-Λ) *Step 3a* (2026-08-05)
  located it geometrically as **(Λ0g)** — `g₁₄ = 0 ⟺ C₁ ∩ M = C₄ ∩ M` as points
  of `M`, one equation on the line `pt(a)` slides along — and it is asserted per
  frame in `outer.py` (`--geom`/`--habitat`/`--sweep`) and at the chart point in
  `ltwo.py`. *Kill condition: none — settled. Deciding surface: §(K-Λ) Step 3a.*
- **It also marks the method's boundary, and confirms §2.3.** The upgrade works
  because (Λ0) is a statement about the **local frame alone**, where the far
  graph does not appear. (K-wit) — the escape's uniformity — quantifies over the
  far covector `λ`, which the frame deliberately leaves free, so it is not a
  statement on this variety and no generic-point computation on the frame
  reaches it. The symbolic route can make every *far-graph-free hypothesis
  package* uniform and stops exactly where the far graph enters.

**Others, in rough order of value.** ~~(i) Is the pullback of the bad
hypersurface's equation identically zero on the image of the `V_bc` map? — an
elimination question, and the exact form of §2.4's open problem.~~ — **STRUCK
2026-09-03 (direction GELIM, killed before computing; the disposition needed no
driver). It was already dead when this list was written**, by (D4), which landed
the same day. The disposition, by companion length:
**at `k ≥ 4`** — the class stratum, by (D3)'s `hnoRigid ⟹ k ≥ 4` — it is **not
frame-expressible** (the far block contributes `3(k−3) > 0`) **and has no
content**: §(K-dom) (D4)'s dominance already gives `φ_G^*(f_B) ≢ 0` per shape,
since a dense image cannot sit inside a hypersurface. The open thing there is
**uniformity**, which is not elimination-shaped.
**At `k = 3`** it *is* frame-expressible — the far block is **0** ((D2): `V_bc`
constant along the entire far chart, 13/13 and 41/41; §(K-pitch) *Step 5b*: no
far data at all), so the `λ` quantifier that bounds this method does not exist
there, and the computation is ~14 indeterminates at degree 12, inside (ANH-16)'s
brackets — it would run. But `k = 3` is **exactly (K-res)**, outside the pinned
class and barred from direction specs; and the containment it would test is
**already refuted pointwise** at both probed `k = 3` habitats ((D4): the escape
holds at all 21 seeds, `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0`, the six `k = 3` seeds
included). So the item is nontrivial **exactly on the stratum it may not serve**,
and vacuous on the one it was proposed for. ~~(ii) Verify
(Λ1)'s 16-entry bracket identity symbolically rather than per-frame.~~ —
**DONE 2026-08-05**, and it was the layer's deliberate first consumer precisely
because its answer was already known, so a mis-configured M2 layer would show
up immediately (`M2 --script notes/scripts/m2/lambda1.m2`; mathematics in
`notes/Pencil-informal.md` §(K-Λ) *Step 2*). It verified, and it came with two
things the per-frame battery could not give: (Λ1) needs **none** of (Λ0) and
none of the panel data, and `rank Φ_loc = 2` is now generic rather than
observed.

**(iii) (K-chord)/`R_3` for parameterized families — LIVE, now this list's only
unstruck item, and NOT dispatchable until a question is named.** `(K-chord)` is
open, and its residue **widened** since this line was written: since §(K-mech)
(direction M, 2026-08-06) the slide device's necessary-condition set is **three**
decoration-free items — (K-chord) itself, both pole-cluster bounds `≤ 1`
((MX-4)/(MX-5)), and no forced flex route ((MX-6)) — measured complete and sound
at 21/21 on the sampled `|V°| ≤ 6` strata ((MX-9)); the live residue is the
**sufficiency** of that set beyond those strata. Two standing objections a spec
must clear first, neither of which was recorded here before 2026-09-03: `R_3` is
a matroid with **no combinatorial characterisation** (generic 3-dimensional
rigidity), so a class argument has nothing to reduce to (the `(K-chord)` row's
own words); and the M2 layer's reach is bracketed from both sides by
**(ANH-16)** — degree 12 in 24 indeterminates finishes at 578 s, the θ core at
the generic point does **not** finish at 600 s — with the layer **cold since
2026-08-07**. *Kill condition: a named question here run, or (K-chord) closed —
decided by the `(K-chord)` gap-map row (`python3 notes/gapmap.py --row
'(K-chord)'`).*

**Standing rule for this list, added 2026-09-03 after direction GELIM was
dispatched on a dead entry:** no item here is dispatchable without (a) an
**(ANH-16) price** and (b) a check of its **owning gap-map row**. Neither
objection that killed GELIM was in this section; both were one row away.

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
is viable only on the **local frame** — 6 points, two panels, a meet line. That
is where the layer's two delivered results live ((Λ0) and (Λ1), §(K-Λ)), and it
is the boundary the gauge-slice datum above measures. ~~which is precisely where
§5.3's first item lives~~ — **struck 2026-09-03 with item (i) itself: that item's
disposition says it is *not* frame-expressible on the class stratum (`k ≥ 4`), so
it was never an instance of this principle.**

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
  **not** implied — 45 constructed hard-stratum, primally-nondegenerate
  counterexamples (53 until the 2026-08-06 harness re-baseline shrank the
  pinned pool from 63 to 47; §(K-σ) *Step σ4*'s blockquote) — but two of the four are free **at `ℝ`**, one is the
  already-named (Λ0d), and the steering is exhibited exactly. What is left **of
  obligation 1** is **Lean**, held by the standing Lean-hold adjudication —
  **but obligation 1 is one of four, and the other three are not Lean and not
  blocked** (scope, the unwitnessed (σ6) failure direction, and the
  never-observed-nonempty branch). Corrected 2026-08-20; see §8.4, and
  `notes/Phase39.md` *Hand-off*'s route-σ blockquote for the split.
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

**Four classical references entered use 2026-08-26 (direction ZJACOB), and their
canonical home is `notes/Pencil-informal.md` §(K-jac)'s own reference block, not
this section** — Eagon–Northcott 1962, Bruns 1981, Eisenbud–Huneke–Ulrich 2004
and Hochster–Eagon 1971, on heights of ideals of minors and generic perfection of
determinantal loci. All four were verified against primary/publisher metadata at
that landing and **no section pointer is asserted for any of them** (the
CLAUDE.md bar: cite "classical" rather than guess a §). They are cited there for
a **negative** use — every one of them bounds the height of an ideal of minors
from *above* and takes the generic rank as an *input*, which is why the
determinantal package cannot supply properness.

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

## 8. The option board (2026-08-20) — every live route, priced

**Why this section exists.** After the eighth fan-out closed, a session's worth
of conversation re-derived the option space from scratch because it was spread
across §4 (candidate invariants), §4.6 (refutations + `U1`–`U3`), the phase
note's carried items, and two workbooks. This section is the **single board** a
fresh session reads to choose a direction. It adds no mathematics: every entry
points at the section that owns it. **Status words here are pointers**; the
owning section and `notes/Pencil-informal.md`'s *State of (K)* map remain
authoritative.

**Not on this board: §9's Zheng shelf** (a project-new external source read
2026-08-21; the source is unrefereed and is an **idea source, never a
citation**). **Corrected 2026-09-03 — this paragraph had gone stale against §8's
own closing paragraph, which records the owed filter checks as DISCHARGED:** of
the six candidates (ZH-1)–(ZH-6), **(ZH-1) and (ZH-4) are struck, (ZH-3) is
struck-by-absorption, (ZH-5) is a design note and (ZH-6) is write-up material**
(§9.3, updated twice on 2026-08-26 by directions ZSHEAR and ZJACOB), and the owed
§2.5 filter checks are **DONE**. What survives is **(ZH-2) in its stratified
reading only**, priced as row 8 of the corrected table below. The shelf stays off
this board. *Kill condition for the shelf as a whole: (ZH-2)-stratified run or
struck — decided by §9.3.*

**Read the two filters first — most candidates die on one of them.**

- **The growing-ground-set test** (§4.6): any proposed structure is a MISS
  unless its index set is `E(G)` or derived from it. This retired both
  literature hunts and two of §4.6's four seeds.
- **Counting saturation** (§2.5): **no** count-expressible invariant can help,
  which rules out `dim R_a ≥ 2` and its family. Reinforced from two directions
  since: §(K-out) **(OC-3)** (no counting, matroid or placement-blind argument
  can deliver (OUT)'s hypothesis) and, 2026-08-19, §(K-out) **(OC-37)** — the
  counting route to a **disproof** is dead too. Counting is closed in *both*
  directions — and a **third** arrival, 2026-09-02: on the `hK` lane's own
  residual, **(GR-141)** (direction GGLOB) kills the counting handle by
  saturation. *Neither filter has a kill condition: they are negatives. Their
  status is decided by the `(K-out)` and `(K-grid)` gap-map rows.*

**RE-RANKED 2026-09-03 — THE NINTH STRATEGY-ONLY PASS, AND THE RANKING A SESSION READS.
RANKS 1, 2 AND 3 ARE ALL SPENT** (BSCOND, ordinal 76; BARCH, 77 — whose recon **lifted this
pass's bar, narrowly**, the lift recorded in the bar paragraph below, not here; and GLEAF,
80, whose kill condition fired on **both** clauses at once); **the live head of this list is
RANK 4**, option B's design pass. **All three spent ranks were decided inside 24 hours of
being written, and rank 3's verdict says something about this board rather than about its
row:** the entry priced a candidate by *the machinery it reaches* and never asked whether
the statement reached is **necessary or sufficient** for the row it sits on — see rank 3.
Coordinator-authored at a session start, no dispatch spent, commissioned by
`notes/Phase39.md` *Hand-off*'s own next-concrete-task line after the liveness round found
**~52 of ~108 forward-looking entries defective**. Every entry below was re-derived from its
**owning** section or gap-map row in this pass and never quoted from a hand-off (the F22
discipline); both filters above were applied to each. **The two lists below this one are dated
records, not rankings** — the 2026-08-25 list (ranks 1 and 2 spent/refuted) and the 2026-09-02
corrected `hK` table, whose per-row *re-derived status* stays authoritative for the `hK` lane
and whose *ranking* this pass supersedes.

**The four binding criteria** (`notes/Phase39.md` *Current state*, the standing delegation):
(1) **max impact on proving or disproving `PencilPair K 3 G`**; (2) **falsification /
architecture-testing as a positive criterion**; (3) **diversification**; (4) the 2026-09-03
**reprioritize** directive — *"if the current approach seems to be getting in a rut then it's
time to reprioritize."*

**THE RUT MEASUREMENT, AND IT DECIDED RANK 1.** The (BE-14) thread is the arc's most
target-moving carried item — seed-free, induction-free, discharging `hbareSplit` **and**
`PencilPair`'s unconditional conjunct as a standalone theorem — and **S-mark is its only open
step**. S-mark has two halves, and the spend is almost all on one: **eleven consecutive
(BE-14)-thread landings, BONEONE (56) through BDEGTWO (74), worked half (B) or one of its
named siblings**, while half (β)'s two named window conditions **(S1)/(S2) have been open since
BWIN (51) and were attacked by none of them**. Meanwhile half (B)'s side-degree-`≥ 2` instance
has defeated **four structurally-different attempts at one obstruction**: (PENCIL-SATURATES)
**refuted** (BSATUR), its `-GEN` repair **refuted** (BSIGMA), `-CHART`'s `(∗)` route **dead
from `dim A = 5`** (BLINE), and both of (BE-134)'s gaps **settled** with the **METHOD** left as
the obstruction (BDEGTWO). That is `/coordinate-phase`'s **recurring-wall** shape exactly —
each fix varied the *upstream* construction and hit the *same* named obstruction — so the wall
is to be suspected in the shared downstream object, and the rule's remedy is a recon of **that
object** before authorizing another re-targeting. The rule fires at the third; here the next
build would be the fifth.

1. ~~**(S1)/(S2) — (BE-57)(iv)'s two window conditions.**~~ **SPENT 2026-09-03 —
   direction BSCOND (ordinal 76), `notes/Pencil-fanout.md` §"BSCOND". Its kill condition
   fired on BOTH:** the two conditions were **one gap** ((BE-143)), **(S1) is REMOVABLE**
   ((BE-148)), (S2)'s first half is **PROVED** with the forcing list exhaustive at two
   ((BE-145)), and its second half is **REFUTED as stated** — `p_{w₁} = p_{w₂}` does pin `λ`
   onto `W^{⊥K}`, at real window middles — then **CLOSED** by the coincidence excess law
   ((BE-146)/(BE-147)). (β) at the window is **UNCONDITIONAL**. **Two things this pass got
   wrong, recorded because the ranking rationale is a forward-looking surface (§8's own
   rule):** (a) *"a refutation costs the window's class theorem its carrier"* — it did not;
   the refutation and the proof turned out to be **the same object**, and the theorem came
   out **stronger**, with a hypothesis deleted; (b) the pass ranked this as *"the only thing
   between half (β) and a class theorem at the window"*, which was right, and priced it as
   **decisive both ways**, which was right for the wrong reason — the decisive information
   was in the *sampler's support*, not in the mathematics of either condition taken alone.
   **What the pass got right, and it is the transferable part:** *"vacuous at every drawn
   piece but NOT theorems"* is the exact profile of an assumption a thread leans on without
   testing, and naming the support before weighting any figure is what cracked it. *Kill
   condition FIRED. Decided by: the `(K-bare)` row's status cell, which now reads
   UNCONDITIONAL.*
2. ~~**Half (B) at side-degree `≥ 2` — the architecture question, AS A RECON.**~~ **SPENT
   2026-09-03 — direction BARCH (ordinal 77), `notes/Pencil-fanout.md` §"BARCH". Its kill
   condition FIRED on the first clause — the method class is settled, and settled the way
   this entry did not expect.** **The method class is NOT dead: it CHANGES AMBIENT.** `s`
   *and* `r` are both `p_x`-free on the fixed core, so their GRAPH `Γ ⊆ Λ²K⁴ ⊕ Λ²K⁴` is a
   FIXED subspace and `ρ̄_i ∩ Π_x = φ_p(Γ ∩ (Π_x ⊕ Π_x))` **exactly** (99/99, as subspaces)
   — so the clause IS a condition on the point `p_x` against a fixed subspace, and
   **(BE-139)(iv) is right inside `Λ²K⁴` and OVER-SCOPED as written** ((BE-149)). A
   **second** `p_x`-free subspace `R₀ = r(ker s) ⊆ R = ρ̄(core; c₁,c₂)` certifies GOOD at
   every `dim A ≤ 5` row ((BE-150)); `dim Γ_Π ≤ 1` PROVES GOOD and fires at **39 of the
   54** relaxation-blind fibres ((BE-151)). On the second question: **14 → 12 survives the
   clause's loss** — the per-side weakening is **dead** (313/164/74/24/0 escapes at
   `f = 2..6`, (BE-152)) but the **two-sided (E4)** leaves **0** of 6 400, is strictly
   weaker, and **holds at BSATUR's own witness**, because a per-side refutation cannot
   touch a statement about the pair ((BE-153)). **(E4) is UNPROVED.** **What this entry got
   wrong, recorded because a ranking rationale is a forward-looking surface (§8's own
   rule):** it priced the likeliest deliverable as *"another method-is-dead negative on a
   half already known blocked"*, and that was the half that was wrong — what is gone by
   construction is `A`'s **sufficiency**, not the **existence** of a `p_x`-free object.
   **What it got right, and it is the transferable part:** it forbade posing the question
   as *"is `A_sharp` proper"*. That reframing is what made the ambient visible; at the
   narrow question the dispatch would have been the fifth attempt. *Kill condition FIRED.
   Decided by: the `(K-bare)` row, whose status cell now reads the METHOD verdict as SCOPED
   TO `Λ²K⁴` with `Γ`-properness and (E4) as the successors.*

   ~~*(superseded framing, kept one line as the dated record)*~~ **Half (B) at side-degree
   `≥ 2` — the architecture question, AS A RECON, and see the bar below.** Owner: `(K-bare)` u39/u40, (BE-139)/(BE-140). The question is not *is `A_sharp`
   proper* but **whether any `p_x`-free-subspace method survives at `k ≥ 2`** — BDEGTWO's own
   mechanism says the pendant multiplier is *free* at `k = 1` and *determined* at `k ≥ 2`, so
   what made `A` `p_x`-free is gone by construction — and, if none does, **whether the 12-block
   residue is reachable without the clause at all** (`⟨M⟩` empty at 93 rows, the other 11
   **unwitnessed-not-excluded**, (BE-97)(iv)). Ranked below (S1)/(S2) because its likeliest
   deliverable is another method-is-dead negative on a half already known blocked, and above
   everything else because it sits on S-mark's critical path. *Kill condition: the method class
   settled either way, or a `p_x`-varying properness argument landed. Decided by: the
   `(K-bare)` row, u39–u40.*
3. ~~**(GR-144) successor 4 — leaf-covering on the branches.**~~ **SPENT 2026-09-03 —
   direction GLEAF (ordinal 80), `notes/Pencil-fanout.md` §"GLEAF". Its kill condition
   FIRED on BOTH clauses at once, in opposite directions:** the machinery **does** reach it
   — at a fixed leaf assignment the demand **is** an Edmonds matroid partition over six
   contracted graphic matroids `M(G°)/K_j` with criterion `Σ_j ν_j(F) ≤ σ(F)`, and the two
   remaining Lean bridges are mechanical ((GR-148)) — and what it reaches is a condition
   (GR-18)(iii)'s residual **implies**, vacuous inside (GR-140)'s own normal form, admitting
   455 400 of 472 680 legal pairs against the residual's 229 320 ((GR-146)). So a **proof
   there cannot move (GR-10)**, and only a refutation — *strictly stronger* than a g-flank —
   could. **What this pass got right, and what it got wrong:** the *reach* clause was right,
   and *"matroid union / Tutte–Nash-Williams, §2.1's ingredient 3, the one ingredient the
   pencil pin does not cost"* was the correct diagnosis of why; the *value* clause — calling
   it the lane's best-shaped live successor — was wrong, and wrong for a reason this board
   can act on: **it priced a candidate by the machinery it reaches and never asked whether
   the statement reached is NECESSARY or SUFFICIENT for the row it sits on.** A necessary
   condition of an open existence statement cannot be a step toward it. **Add that question
   to the two filters** for any future entry. Successors 2 and 3 are unchanged — engineering
   and a search, both disfavoured by the do-not-do's general form — and successor 1 stays
   **demoted**; the residue GLEAF names ((GR-152)(v)) is a *conjecture about its own
   criterion* with **no consequence for (GR-10) or (GR-15) either way**, so it does not
   inherit this rank. *Kill condition FIRED. Decided by: `(K-grid)` close-it u7, which now
   reads SPENT.*
4. **Option B for `hbareSplit` — the design-pass first step ONLY.** Owner: §8.4's row. The
   diversification pick with genuine target impact (criterion 3): the only identified path to
   `hbareSplit` other than (BE-14), **re-opened 2026-09-03** on the *declines are not locks*
   directive, with **both stated prerequisites DISCHARGED** (the KT pp. 684–691 re-pin landed
   2026-08-02; the boundary-load calculus transports at 192/192) and a **first step the Lean
   hold does not park**. Priced deliberately at *one design pass* — decision-relevant before
   any research-scale commitment, and the pass itself is what prices the rest. *Kill
   condition: commissioned and run, or (BE-14) closing `hbareSplit` without it. Decided by:
   the `(K-bare)/(K-bare-ext)` row.*

**Below the top four, in order, each keeping its own kill condition where the row above
states one:** **U1** (the annihilator retarget, §8.2 — now inherits the whole §4.6 shortlist's
weight, **U2 struck and U3 struck**, and its residual (ANH-9)(iii) *is* the same missing
technology as (GR-10)); ~~**U3's one residue**, the `H ∪ {bar along M}` ledger nobody ran~~ —
**RETIRED 2026-09-03 (direction OBAR): the admissibility check that gated it ran and came
back NEGATIVE**, and the ledger had nothing to compute (§(K-out) *Steps O52–O57*); **RPOOL's two successors** — the *repaired* (RS-5) uniformly (108 per-shape
confirmations, 72 exact-point proofs, 0 counterexamples) and **a route for the
`index < 2·g_forced` members, which have no named home** — both inside the (K-res) wave, which
stays a **user call** and is now dearer; **block 10's one-end-series** ((β)'s largest remaining
per-shape component, value raised at BDOUBLE) and **BTWOCUT's bundle construction** (skipped
at every direction since ordinal 44); **(OW)** (OWALL's reduction — buys a quantifier, not
a gap-map row); **collision dominance** `min_M B(M) ≤ d_adm` (not barred); **(GR-144)
successors 2 and 3**; **(AV-7)'s Case-I gluing arm** (unpriced and untouched); **OGEOM's
Kirchhoff-injectivity sentence** and the unsearched `n(F°) ≥ 6` frontier (disproof-risk
reduction, which (OC-24) says can never be the binding obstruction); **(ZH-2) stratified**;
**route σ obligations 2–4** (insurance, not repair — obligation 4's branch has never been
observed nonempty).

**THE NEW BAR THIS PASS PRODUCED, recorded here the way the do-not-do below is.** **Do not
dispatch `A_sharp` properness — or any further single-clause repair of
(PENCIL-SATURATES-CHART) at side-degree `≥ 2` — as a build before rank 2's recon runs.** It
would be the **fifth** attempt at the same named obstruction, and BDEGTWO's own verdict is that
what fails there is the **architecture, not the clause**. This bar is **methodological, not
mathematical**: unlike the do-not-do below, the underlying mathematics is not spent, so rank
2's recon can lift it — and a lift must be recorded **here**, with its reason, not inferred
from a row elsewhere. *Kill condition: rank 2's recon delivered.*

> **THE BAR IS LIFTED — NARROWLY, 2026-09-03, by rank 2's recon (BARCH, ordinal 77).**
> Recorded **here**, with its reason, exactly as the paragraph above requires; do not infer
> its scope from the `(K-bare)` row.
>
> - **STILL BARRED: `A_sharp` properness as posed**, and any repair that keeps a moving
>   subspace of `Λ²K⁴` as its downstream object. **The reason is now a theorem, not a
>   count**: (BE-149) shows `A` is the *only* `p_x`-free `s`-image in `Λ²K⁴`, so an argument
>   of that shape has nothing fixed to stand on. Priced as a candidate inside the method
>   question, as this bar asked: it is the **worst of the three**, because it is the one
>   that keeps the object four attempts have already eaten.
> - **LIFTED: `Γ`-properness.** Properness of `{p ∈ F : dim(Γ ∩ (Π_x(p) ⊕ Π_x(p))) ≥ 2}` —
>   one incidence lemma for a **fixed** subspace of `Λ²K⁴ ⊕ Λ²K⁴` against a 3-parameter
>   family of products of **totally singular** 2-spaces (`Π_x = Σ_{p_x} ∩ Λ²π_x`). Half of
>   (BE-115) lifts to it and the Klein-quadric half does not ((BE-149)(v)).
> - **LIFTED: (E4)** as the clause replacing (PENCIL-SATURATES-CHART) in (BE-101) — the
>   cheaper of the two, since the arithmetic is already exhaustive ((BE-152)/(BE-153)).
>
> **Both lifts name a NEW downstream object**, which is what the recurring-wall rule asks
> for; the bar's own condition is therefore met rather than waived. **And the cheapest
> decisive move is a falsification, not either proof**: a peel with `c_i(Π_x) = 2` and
> `e₁ + e₂ ≤ 3`, which on BSATUR's `ρ_i = 5` witness needs `ρ̄_j ⊆ Π_x` outright. If that
> configuration exists, **(E4) dies and this bar comes back down over the whole clause
> family** ((BE-154)(iii)/(iv)).

**SUPERSEDED AS A RANKING by the 2026-09-03 pass above (back-link added in that same
commit); kept as the dated record, and its per-entry content stays authoritative.**
**RE-RANKED 2026-08-25** (the eighth strategy-only pass, post-GFLIP/GCHEAP;
each candidate's stated inputs re-derived against its owning workbook step, not
quoted from a hand-off — the dispatch-log F22 discipline). Cheapest-decisive
first, the board's own convention; both filters applied (none of the three is
an invariant proposal, so neither filter bites):

> **RANKS 1 AND 2 ARE SPENT — RE-RANKED 2026-09-02 (coordinator, from a read-only
> `hK`-scoping recon; the corrected list is *below* this list, which is kept as the dated
> record).** Both entries were left live here after their owning sections had settled them,
> and **§8.1's table already struck rank 1** — so the two surfaces of this board have
> disagreed since 2026-08-26, with the *ranking* (which the preamble says is what a fresh
> session reads) the stale one. **Rank 1 is SPENT**: OQRANK (ordinal 32, 2026-08-25) ran
> it; input (a) holds at **all 174 certified classes** and *"zero rulings — the
> (K-tight)-event branch never fires"*, so **both** branches the entry calls decisive are
> settled, and `(K-out)`'s row records input (a) as *"OPEN as a class-uniform statement and
> **NOT an independent gap**"*. **Rank 2 is REFUTED**: (GR-104)(i) was killed by **(GR-122)**
> at §(K-grid) *Step G142* (direction GHWIT, ordinal 36) on **2026-08-26 — the day after it
> was ranked**, by an `n_hub = 20` all-(2,2) pair of gap 4. This board's closing paragraph
> *was* edited that same day (the ZSHEAR filter discharge), so the list was read and left
> stale on the very day its rank 2 died. **Rank 3 is not an `hK` item** — it is the (K-bare)
> seed-free shape, i.e. the (BE-14) thread, running since BATTAIN (39) and 20+ directions
> in. Net effect, and it is the likely reason `hK` went untouched for **ordinals 44–65, 22
> consecutive dispatches**: the one place a session looks for an `hK` candidate has pointed
> at two dead items and one that is not `hK`.

1. **The ℚ(i) eigen-block leg of §(K-out) *Step O29*** — **SPENT (OQRANK, 2026-08-25);
   entry kept as the dated record, see the box above** (`rank(Q|_D) = 3` →
   **(a₁)**). O29's own landing calls it *"the single cheapest open step this
   pass leaves"*; harness-unblocked since the adjudicated `Gauss` →
   `exactcore` move-down (*"Step O29's route may now use exact `ℚ(i)`
   directly"*). Decisive **both ways**: it either closes (a₁) — hence, with
   (OC-34)'s 174/174 certificates and (OC-31), **input (a)** — at every
   certified isomorphism class, or exhibits the arc's first
   `rank(Q|_D) ≤ 2` class point, a candidate **(K-tight) event** (routes A
   and B dead at that split — the most informative negative available). A
   HIT chains with CIRR's chart irreducibility into (OC-8), i.e. **(K-wit)**,
   the single live form of the pitch route, discharged per-class over the
   widest keyed population the arc has — and by a *mechanism*
   (⋆-eigen-block decoupling), §2.2's recipe sense, not a search.
2. **(GR-104)(i)** — **REFUTED by (GR-122), *Step G142*, GHWIT, 2026-08-26; entry kept as
   the dated record, see the box above** — the price form at `n ≥ 12` (§(K-grid) *Step G124*).
   Machinery landed (`w4/gcheap.py` + `gridbal_common`), the adversarial
   controls named (the `n = 12`, `2k = 2` stall pairs), and (GR-102) confines
   any refuting pair to `d_par(M) ≥ 2|δ| − b_M`. A HIT makes (b′) at the
   constant 2 `n`-free — the last constant gap on the GFLOW descent chain.
   Ranked below the O29 leg because it is a residual-of-a-residual inside the
   (a′)/(b′) ledger and does not touch a named `hK` gap.
3. **(K-bare) at the seed-free direct-attainment shape** — bypass the
   antecedent and attack `HasPencilRealization K 3 G` directly on the
   habitat (the KBARE-FALSIFY probe's own suggestion; **not option B**).
   **BOTH OF THIS ENTRY'S STATED REASONS FOR ITS RANK ARE NOW FALSE
   (corrected 2026-09-03); the item itself is LIVE.** It is the **(BE-14)
   thread**, run continuously since **BATTAIN** (*Steps BE9–BE13*) through
   **BDEGTWO** (*Steps BE135–BE140*) — 140+ steps — so *"39 directions on `hK`,
   zero on (K-bare)"* describes only the day this was written; and its first
   slice is **not** exploratory, because the thread now has named one-step
   residues. Current locus, from the gap-map row rather than from this board:
   (BE-14) is **OPEN**, its **only open step** is **S-mark, the 2-cut
   composition lemma**, half (B)'s residue **(PENCIL-SATURATES-CHART)** is a
   **THEOREM at every side-degree-`1` terminal** ((BE-122)–(BE-128)) so
   **14 → 12** stands generically, and at side-degree `≥ 2` the `(∗)` route is
   **DEAD** ((BE-130)) — the two successors BLINE named being **SETTLED** at
   BDEGTWO (the sweep PROVED ((BE-136)), the *keep `xc₂…xc_k`* reduction
   **MOOT** ((BE-137)), fibre-properness closed-form ((BE-138))), leaving the
   **METHOD** as the obstruction and properness for the `p_x`-varying
   `A_sharp` as the successor ((BE-139)). Of KBARE-FALSIFY's
   two shapes, the `∃`-seed + deformation-repair one meets §(K-tight)'s wall;
   this seed-free one is the running thread. *Kill condition: (BE-14) settled —
   decided by the `(K-bare)/(K-bare-ext)` row (`gapmap.py --row '(K-bare)'`,
   units u38–u39).*

Below the top three, unchanged in relative order:
~~the one-unit-defect redo of (GR-79)–(GR-82)~~ — **BARRED 2026-09-03 by the
DO-NOT-DO below. It IS an (a′)/(b′) ledger direction** (attack (c) of route-ledger
entry 1, *Step G103* hand-off item 1), so the bar reaches it by its own reason,
not merely by span. **The mathematics stays OPEN and this is not a closed-route
record** — `(K-grid)` close-it u26 still names it as attack (c)'s successor
(*"redo (GR-79)–(GR-82) with a one-unit defect budget"*, *"cheap,
self-contained, and the honest completion of attack (c)"*), and (GR-84) already
realizes both unbounded residual cases at `n_hub = 16`, so it is bookkeeping-grade
even unbarred. It is a live item this board declines to dispatch;
collision dominance (*Step G115* (GR-96)(iii) — non-vacuous at only the 180
Petersen witnesses, and no mechanism identified) — **NOT barred: GCOLL lives
inside *Steps G74–G148* but is not an (a′)/(b′) ledger direction, and the
DO-NOT-DO is by attack name, not by span (see below)**; *kill condition:
`min_M B(M) ≤ d_adm` proved or refuted — decided by `(K-grid)` close-it u16*;
(OC-19) input (c) ((GR-15)-flavoured, the oldest missing technology) — *kill
condition: `H/X` rigid class-uniformly — decided by the `(K-out)` row, u9, and
§(K-out) *Step O18**. §8.4's route-σ obligations 2–4 keep their standing notes, and of
§8.2 only **U1** now does — **C2 was STRUCK 2026-09-03 (direction DSAT), its own
satisfiability kill condition having fired**; **§8.2's U2 and U3 do not — both were re-settled 2026-09-03, and
BOTH ARE NOW STRUCK: U2 by (OC-4)+(OC-3), U3 by OBAR's negative gate (see §8.2). This sentence used to read
"C2/U1/U3", silently omitting U2; that omission turned out correct in outcome
and is now explicit.** **The one filter note this board owed on §9's shelf is
DISCHARGED (2026-08-26, direction ZSHEAR's secondary deliverable):** (ZH-2)
survives §2.5 only in its **stratified** reading (whole-chart `∆` is
count-expressible, so the filter bites exactly there), and (ZH-3) survives the
filter but is **circular as posed** — a sharper objection. As predicted, neither
moves anything onto this board, and the shelf stays off-board; §9.3's order was
updated **twice on 2026-08-26** — ZSHEAR struck **(ZH-1)**, and ZJACOB struck
**(ZH-4)** and absorbed **(ZH-3)** — leaving **(ZH-2)-stratified** as the shelf's
only dispatchable content (row 8 below). *(The second update was missing here
until 2026-09-03.)*

**SUPERSEDED AS A RANKING by the 2026-09-03 pass above (back-link added in that same
commit); its per-row *re-derived status* stays authoritative for the `hK` lane, and rank 3's
own successor list is where the 2026-09-03 pass found its rank 3.**
**THE CORRECTED `hK` RANKING (2026-09-02).** Re-derived from each item's *owning*
section rather than from this board (the F22 discipline), by a read-only scoping recon
commissioned because `hK` had gone 22 consecutive dispatches untouched while the board's
own top two were spent. **The two filters were applied to every entry.**

| # | item | owner | status, re-derived |
|---|---|---|---|
| ~~**1**~~ | ~~**(GR-18)(iii)**, the grouping problem~~ | §(K-grid) *Steps G149–G164* | **SPLIT IN TWO 2026-09-02 (GPACK)**: the packing-and-split half is an **unconditional theorem** ((GR-130)) off `def(G) = 0` alone, and the residual is a **hub list-colouring** ((GR-132)) at `Λ = ∅`. **SPENT at the `ℓ = 2`-rich shapes 2026-09-02 (GLIST)**: that residual is now a 9-valued hub CSP in `(α, γ)` with clause (a) **free** ((GR-134)) and an exact local criterion — a cubic pure hub fails **iff** its three `D_β` are a perfect matching of the six trees ((GR-135)) — but **82 % of the infeasible pairs are locally feasible at every hub** ((GR-136)), so the open half is not hub-local. **RE-LOCATED and made CSP-FREE 2026-09-02 (GGLOB)**: the packing quantifier is **eliminable** and the residual is an orientation-plus-two-colourings criterion on the length-2 subgraph which, on the `D = 0`, `Λ = ∅` stratum, **IS (GR-10)** ((GR-140)); both named handles are dead — counting by saturation ((GR-141)), matroid union by an exhibited exchange failure ((GR-142)) — and the obstruction has **three tiers**, all of the 82 % being propagation-visible and the genuinely global tier first realized at `n_hub = 6` ((GR-143)). The successors are (GR-144)'s; `Λ ≠ ∅` still needs a merging conjunct nobody has written |
| 2 | collapse-order bound `κ ≤ 4/5` + the `r = 4` certifying criterion | §(K-grid) *Step G22* ((GR-19)); TCOL (i)/(ii) | measured `κ ≤ 4` at **18/18** separators, unproven, untouched since 2026-08-07 — **re-checked 2026-09-03, unchanged**. *Kill condition: `κ ≤ 4` (or `≤ 5`) proved, or a census-pool `dim Z = 0` block with `κ ≥ 5` — decided by `(K-grid)` **close-it u6, targets (ii) and (iii)**. Item (iv) of that same list is already settled by (GR-130); (ii)/(iii) are the two that survive* |
| 3 | **(OC-44)(iii)** wall-avoiding certificate-colouring existence | §(K-out) *Steps O41, O47–O51* | **RE-SCOPED 2026-09-02 (OWALL), row was stale until 2026-09-03**: (OC-44)(iii) is **REDUCED to (OW)**, geometry-free, and *Step O41*'s own named route is **REFUTED BY LOGIC** ((OC-50)–(OC-55)) — the conjunct it attacked is implied by the one it did not. Still open at (OW); a HIT still buys a **quantifier**, not a gap-map row |
| 4 | the (a′)/(b′) ledger residuals | §(K-grid) *Steps G98–G148*; the route ledger, `Pencil-informal-grid.md` L8374 | **route-ledger entry 1** (uniform fully-good existence at `Λ = ∅`, `D = 0`); **entries 2–4 are (GR-4′), `Λ ≠ ∅`, `D > 0`** — recorded *unchanged/unswept* at every landing since 2026-08-13; **entry 5 is PROVEN** ((GR-54)). *(The row used to say "entry 1 of 4" and name none of the others, which is why it was uncheckable.)* Its one live successor moved 2026-08-26: the **(L)** reading — *is the ledger gap ever `≥ 3`?* ((GR-127); spectrum `{0,1,2}` at 4 935 shapes) — **not** (P) (FALSE, (GR-122)) or (m) (PROVEN, (GR-126)). **BARRED by the do-not-do note below.** *Kill condition: any of entries 1–4 moves status — decided by `(K-grid)` close-it u14–u26* |
| 5 | (OC-19) input (c) | §(K-out) *Step O18* | **the ZNEQ pool re-key is STRUCK — it was DONE 2026-08-19**, by **(OC-34)**, §(K-out) *Step O30*, direction OSCHU: the (a₂)/`s₀` re-keying landed (`907 → 75` classes covering 19 of 174, the other **155 certified DIRECTLY**), so the `s₀` half is free at **all 174 and *without* (GR-10)**. It was already done fourteen days before this "corrected" table listed it as cheap and unrun — recorded, not silently removed, because that is the exact defect this round exists to catch. What survives is a **different** job, *Step O30* hand-off item 2 — the **uncapped** re-keying that would turn 174 into a class statement — and it is **not** *"a combinatorial cross-pool job, no new mathematics"*. Input (c) stays open and is (GR-15)-flavoured. *Kill condition: input (c) class-uniform — decided by the `(K-out)` row, u9* |
| 6 | route σ obligations 2–4 | §8.4; §(K-σ) *Step σ5* | eligible (obligation 1 only is Lean-held), but the branch obligation 4 closes *"has never been observed nonempty"* — insurance, not progress. **Route σ faces exactly one crux** (`(K-σ)` close-it u2): the workbook's two kills of `M₁` (§(K-tight) *Step 1* and *Step 2.6*) rest on the **same** reason, the `hinge(vb) := q(ab)` pinning. *Kill condition: an obligation discharged, or the obligation-4 branch observed nonempty — decided by the `(K-σ)` row, status u8* |
| 7 | OGEOM's successors | §(K-out) *Steps O42–O46* | disproof-risk reduction, which **(OC-24)** says can never be the binding obstruction. The successor is **one shape-free sentence**: *at every live core the Kirchhoff map `⊕_Q S_Q^⊥ → (K⁶)^nodes` is injective at the generic chart point.* Unsearched: `n(F°) ∈ {4,5}` at `\|E°\| ≥ 9`, and **every** `n(F°) ≥ 6`. *Kill condition: that sentence proved, or a `σ > 0`-everywhere shape exhibited (a PENCIL event) — decided by the `(K-out)` row's disproof paragraph, u26* |
| 8 | **(ZH-2) stratified** | §9 (Zheng preprint) | unrefereed, **idea source never a citation**, deliberately off-board; the shelf's last dispatchable candidate. *Kill condition: (ZH-2)-stratified run or struck — decided by §9.3* |

**Why the (GR-18)(iii) line was rank 1, and what its successors inherit** (updated
2026-09-03; **the row itself is struck above**, so this is rationale carried forward, not a
live ranking). Its input **(GR-18)(i) is a landed theorem** — `def(G) = 0` *alone* forces
`Ĝ` to partition into exactly 6 spanning trees — and the split half is now unconditional
((GR-130)). It passes the **growing-ground-set** test better than anything else on this
board (index set `E(Ĝ)`, size `6(\|V\|−1)`), **counting saturation does not bite** because
it is not an invariant of the escape, and it is `(GR-4′)`-free and stratification-free, so
it owes **none** of the three ledger entries that have sat unswept all arc. **One freedom,
not two (corrected 2026-09-03):** this paragraph used to name two — re-choose the packing
by matroid exchange, and the even branches' bits — but **(GR-140)** (GGLOB, 2026-09-02)
makes the packing a *function* of the solution, so the **packing quantifier is eliminable**
and the exchange freedom is gone. What is left is *orient `H`, 3-colour the hubs twice,
every cycle carrying a head of each `α`-colour and a tail of each `γ`-colour* — which on the
`D = 0`, `Λ = ∅` stratum **IS (GR-10)**, so **(GR-13)'s hardness note now applies to the
residual itself** (*"any proof of (GR-10) must be an existence-of-good-colouring
argument"*), a strengthening rather than a loss. HIT → (GR-10) → (GR-15) → `hK` **on the
tight stratum**; MISS → the first (GR-10) flank in **81** directions. *Kill condition:
(GR-144)'s successor list exhausted, or (GR-10) settled — decided by `(K-grid)` close-it
u7. **Successor 4 is SPENT (GLEAF, ordinal 80) and successor 1 demoted, leaving 2 and 3,
both disfavoured; the list is one step from exhausted and no successor on it reaches
(GR-10).***

**THE DO-NOT-DO, and it is the strongest item this re-rank produced.** **Do not dispatch
another (a′)/(b′) ledger direction.** Fourteen directions (GLAW → GMINM, mostly living in
*Steps G74–G148*) have worked it; the `(K-grid)` status cell's own summary over that span
is *"(GR-15) stays OPEN throughout, unchanged in status, no gap-map status move"*. Its live
successor is bookkeeping by its own words, and it is the thread that produced this board's
rank 2 — refuted the day after it was ranked. The general form: **the next `hK` dispatch's
deliverable must be an argument, with the search demoted to an adversarial control.** The
record is 907/907, 40 742 exhaustive, 549 172 blocks, 1 158 344 instances, 323 adversarial
constructions — and (GR-15)'s status word has never moved. §2.2 already wrote the reason:
*"A search does not carry a reason."*

**Scope of the bar, ruled 2026-09-03 because two live options sat ambiguously inside it.**
The bar is **by attack name, not by span**: it prohibits further **(a′)/(b′) ledger
directions wherever they live**, and *Steps G74–G148* is a *"where they mostly live"*
pointer, **not** the definition. The span is over-broad — it sweeps in work the bar's reason
does not reach. Concretely: **collision dominance (GCOLL, *Steps G110–G115*) is NOT barred**,
nor is any other non-(a′)/(b′) work inside that span; the **one-unit-defect redo of
(GR-79)–(GR-82)** (attack (c) of route-ledger entry 1, GTMPL *Steps G98–G103*) **IS** an
(a′)/(b′) ledger direction and **is** barred, and the two places above that used to offer it
now say so. The reason matters: this bar is **mathematical** — the ledger is spent, and
(GR-15) has not moved across fourteen directions — not a priority call, so the
re-openable-on-merit rule that governs declined options elsewhere on this board does **not**
loosen it. Lifting it for a specific item is a coordinator decision and must be recorded
*here*, not inferred from a row above. *Kill condition: an argument-shaped handle on the
ledger, or (GR-15) moving status — decided by the `(K-grid)` status cell.*

**TWO INTERNAL CONTRADICTIONS FLAGGED — BOTH NOW RESOLVED** (each needed a
whole-file check, and one of them lived in the authoritative status object):
**(a) RESOLVED 2026-09-03 (liveness round, from §4.6 and the gap map — settled
without reading this board, so the verdict is independent of the surfaces that
were in conflict).** The dispute was **three-way**, not two-way: §8.2 listed
**U2** *"live, rank 2"* and **U3** *"live, rank 3"*; §8.6 said U2 was *"delivered
by (GR-16)'s reduction"* and U3 *"already exploited for the tight stratum only"*;
and this board's own below-the-top-three paragraph enumerated *"C2/U1/U3"*,
**silently omitting U2**. Verdict: **§8.2 was the defect.** **U2 is DEAD** by its
own named kill clause — it dies if the support condition is satisfiable at some
class shape, and **(OC-4)** reaches the bad line by a legal chart move at all four
certified habitats, with **(OC-3)** independently ruling the target out in
principle as a matroid statement. **§8.6's verdict was right and its cause was
wrong**: (GR-16) is a *different object*, an exact `3c × 3c` system on `G°`
alone. **U3 is ALREADY-PURSUED**, not live-rank-3 — **and STRUCK
OUTRIGHT since 2026-09-03, direction OBAR**. The below-top-three omission was
correct in outcome. All three surfaces are now repaired; §8.2 carries the
detail. **(b) RESOLVED 2026-09-02 (direction GLIST, which
owned the surface it touched)** — the `(K-grid)` **close-it** cell listed as live route (i)
*"a colouring-existence argument over Step G12's branch bits … + (GR-4′)"*, i.e.
**certificate 3**, while the same cell filed *"the whole certificate-3-uniformity route"*
under do-not-re-run. **Both readings survive: (i) is the STATEMENT and what *Step G37*
killed is the METHOD** — *"cap + `Λ ≠ ∅` flip + `D > 0` lift + (GR-4′)"*, whose first
ingredient, the `g ≤ 1` cap, is false from `n_hub = 8` ((GR-29)/(GR-30)). Calling a
statement a route is what made the cell read as self-contradictory; the cell now says
**targets**, and the dead entry is qualified as the *cap + repair* method. Recorded at
§(K-grid) *Step G158*; no mathematics and no status word moved.

**WHAT A (GR-15) HIT BUYS — ASKED 2026-09-02, ANSWERED THE SAME DAY (direction GPACK,
job 2), AND THE COORDINATOR'S OWN FRAMING OF THE QUESTION WAS WRONG.** A (GR-15) HIT
discharges `hK` **on the tight stratum**; `C11`, a bare odd cycle, is *in* the habitat, is
**not** count-tight, refutes `(AC-6)` as a class statement, and `(K-clos)` calls it
permanent. The scoping recon, having read four of 28 rows, could find no row owning that
remainder and raised it as a question. **It is owned: `§(K-res)/(RS-5)`**, which routes
`def > 0` habitat members to the **escape route** ((RS-6)). **Not an unowned gap** — a
(GR-15) HIT buys the tight stratum and hands `C11`'s stratum to a route that has an owner.
**Three precisions from that row, added 2026-09-03:** **(RS-5)** is *(GR-15)'s criterion
verbatim, quantifier widened past the tight class*, and its quantifier is **disjoint** from
(GR-15)'s — the row's own words are *"closing (GR-15) does **NOT** close this row"*; it is
**(RS-6)** that retires the `def > 0` fringe, by a **proven** mechanism (θ(2,3,7) capped at
`58 < 59` at all 4 admissible colourings); and the row **prices the (K-res) wave** —
reduction free, per-shape checks cheap, uniformity machinery to rebuild above the *Step G23*
waterline. *Kill condition: (RS-5) proved, or a `def = 0` (K-res) shape whose every
admissible colouring has `dim Z > 0` — decided by the `§(K-res)/(RS-5)` row.*

**And the way this box first posed the question INVERTED ITS OWN SOURCE.** It asked whether
the remainder is *"genuinely free — §2.5's `dim R_a ≥ 2` ⟹ escape automatic"*. That
implication is real, but **§2.5 is a NEGATIVE result** and citing it as a freeness route
reads it backwards: its content is that at tight shapes the count **forces**
`dim R_a = 5 + def(G′) − def(G − v) = 1`, so *"carry `dim R_a ≥ 2`"* is exactly the
invariant that **cannot** be carried — and §(K-flank) *F5(d)* makes it worse, with five
legal seeds where the count predicts `1` and the geometry delivers `0`. §2.5's own summary
is *"counting data is saturated **and provably blind** to the discriminating phenomenon"*.
**Do not quote §2.5 as supplying freeness anywhere.** Recorded rather than silently fixed
because the mis-citation was the coordinator's, it was written into this board, and a
later session reading it would have inherited a route the section exists to close.

### 8.1 Continue the current architecture

The induction is the framework (§4's framing correction); these are attacks on
its named residuals, all slice-sized, none needing an adjudication.

| option | what it would buy | owner |
|---|---|---|
| ~~**(GR-R1)**~~ (§(K-grid), GFLOW's clause) | **DONE — PROVEN 2026-08-25 (direction GFLIP, ordinal 30)**, strengthened to `≥ \|δ\|` feasible majority flips; (b′)'s `n`-free `≤ 12` is now a **theorem** | §(K-grid) *Steps G116–G119* |
| ~~**(GR-C2)**~~ (§(K-grid), GFLOW's) | **SETTLED per-configuration in both directions 2026-08-25 (direction GCHEAP, ordinal 31)**: every-step form PROVEN for `n_hub < 6\|δ\|` — **(b′) at the constant 2 is a THEOREM on the whole `n_hub ≤ 6` stratum** (modulo (GR-C1) at `n = 8, 10`) — and per-configuration form REFUTED from `n_hub = 12`, boundary exact both ways. **Read with (GR-127) (GMINM, 2026-08-26), added 2026-09-03:** (b′) has **three inequivalent readings** and the ledger consumes the third — **(P)** `∀M` **FALSE** ((GR-122)), **(m)** `min_M(d_adm − d_par)` **PROVEN** ((GR-126)), **(L)** the difference of minima (what `gdev.min_dev` actually computes) **untouched by both**. These headlines are (P)/(m)-shaped; five directions attacked a statement the consumers never used | §(K-grid) *Steps G120–G124* |
| ~~**(GR-104)(i)**~~ (§(K-grid), GCHEAP's) | **REFUTED 2026-08-26 by (GR-122)** — §(K-grid) *Step G142*, direction GHWIT: an `n_hub = 20` all-(2,2) pair of gap 4, **one day after it was ranked 2**, with (GR-86)'s cap attained. Row kept as the dated record; the price form is **not a live option**. *(This row still read "RANK 2 on the 2026-08-25 re-rank" until 2026-09-03 — the main list above had been corrected and this table had not, so §8.1, the menu a session reads for slice-sized work, offered a refuted route for a week.)* The surviving question on this chain is the **(L)** reading — *is the ledger gap ever `≥ 3`?* — and it is barred by the do-not-do above | §(K-grid) *Steps G124, G142* |
| ~~one-unit-defect-budget redo of (GR-79)–(GR-82)~~ | would finish ledger attack **(c)** past its `n_hub ≤ 14` boundary — **BARRED 2026-09-03: it IS an (a′)/(b′) ledger direction** (attack (c) of route-ledger entry 1), so the do-not-do above reaches it by its own reason. **Mathematics still OPEN**, named in `(K-grid)` close-it u26 as attack (c)'s successor; bookkeeping-grade even unbarred, since (GR-84) already realizes both unbounded residual cases at `n_hub = 16` | §(K-grid) *Steps G98–G103* |
| ~~`rank(Q\|_D) = 3` — the **ℚ(i) eigen-block leg**~~ | **RUN 2026-08-25 (direction OQRANK, ordinal 32) — a graded HIT: input (a) DELIVERED at all 174 certified classes**, per-class/per-colouring-generic, by the completed ⋆-eigen-block mechanism; the naive first-colouring form REFUTED as a class statement (27/174, incl. the (OC-42) **WALL**); zero (K-tight)-event rulings. O29's open caveat is answered *graded*: the wall and the secant positives are combinatorial, the general per-block condition is not. Successors, **both DELIVERED 2026-09-02 (direction OWALL, *Steps O47–O51*; this clause named them as open until 2026-09-03)**: (OC-44)(iii) is **REDUCED to (OW)**, a geometry-free partition-constrained colouring-existence statement in (GR-10)'s object class ((OC-55)), and *Step O41*'s own route is **REFUTED BY LOGIC** ((OC-52) — the conjunct it attacked is implied by the one it did not); the second confinement's mechanism is **(Z)**, the `≤ 3`-class cycle vanishing rule, accounting for **19 of the 20** points ((OC-51)/(OC-54)). What is live is **(OW)** — corrected table row 3 | §(K-out) *Steps O37–O41, O47–O51* |
| collision dominance `min_M B(M) ≤ d_adm` | GCOLL's successor to the refuted (GR-64)(R2) — **OPEN**, non-vacuous at 180 Petersen shapes, vacuous at the other 81 302; **NOT barred by the do-not-do** (GCOLL lives inside *Steps G74–G148* but is not an (a′)/(b′) ledger direction). *Kill condition: `min_M B(M) ≤ d_adm` proved or refuted — decided by `(K-grid)` close-it u16* | §(K-grid) *Step G115* |
| (OC-19) input (c) class-uniformly | OCON's #1 by value — but **(GR-15)-flavoured**, so it re-enters the oldest missing technology. *Kill condition: `H/X` rigid class-uniformly — decided by the `(K-out)` row, u9* | §(K-out) *Step O18* |

### 8.2 Change the inductive invariant

| option | status | note |
|---|---|---|
| **C1** dominance of the `V_bc` map | **STRUCK** 2026-08-05 | dominance *holds* (rank 9), but both stated reasons refuted and it does not reach uniformity (§(K-dom)) |
| ~~**C2** carry `V_bc` general position as a motive conjunct~~ | **STRUCK 2026-09-03 (direction DSAT) — its own kill condition FIRED** | The trace this row demanded was run: the strengthened motive is **UNSAT off the class and SAT on it**, so **C2 dies as a *uniform* carry** — §(K-dom) *Steps D8–D14*. **(DM-6)** *(proven)* at a degree-2 `a`, `dim V_bc = dim mot(G−a) − dim mot(G) ≥ def₃(G−a) − def₃(G)`; **(DM-7)** *(proven)* `def₃(G−a) − def₃(G) ≥ 4` then makes the conjunct at `a` unsatisfiable at **every** realization; **(DM-8)** it fires at both (K-res) habitats — which `hK` carries — and at none of the five class ones. **Read the halves apart: the (K-res) half is PROVED, the class half MEASURED at five shapes, so C2 is NOT shown dead as a class-only conjunct** — that form stays blocked by §(K-ind) *Step I6* (no chart morphism at `hcontract`) rather than by satisfiability. Two further findings: the index set is forced to the degree-2 triples, which **passes** the growing-ground-set filter ((DM-5)); and "general position" read as a *general point of `Gr(3,6)`* is unsatisfiable at **6 of 8** indices of the class exemplar θ(3,4,5) ((DM-10)), so only the (PC-Z) escape reading survives. **This row's own clause *"nothing in `(K-dom)` bears on C2"* is REFUTED** — the deciding mechanism is a §(K-dom) dimension count, and it reproduces (D1)'s exact class-vs-(K-res) split. Kept as the dated record. *Successor, and it is the whole class-side question: a class member with a degree-2 `a` and `def₃(G−a) − def₃(G) ≥ 4`, or a proof that none exists — decided by the `(K-dom)` row's close-it* |
| **U1** retarget §2.4's image problem to the annihilator | **live, rank 1** | §4.6. `(K-ann)`'s close-it still names the remaining item as *"a class-uniform independent-point recipe ((ANH-9)(iii)) — the same missing technology as §(K-grid)'s residual"*. *Kill condition: (ANH-R1) made class-uniform, or the retarget refuted — decided by the `(K-ann)` row, close-it u6* |
| ~~**U2** hinge-rate / cycle-space presentation~~ | **STRUCK 2026-09-03 — DEAD by its own kill clause** | U2 dies if its support condition is **satisfiable at some class shape**, and it is: **(OC-4)** reaches the bad line by a legal chart move at **all four** certified habitats. **(OC-3)** independently rules the target out in principle, it being a matroid statement — *no counting, matroid or placement-blind argument* can deliver it. **This row read *"live, rank 2"* for weeks while §8.6 recorded U2 as delivered; §8.6 had the verdict right and its cause wrong** (it credited (GR-16)'s reduction, which is a *different object* — an exact `3c × 3c` system on `G°` alone). Kept as the dated record, not removed |
| ~~**U3** restate `hK` as a **non-existence**~~ | **STRUCK 2026-09-03 (direction OBAR) — its kill condition FIRED on the admissibility branch** | Its named first step was **delivered more generally as (OC-35)** (§(K-out) *Steps O31–O36*, SIGZ), leaving **one genuine residue**: the ledger nobody ran on `H ∪ {bar along M}`, gated by an **unverified** admissibility check. **That check ran and is NEGATIVE three independent ways** (§(K-out) *Steps O52–O57*, **(OC-56)**): `bc ∉ E(G)` so the object is no subgraph of `G`; a **bar is one row** where (OC-36)'s ledger counts five; and a *hinge* along `M` needs **both** halves of (Λ0d) to fail, which **(σ7)** rules out — on (σ7)'s own basis, conjunct 4's argument plus 39/39 witnesses, so chart-wide only as far as (σ7) is. **And the ledger had nothing to compute:** a `b`–`c` attachment adds no topological path, its whole increment being `dim(A ∩ V_bc^{⊥_E})` **(OC-57)**, so the bar is in a support **iff** `V_bc ⊥_B C(M)` — **(T3) verbatim**, the (K-wit) row's own content **(OC-58)** — while the five-row *hinge* reading makes the statement **FALSE** pointwise **(OC-59)**. **The logical-form move (§2.3) does NOT survive**: the non-existence *is* a rank lower bound, so the asymmetry was never evaded. Kept as the dated record. *No kill condition remains — this row is closed* |

`U1`–`U3` **interlocked** — one target, one machine, one logical form — rather
than being independent bets (§4.6's own framing). **As of 2026-09-03 only U1
survives, and now with nothing else on the shortlist at all**: U2 is struck by
(OC-4)+(OC-3), and U3 is **struck** by direction OBAR — its residue's
admissibility gate came back negative and its ledger had nothing to compute.
The interlock is why that matters — **U1 inherits the shortlist's whole
remaining weight, not one third and no longer two thirds of it.** Nothing in
either strike bears on U1: its residual (ANH-9)(iii) is untouched by both.

### 8.3 Change the target

| option | status | note |
|---|---|---|
| **C3** — pin only a subset `S` of bodies to pencils | **GATE PRICED 2026-08-24 (probe C3-AVOID) — NO-GO as a crux-avoidance route; live only RE-SCOPED** | The *"reduce avoiding `S`"* gate is decided: universal threshold **exactly `\|S\| ≤ 2`**, capped by a conservation law at `2 μ(G)` with `μ = \|E\| − \|V\| + 1`, no structural hypothesis on `S` lifting it, `\|S\| = 3` failing at the cycles `C_3 … C_6`. So C3 does **not** relocate the hard case for a chemically meaningful `S`; what survives is `μ` as the exact grading, and the relocation is into **Case-I gluing**, which the probe did not price. Full mathematics + caps: **§4.7**; landing record `notes/Pencil-fanout.md` §"Probe C3-AVOID". *Kill condition: (AV-7)'s Case-I gluing arm priced — decided by §4.7 (AV-7). Re-checked 2026-09-03: still **unpriced and untouched**; no direction has run it.* |

### 8.4 Attack a kernel's own proof

| option | status | note |
|---|---|---|
| **route σ** — the polarity applied to the seed | **candidate closure; obligation 1 Lean-blocked, obligations 2–4 open and NOT blocked** | Corrected 2026-08-20: only obligation 1 is Lean ("*not new mathematics*"). **(2)** scope — the `dim R_a = 0` stratum untouched and the **(K-res)** habitat unsampled, so **route σ is not a route to (K-res)**; **(3)** (σ6)'s failure direction unwitnessed; **(4)** the branch it closes has **never been observed nonempty**, so its value is **insurance, not repair**. Obligations 2 and 4 are decision-relevant *before* commissioning any Lean. §(K-σ) *Step σ5*. *Kill condition: an obligation discharged, or obligation 4's branch observed nonempty — decided by the `(K-σ)` row, status u8* |
| **option B for `hK`** — the stress-function infrastructure | **DECLINED 2026-07-30 under that date's evidence; re-openable on mathematical merit** (re-stated 2026-09-03 — it previously read as a standing bar) | research-scale. An adjudication records a **past priority call under past evidence, not a permanent prohibition**: re-opening needs a **mathematical reason, not permission**. Note its **first step is a design pass**, which the 2026-08-05 Lean hold does not park. *Kill condition: commissioned and run, or a cheaper route closing `hK` first* |
| **option B for `hbareSplit`** — the insertion calculus | **DECLINED 2026-07-30 under that date's evidence; re-openable on mathematical merit** | was recorded here as *the only identified path* to closing `hbareSplit` — **no longer true since 2026-08-20**: KBARE-FALSIFY refuted its (K-bare-ext) target as stated *and* named two successor shapes (next row). **Its two stated prerequisites are DISCHARGED (corrected 2026-09-03; this row asserted them as still owed):** the **KT pp. 684–691 re-pin landed 2026-08-02** — §(K-tight) *Step 0*, against the carrier, **exact at arbitrary target-rank seeds** — eighteen days *before* the edit that recorded it as owed; and the corank-stratified **boundary-load calculus transports** at **192/192** placements, corank identity scope-free (KBARE-FALSIFY). So option B is un-commissioned by **choice**, not by blocker, and its first step is a design pass the Lean hold does not park. *Kill condition: commissioned, or the (BE-14) thread closing `hbareSplit` without it — decided by the `(K-bare)/(K-bare-ext)` row* |
| **(K-bare) development — the (BE-14) thread** | **LIVE and CONTINUOUSLY COMMISSIONED since BATTAIN (*Steps BE9–BE13*) through BDEGTWO (*Steps BE135–BE140*), 140+ steps** — corrected 2026-09-03; this row read *"live, un-commissioned"* while §8's own box eleven lines above said *"running since BATTAIN (39) and 20+ directions in"* | Of KBARE-FALSIFY's two successor shapes, **(ii) "bypass the antecedent" IS the running thread** — the row's target is **(BE-14), direct attainment**, discharging `hbareSplit` **and** `PencilPair`'s unconditional conjunct — while **(i) the `∃`-seed form meets §(K-tight)'s wall**. Neither is option B. Current locus: the **only open step is S-mark, the 2-cut composition lemma**; **(PENCIL-SATURATES-CHART)** is a **THEOREM at every side-degree-`1` terminal** so **14 → 12** generically; at side-degree `≥ 2` the `(∗)` route is **DEAD** ((BE-130)) and BDEGTWO settled both of (BE-134)'s gaps, leaving the **METHOD** as the obstruction ((BE-139)). Gap-map row: `(K-bare)/(K-bare-ext)`, *Steps BE1–BE140*. *Kill condition: (BE-14) settled — decided by that row, u38–u39* |
| **(K-res)** | **ATTACKED TWICE — RESGRID (2026-08-28) and RPOOL (2026-09-03)**, which opened `§(K-res)/(RS-5)`, *Steps RS1–RS16*. **RPOOL exercised this row's own kill condition and it FIRED: (RS-5) is REFUTED.** The **wave** stays declined and is now RE-PRICED upward — a user call, re-openable on mathematical merit; the declined wave did **not** lock out the cheap slice, which is what found the flank | a kernel of `hK`'s difficulty class on the complementary habitat, proof route *strictly harder*; W4 route 3 cannot close without it. RESGRID transported the §(K-grid) geometry **verbatim** ((RS-1)–(RS-4) — still theorems) and **REFUTED the deficient fringe with a mechanism** ((RS-6)). **RPOOL then refuted (RS-5) itself**: the witness `R20 = family_g(5,(0,0,2),(4,4,4))` is `widened.W19` with a one-edge-longer core and was in the recorded 255 pool from 2026-08-02; **30 of the pool's 102 `def = 0` members refute (RS-5), 72 carry exact-point proofs**, and the split is governed by `index < 2·g_forced` ((RS-15), 0 counterexamples at 153 shapes). **(RS-5)'s quantifier stays disjoint from (GR-15)'s** — the refutation touches the tight side in neither direction. **What the wave now is:** *prove the repaired statement uniformly* **and** *route the `index < 2·g_forced` members*, which have **no named home** — strictly more than before. *Kill condition: the repaired statement settled, or a flank at `g_forced ≥ 2` exhibited (which would also refute (RS-15)) — decided by the `§(K-res)/(RS-5)` row* |

### 8.5 Test the architecture instead of extending it

The move this board's own risk analysis recommends before more `hK` spend.

| option | status | note |
|---|---|---|
| ~~**`hbareSplit` falsification probe**~~ | **LANDED 2026-08-20 — a T1 HIT**: (K-bare-ext) **refuted as stated**, `hbareSplit` itself untouched (its consequent is an `∃`; every probed gadget attains) | §(K-bare-ext) *Steps BE1–BE8*; landing record `notes/Pencil-fanout.md` §"Probe KBARE-FALSIFY". The successor shapes it named are priced on §8.4's board (the (K-bare) development row) |
| the geometric route to a disproof | **NARROWED, still open** (direction OGEOM, 2026-08-26) | The **counting** route is dead ((OC-37)). The geometric half is now free **by an argument** on everything searched: `σ` depends on the induced `H` alone ((OC-46)); paths of length `≥ 6` are dead, so girth `≥ 7` kills every cycle and bouquet — **(OC-37)(ii)'s one-unit topology dies class-uniformly** ((OC-47)); 91 260 live cores, **0 candidates**, and `{σ = 0} ≠ ∅` becomes a theorem at 275 342 class pairs, upgrading (OC-39) from sample to theorem ((OC-48)/(OC-49)). **Unsearched, and the row stays open for exactly these:** `n(F°) = 4` at `\|E°\| ≥ 9`, `n(F°) = 5` at `\|E°\| ≥ 9`, every `n(F°) ≥ 6`. Successor is one shape-free sentence — injectivity of the Kirchhoff map at the generic chart point. §(K-out) *Steps O42–O46*. *Kill condition: that sentence proved, or a `σ > 0`-everywhere shape exhibited (a PENCIL event) — decided by the `(K-out)` row's disproof paragraph, u26* |
| ~~**(T)** / **(V)** / **(E-loc)**~~ | **ALL THREE SETTLED 2026-09-02 — a dated record, not an option** (this row read *"open, slice-sized"* until 2026-09-03) | **(T) is a THEOREM** (direction WTRI, *Steps TF1–TF5*): no feasible residual carries a triangle at all, by **two landed feasibility transfers** the section's own *Step 4* had not inventoried — so the *"genuine research gap, not a numerics gap"* and landed-**invisible** readings above are both retired. **(E-loc) is REFUTED** (direction WELOC, *Step EL5*) by the `\|V\| = 32` witness `T32`, two *disjoint* count-dependent `C₄` cores; **(E)** returns to being the primitive gap — open, **tight** (`f = 4`), and **off every W4 path** — and its successor **(E-pair) is a THEOREM** (WPAIR + WGROW, *Steps PR1–PR6*/*GW1–GW6*), with **(V)** a theorem alongside it ((PAIR-6)). **Net: W4 route 3's non-user-call cost list is EMPTY** — what remains is **(K-res)** (a user call, §8.4) and the held W4 build. `notes/Pencil-W4-informal.md` §"widened kernels (routes 1/3)" |

### 8.6 Durable negatives — do not re-run

**STANDING RULE FOR THIS LIST, added 2026-09-03.** Every entry here carries a
**back-link**: the recommendation surface that still points the other way, struck
or annotated **in the same commit**. Forward kill conditions alone do not catch
this list's own failure mode — §5.3 item (i) sat here as a durable negative for
four weeks while §5.3 listed it as the CAS layer's *highest-value unrun* item,
and **no reader of §5.3 could see that the kill already existed here**. It cost a
dispatch (direction GELIM).

§4.6's six refutations; §2.5's counting saturation; **C1**; both literature
hunts (rigidity-side, Δ-matroid-side); the symbolic meta-option, landed as
`m2/lambda0.m2`.

**`C2` as a UNIFORM carry — added 2026-09-03 (direction DSAT), and the scope
line is part of the entry.** C2's own kill condition fired: the satisfiability
trace it demanded returns **UNSAT off the class**, provably — §(K-dom)
*Steps D8–D14*, **(DM-6)**/**(DM-7)**/**(DM-8)** — at both (K-res) habitats,
which `hK` carries. Do not re-run the trace, and do not re-open *"carry `V_bc`
general position at every index of every object the reduction reaches"*. **What
this entry does NOT cover, stated because the summary would otherwise outrun
its caveat:** the **class-restricted** conjunct is *not* on this list. The class
half of the measurement is **five shapes**, not a theorem, so a proposal to
carry the conjunct on the pinned class alone is answered by §(K-ind) *Step I6*
(no chart morphism at `hcontract`) and by the `(K-dom)` row's open successor —
**not** by this negative. Nor is *"general position"* re-openable in the
`Gr(3,6)`-generic reading: **(DM-10)** kills that at 6 of 8 indices of the class
exemplar θ(3,4,5), so the only live reading was always the (PC-Z) escape.
*Back-links, all struck or annotated in the same commit: **§8.2**'s C2 row (was
"live, unpriced", and its clause "nothing in `(K-dom)` bears on C2" is
**refuted**); **§4-C2**'s kill-condition box (whose "never tested … and the
Lean hold blocks it" was **wrong twice** — the trace is numerics plus a source
read); **§8**'s below-the-top-four list (which carried "C2's satisfiability
trace" as live); **§8**'s "§8.2's C2/U1 keep their standing notes"; **§4**'s
gate box; and §(K-ind) *Step I6*, which read as C2's only kill.*

**`U2` and `U3` — verdict kept, cause REPAIRED 2026-09-03.** This list said `U2`
was *"delivered by (GR-16)'s reduction"*: the verdict is right, the cause is
wrong — **(GR-16) is a different object**, an exact `3c × 3c` system on `G°`
alone. **U2 is dead by its own kill clause**: its support condition is satisfiable
at a class shape, **(OC-4)** reaching the bad line by a legal chart move at all
four certified habitats, with **(OC-3)** ruling the target out in principle as a
matroid statement. `U3` is **STRUCK OUTRIGHT (2026-09-03, direction OBAR)**, and
therefore belongs on this list rather than beside it: its negative-form insight
was already-pursued, its first step delivered more generally as **(OC-35)**, and
its one residue — the `H ∪ {bar along M}` ledger nobody ran — is **RETIRED**, the
admissibility check that gated it having come back **NEGATIVE** three
independent ways (§(K-out) *Steps O52–O57*, **(OC-56)**) with the ledger itself
having **nothing to compute** (**(OC-57)**/**(OC-58)**: the object's whole
content is one Klein condition on `V_bc`, i.e. (T3) restated). **Do not re-open
the residue as a ledger question, and do not re-pose "is the meet-line bar an
(OC-35) subgraph" — it is not, and one of the three reasons is that a bar is a
one-row constraint where that ledger counts five.** The one clause here whose
strength is *inherited* rather than proved outright is the hinge branch, which
rests on **(σ7)** — conjunct 4's argument plus 39/39 witnesses — so
*"chart-wide"* means *"as far as (σ7) is"*, never more. *Back-links:
**§8.2**, whose rows read "live, rank 2" and "live, rank 3" until 2026-09-03 —
both now struck there, U3's row closed with no kill condition remaining; and
**§4.6**, whose U3 blockquote and rank-3 subsection carried the identical
admissibility flag and are struck in the same commit as this entry, the two
having been required to agree.*

**§5.3 item (i)** — the `V_bc` pullback elimination question — **STRUCK
2026-09-03** (direction GELIM, killed before computing). **Its cause here was
wrong and is now repaired:** it is **not** ruled out by §5.3's local-frame
feasibility boundary, which the strike says it would *clear* (`k = 3`: ~14
indeterminates at degree 12, *"it would run"*). It is dead because at **`k ≥ 4`**
— the whole class stratum, by (D3) — it is not frame-expressible **and has no
content**, (D4)'s dominance already giving `φ_G^*(f_B) ≢ 0` per shape; and at
**`k = 3`** it is exactly **(K-res)**, outside the pinned class, with the
containment **already refuted pointwise** ((D4), all 21 seeds). Full disposition
at §5.3. *Back-links: **§5.3**'s "Others, in rough order of value" list, where it
was item (i) and is now struck; and — **flagged 2026-09-03 as owed, PAID THE SAME DAY in
`ba0db779`, and STRUCK HERE 2026-09-03 (ninth strategy pass), this file having been the last
surface still claiming the debt** — **`notes/CLAUDE.md`**'s own description of this file. It
read "what remains of §5.3 is item (i) … which … sits beyond §5.3's own local-frame
feasibility boundary": a THIRD copy of this entry carrying the SAME refuted cause, and the
worst-placed of the three, since `notes/CLAUDE.md` **auto-loads at the start of every session
that touches `notes/`**. It now records the strike **and** that the old cause was wrong. The
flag outlived the repair by exactly one commit, for the ordinary reason this list exists to
catch: `ba0db779` edited `notes/CLAUDE.md` and never opened this file.*

**Added 2026-08-24:** C3's *"reduce avoiding `S`"* gate — settled at threshold
`|S| ≤ 2` with the exact ceiling `2 μ(G)` (§4.7, **(AV-3)**/**(AV-4)**); do not
re-open it as a cardinality question, and do not look for a structural hypothesis
on `S` (**(AV-5)** refutes that class). *Back-link: **§8.3**, whose C3 row states
the same NO-GO — consistent, no repair needed.* What is *not* a durable negative
and is the live successor: **(AV-7)**'s Case-I gluing arm, **unpriced and
untouched as of 2026-09-03**.

**Nothing on this list is a priority call.** Every entry is a refutation, a
theorem, or a measured impossibility — so the *"declined once, re-openable on
merit"* rule that governs §8.4's two option Bs and the (K-res) wave does **not**
reach anything here. The one bar that is *adjacent* to this list without being on
it is the **do-not-do** above; that one is also mathematical (the ledger is
spent), not a priority call.

## 9. External technique transfer — the Zheng body–pin preprint (2026-08-21)

**What this is.** A read of a project-new external source against the kernel-(K)
arc, producing six named candidates **(ZH-1)–(ZH-6)** for a future direction
pick.

**STATUS, 2026-08-26 (banner corrected by the 2026-09-03 liveness sweep, which
found this paragraph contradicted by §9.2 and §9.3 below). The shelf is
TWO-FOR-TWO and has exactly ONE dispatchable candidate left:** (ZH-1)
**STRUCK** (direction ZSHEAR, driver `notes/scripts/w4/zshear.py`, canonical
home §(K-shear)); (ZH-4) **STRUCK** (direction ZJACOB, driver
`notes/scripts/w4/zjacob.py`, §(K-jac)); (ZH-3) **struck by absorption** into
(ZH-4); (ZH-5) a **design note**; (ZH-6) **write-up material**; **(ZH-2)** live
in its **stratified reading only**. The §2.5 counting-saturation checks (ZH-2)
and (ZH-3) owed are **DONE** (2026-08-26, §(K-shear) *Secondary deliverable*).
Two of the six therefore *are* verdicts and *do* carry committed drivers — the
sentences this paragraph used to contain, *"no claim here is a verdict, none
carries a driver"* and *"two of them owe a §2.5 check"*, were both false from
2026-08-26 and are struck here with that cause.

Same discipline as the rest of this file otherwise: strategy, not mathematics —
the four surviving readings are arguments a successor should attack rather than
assume, and every mathematical claim points at the section that owns it. **The
shelf is deliberately UNPRICED — it is not on §8's board — and that is a
priority call, not a prohibition:** per the 2026-09-03 user ruling an
adjudication records a past priority call under past evidence, so any entry
below may be re-opened **on a mathematical reason, without asking**. What that
ruling does *not* touch is the evidential caveat that follows, which is a
statement about the source's reliability rather than about this project's
priorities and stays exactly as strong as it is.

**Provenance and status caveat.** D. Zheng, *Stress Degeneracy of Direction
Complexes of (2,2)-Sparse Graphs and Three-Dimensional Body–Pin Rigidity*,
preprint dated August 2026, read in full from
`.refs/zheng-2026-body_pin_partition_collinearity_flag_en_20260816.pdf`. It
claims the Király–Tanigawa body–pin partition conjecture (their Conjecture 5;
Jackson–Jordán–Villányi Conjecture 7.6) in `ℝ³`. **It is unrefereed**, its own
acknowledgment credits an AI assistant with *"the refinement of proof details,
the Lean formalization and its verification"*, and its appendix names a Lean 4
formalization repository (Lean 4.29.0 plus a pinned mathlib commit).
**Neither the paper nor the repository has been independently checked by this
project.** Per top-level `CLAUDE.md` *Referencing prior work*
and `DESIGN.md` *Formalize everything the argument uses*, nothing below may be
cited as established: these are **idea sources**, and anything load-bearing
would be a formalization target. **This does not disturb §8.6's two durable
literature-hunt negatives** — those hunted for the pencil statement and for
Δ-matroid structure; this source was not found by a hunt and is about neither.

*Kill condition for this caveat (added 2026-09-03): the project independently
checks the source. **It never has**, and nothing in-tree decides it — that
absence IS the status. No reader may treat this section as a verification, and
no (ZH-\*) status below is upgraded on the strength of the source: an entry is
live here only where the **project-side** question it names is live.*

**Where the load sits in the source, if a successor does go read it.** Its whole
induction turns on the interaction of its Lemma 3.4 with its Proposition 3.3,
and a dimensional analysis done at read time shows Lemma 3.4 sits *exactly* on
its boundary at `d = 3` (the identity `2(d−1) = d+1`, which fails at `d ≥ 4`).
There is no slack in that count, so an error there would be structural rather
than repairable. Read its §3 before trusting its §5. *(Kill condition, 2026-09-03:
an in-project check of the source's §3 — **never run**; the paragraph above is
a read-time dimensional analysis, not a verification.)*

### 9.1 The one identity — its quadratic form IS ours

Not an analogy. §(K-pitch) *Step 0* sets `B(x,y) = ⟨x, ★y⟩` and the pitch
quadric `Q(x) = B(x,x)`, with `Q(x) = 0` ⟺ `x` is a line extensor. The source's
§5 sets `q(ω,b) = ω·b` on `k³ ⊕ k³`, names it the **Split–Klein form**, and its
Lemma 6.2 gives `q(X) = 0` ⟺ the twist has a fixed point. Same form, same
vanishing locus, same meaning (zero pitch = rotation about a line, not a screw).

The logical roles coincide too. §(K-pitch)'s route needs `Q(r̃) ≢ 0` on the seed
variety **uniformly over the class**, one scalar polynomial per (graph, split);
the source's Theorem 1.3 asserts that the `|E_F|` polynomials `q(X_u − X_v)`,
indexed by the edges of a `(2,2)`-sparse graph, cut codimension exactly `|E_F|`
on the locus where the `X`s are pairwise distinct — a **class-uniform
non-degeneracy statement for the same quadric, indexed by a graph, over any
infinite field**. That is the arc's open thing, in the arc's own object.

Relevant adjacency: §7 already lists **Witt's theorem** and the α/β
classification of the Klein quadric's maximal isotropics among the classical
facts in use here, so the machinery below sits next door to machinery already in
play — a successor should first check whether it is *already* implicitly
available rather than new. **That advice was vindicated (2026-08-26):**
§(K-shear) *confirms* this section's identification of the two quadrics while
killing the device built on it — `Φ_S = Λ²(T_{−s})` identically, so the shear
group **is** the translation subgroup of `PGL(4)` on line coordinates and `Q`
is its own defining invariant. The identity stands; the machinery was already
ours. *Kill condition: the two forms differ. Deciding surface: §(K-pitch)
*Step 0* and §(K-shear) — no gap-map row.*

### 9.2 The six candidates

**(ZH-1) The Witt shear as a uniformity device. — STRUCK 2026-08-26, direction
ZSHEAR: REFUTED, and the reason is that the shear is a GAUGE transformation.**
Canonical home for the refutation is `notes/Pencil-informal.md` §(K-shear)
*Steps SH1–SH5* — not restated here. *(Kill condition as this entry itself
named it — "if that failure locus turns out shear-invariant, (ZH-1) dies
immediately" — **FIRED**. Deciding surface: §(K-shear), driver
`notes/scripts/w4/zshear.py`; **no gap-map row** — the direction moved no
status. Struck, not deleted: the original pitch stands below.)* In one line: `Φ_S = Λ²(T_{−s})`
identically, so the shear group **is** the translation subgroup of `PGL(4)` on
line coordinates, `Q` is its own defining invariant, and the §(K-tight)
criterion matrix is **literally the same matrix** in the pushed basis (150/150
entry-for-entry, `dim R_a` moved at **0 of 45**) — so the bad-`S` set is `so₃`
or `∅`, never a *proper nonempty* affine subspace, and (ZH-1)'s mechanism is
**vacuous**. The death is **stronger** than §4.6's predicted
growing-ground-set one. The reading below is preserved as the shelf's original
pitch. The source's Lemma 5.1: the
orthogonal group of `q` contains unipotent shears `Φ_S(ω,b) = (ω, b + Sω)` for
`S` skew, which fix **each generator individually** (not merely the ideal),
because `ωᵀSω = 0`. Its uniformity argument is then: for each pair, the bad `S`
form a **proper affine subspace** of `so₃(k)`; finitely many proper affine
subspaces cannot cover an affine space over an infinite field; so a good `S`
exists. That converts *"exhibit a good seed"* into *"avoid finitely many proper
subspaces"*, with the number of subspaces irrelevant.

*What it would buy.* (i) A **propagation mechanism** the arc lacks: under a group
fixing every generator, one witness certifies a 3-parameter orbit, whereas today
`P ≢ 0` is re-established per habitat. (ii) It **dissolves** rather than pays the
field-scope problem — §8.4's route σ is an `ℝ`-only construction
(`screwComplementIso`) aimed at an `hK` quantified at general `[Infinite K]`, and
generalizing its polarity cost a whole section; Lemma 5.1 needs only that `k` be
infinite, which is exactly `hK`'s hypothesis.

*The cheap decisive test, and the honest risk.* §(K-flank) *Step F5(d)* exhibits
five legal nondegenerate target-rank `G′` seeds at `P21` with `s₀ = 1`,
`dim R_a = 0`, `dim U = 1` that the *Step 2.3* calculus **proves** fail at every
placement. Those are known escape failures and therefore the right adversarial
bed: apply a random `S ∈ so₃` and ask whether the criterion matrix's minors move
while the target-rank condition survives. **If that failure locus turns out
shear-invariant, (ZH-1) dies immediately — and dies for exactly §4.6's
growing-ground-set reason**, since `so₃(k)` is a *fixed*-dimensional group and so
cannot see the graph. A new committed driver
(`notes/scripts/w4/shear.py` or equivalent) would be required by the standing
reproducibility rule.

**(ZH-2) A transcendence-degree potential function — the deepest reframe.** The
source never works at a point. It works at the generic point of a family over
`K = k(Y)` and carries the additive potential
`∆ = (self-stress dim) + trdeg_k K − 3|V|`, target `∆ ≤ 0`, with a
vertex-deletion increment and the tower law for `trdeg`. Its entire proof is
*"the increment is ≤ 0 at every reduction step, with one exception, which you
decorate and carry"*.

*Why it targets the open thing.* The arc's criterion is **pointwise** (*"one
witness seed decides a split"*, §(K-pitch) *Step 0*), and class uniformity is
precisely the difficulty of producing a point for every member of an infinite
class. A potential function would never exhibit a seed. The arc already has the
combinatorial arithmetic for reductions — the *Shared dictionary*'s **(SD-6)**
computes `f(V(G′)) = f(V(G)) − 5ℓ + 6(ℓ−1) = ℓ − 6`, exactly such a per-step
count; what it lacks is a *geometric* quantity riding along on it, and `trdeg` of
the pencil realization's coordinate field is the natural candidate.

*Filter check — **DONE 2026-08-26**, §(K-shear) *Secondary deliverable* (this
paragraph's "owed" wording is struck here, 2026-09-03).* `∆` is indexed by
`V(G)`/`E(G)` and grows with the graph, so it passes §4.6's
growing-ground-set test. Against §2.5 it **SURVIVES in its stratified reading
and DIES in its whole-chart reading**, and the distinction is the whole content
of the check: at the generic point of the *whole* chart
`trdeg_k K = dim(chart)`, a function of hub/degree data alone, so `∆` is
count-expressible and §2.5 bites exactly; on the stratum carrying the
degeneracy `trdeg` is that stratum's dimension, which *Step F5(d)* and §(K-out)
**(OC-38)**(iii) show is **not** count-predicted. Carry the pass's own caution:
pointwise self-stress dimension is upper semicontinuous and jumps *up* exactly
where `trdeg` drops, so the sign of the increment must be checked **per
reduction move**, never assumed additive. *Kill condition: `∆` taken
whole-chart (**fires**), or a reduction move whose increment cannot be signed.
Deciding surface: §(K-shear) *Secondary deliverable* — the shelf has **no
gap-map row**.*

*A second check, **OWED and never run** (added 2026-09-03).* `∆` is a potential
carried **along reduction steps**, and §(K-ind) proves *"no move of
`pencil_reduction` relates two class members"*, with *Step I5*(2) showing the
arc's one dimension-carrying quantity moving in the **fatal direction** under
the split (`9 → 4` at `k: 4 → 3`). A potential-function induction may
legitimately descend *out* of the class, so this is **not** claimed as a kill —
but a dispatch must say which it does. *Row: gap-map **(K-ind)**.* Highest
ceiling, highest risk: this is a reformulation of the kernel, not a route inside
the current one.

**(ZH-3) A rank lower bound from a codimension count. — RE-LABELLED
2026-08-26, direction ZSHEAR: CIRCULAR AS POSED, which supersedes "owes a §2.5
filter check"; then STRUCK BY ABSORPTION 2026-08-26, direction ZJACOB — it
**is** (ZH-4)'s hypothesis, so the two "concrete" candidates were one.**
*(Header aligned with §9.3 by the 2026-09-03 liveness sweep; mechanism and
original pitch below unchanged. Kill condition: the bound reaches the target
only at `c = 0`, where it **is** `HasGenericPencilRealization` — **FIRED**.
Deciding surfaces: §(K-shear) *Secondary deliverable*, §(K-jac); no gap-map
row.)* It does survive §2.5 (a codimension is geometric, and it does
separate seeds at a fixed graph), but the filter is not the binding objection:
on the tight class `m = 5|E| = target`, so `rank ≥ m − c` reaches the target
only at `c = 0`, where the statement reads *the pencil chart's generic
self-stress dimension is 0* — which **is** `HasGenericPencilRealization`
(`Motive.lean:140`, coordinator-verified against the body). Its content is
expected-codimension transversality **relative to the pencil chart**, i.e.
§2.4's wall; at `c ≥ 1` it yields `target − 1`, the shortfall already recorded
at §(K-flank) *Step F5(d)*. Detail: §(K-shear)'s *Secondary deliverable*. The
source's
Theorem 1.2, read contrapositively: a stratum of codimension `c` has generic
self-stress dimension `≤ c`, hence **rank `≥ m − c`** — a rank lower bound
derived from nothing but the codimension of the stratum. The arc has no tool of
this type; every rank lower bound in it comes from an explicit witness or from a
bracket-monomial closed form (§(K-pitch) *Step 5*).

*Why it is not free.* The source's theorem is for `(2,2)`-sparse **bar–joint**
graphs; this phase's carrier is body–hinge at multiplicity 5. **No theorem
transfers.** What transfers is a target to seek: a *"stress degeneracy costs
codimension"* theorem for the body–hinge carrier, whose sparsity class would be
the Tay packing class rather than `(2,2)`. Whether that is tractable is a real
open question, and §2.5's filter is owed here too.

**(ZH-4) Escape failure as a singular locus — the Jacobian route. — STRUCK
2026-08-26, direction ZJACOB: REFUTED, and by an EQUIVALENCE rather than an
obstruction.** Canonical home `notes/Pencil-informal.md` §(K-jac) *Steps
JC1–JC5* — not restated here. *(Kill condition: the Jacobian criterion's
hypothesis unfolds to the phase target — **FIRED**. Deciding surface:
§(K-jac), driver `notes/scripts/w4/zjacob.py`; **no gap-map row**. Struck, not
deleted: the original pitch stands below.)* In one line: stratifying by corank gives
`dim 𝒞 = max_{k≥0}(dim B_k + 6 + k)`, so *"local complete intersection of the
expected codimension"* ⟺ `B_0 ≠ ∅` **and** `codim B_k ≥ k` (∀`k ≥ 1`) — and
`B_0 ≠ ∅` **IS** properness, which on the tight class is the phase target. **The
route's hypothesis contains its conclusion as its weakest clause**, so the
Jacobian criterion unfolds with no computation in between to *"the rank attains
target generically"*. Two independent corroborations: every classical bound on
heights of ideals of minors is an **upper** bound taking the generic rank as
**input**, and on our shapes evaluates to the graph-independent constant `7`
(so §4.6's filter fires too); and the criterion is **identically blind** to the
pure-condition half (every partial of a fibre-quadratic vanishes on the zero
section, 84/84). **The corollary that matters for this shelf: (ZH-4)'s
hypothesis IS (ZH-3)** — the two "concrete" candidates were one candidate, and
(ZH-3)'s *circular as posed* transfers verbatim. Granting the source's
Theorem 4.2 in full changes nothing: a carrier analogue would **be** the phase
target. The reading below is preserved as the shelf's original pitch. The
source's
Theorem 4.2 is a scheme-theoretic upgrade of exactly the White–Whiteley
pure-condition material §(K-pure) works by hand: degeneracy loci as
determinantal subschemes of a two-term complex, the universal
infinitesimal-motion cone a local complete intersection of the expected
codimension (hence Cohen–Macaulay and equidimensional), and — the usable part —
the identification of the first degeneracy locus with the **singular locus of
that cone along its zero section**, via the Jacobian criterion.

*What it would buy.* If the escape-failure locus can be presented as such a
singular locus, then *"escape fails only on a proper closed subset"* becomes
*"the cone is generically smooth along its zero section"* — a Jacobian-rank
computation rather than a witness hunt. §(K-pure)'s chord obstruction and
isotropic completions (**(PC1)**–**(PC3)**, **(PC-Z)**) are already local
computations at a limit carrier, so this looks like a repackaging with real
leverage and no filter problem on its face. The more concrete of
(ZH-2)/(ZH-4).

**(ZH-5) The collinearity-flag pattern, as a design template.** The source's §3
solves a problem structurally identical to one this phase has — *an induction in
which one exceptional geometric degeneracy must survive every recursive step* —
with a four-part template worth stealing whole: **(a)** decorate rather than
discard (the degeneracy becomes a combinatorial object: support triple,
distinguished missing edge, auxiliary vertex); **(b)** test consistency by
requiring the *simultaneous* completion of all decorations to stay in the
sparsity class, one combinatorial check standing in for a system of geometric
conditions; **(c)** prove the **incidence graph of the decorations is a forest**,
which is what makes codimensions *add* rather than merely bound; **(d)** match
the ledgers — combinatorial cost of a decoration equals its geometric
codimension (both 2, in every dimension), which is why the accounting closes.

Part **(c)** is the one to emphasize. The arc has repeatedly hit *"the conditions
might not be independent"* walls — §(K-slide-comb)'s class-wide refutation, its
starvation bound, its matroid-intersection menu. A forest structure theorem on
the **incidence of degeneracies**, rather than on the degeneracies themselves, is
a move the arc has not made.

*Adjacency, 2026-09-03 — recorded as adjacency, **not** as delivery.*
§(K-bare-ext) directions **BRNODE** and **BDECOR** independently instantiate
part **(a)** and something close to part **(c)**: decorated skeletons, and a
per-branch **product** law for the achievable decorations of a piece (*"at a
fixed flag assignment on the hub set the legal configurations of ANY piece are
a product, one factor per topological branch"*). They were reached
independently, not imported, and **whether that is this template's part (c) — a
forest structure theorem on the *incidence* of decorations — is NOT verified.**
*Kill condition: the arc makes the incidence-forest move, or the template is
shown not to transfer to the body–hinge carrier. Row: gap-map
**(K-bare)/(K-bare-ext)**.* Still a design note, never a dispatch — a priority
call re-openable on merit, not a bar.

**(ZH-6) Orientation, not a route — why our counting works and theirs does not.**
The source's partition condition and this phase's `def(H)` are the same template
with different capacity functions. Body–hinge: `Σ 5·d(P_i,P_j) ≥ 6(t−1)`,
capacity `5m`, **additive**. Body–pin: `Σ ℓ(d(P_i,P_j)) ≥ 6(t−1)` with
`ℓ ∈ {0,3,5,6}`, capacity `2m+1` **saturating** at 6. The additivity is exactly
what puts body–hinge in matroid-union land — Nash-Williams/Tutte's
`k·d(P) ≥ r(|P|−1)` ⟺ `kH` packs `r` trees, which is Tay's theorem and this
phase's `def(H) = 0` criterion. A saturating capacity is not the rank function of
any union of graphic matroids on the multigraph, which is why the source must
first collapse to a simple support graph and only then use two copies. Useful
when the phase writes up why its own counting is available; **not a direction.**
*(Kill condition, 2026-09-03: none — this entry is never dispatchable by
construction; it retires when the phase writes up its own counting. Deciding
surface: none needed.)*

*(The saturation also explains the source's `2`: its needed equation count is
bounded by `2(t−1)`, exactly the `(2,2)`-tight bound on `t` vertices. Recorded
for orientation; nothing in the arc turns on it.)*

### 9.3 Suggested order, if a direction is ever spent here

**The shelf is TWO-FOR-TWO and has exactly ONE dispatchable candidate left**
(2026-08-26; table rebuilt 2026-09-03 by the liveness sweep). *This subsection
was self-contradicting for a week and is the round's cleanest specimen of the
`RESEARCH-ARC.md` §8 failure mode: the second update prepended a correct header
and left the first update's ranking standing underneath, so the paragraph named
**(ZH-4)** as the head of the order — an entry its own §9.2 marks STRUCK four
paragraphs earlier — and closed "one-for-one" against its own opening
"two-for-two". A coordinator reading top-down for a dispatch read "the head is
(ZH-4)". The ranking prose is replaced by this table; nothing is deleted, and
every strike keeps its cause, its date and its preserved original pitch in
§9.2.*

| entry | status | direction / date | canonical home |
|---|---|---|---|
| **(ZH-1)** | **STRUCK** — the Witt shear is a *gauge* transformation, so the mechanism is vacuous | ZSHEAR, 2026-08-26 | §(K-shear) *SH1–SH5*; `notes/scripts/w4/zshear.py` |
| **(ZH-2)** | **LIVE, stratified reading only** — the shelf's whole dispatchable content | filter check DONE 2026-08-26 | §(K-shear) *Secondary deliverable* |
| **(ZH-3)** | **STRUCK BY ABSORPTION** — circular as posed, and it **is** (ZH-4)'s hypothesis | ZSHEAR then ZJACOB, 2026-08-26 | §(K-shear); §(K-jac) |
| **(ZH-4)** | **STRUCK** — refuted by an *equivalence*: its hypothesis contains its conclusion | ZJACOB, 2026-08-26 | §(K-jac) *JC1–JC5*; `notes/scripts/w4/zjacob.py` |
| **(ZH-5)** | design note feeding a fan-out's *selection* — **never a dispatch** | unopened | — |
| **(ZH-6)** | write-up material — **never a dispatch** | unopened | — |

**So the order is: (ZH-2), in its stratified reading only, and nothing else.**
**(ZH-5)** is consulted when a fan-out selects directions; **(ZH-6)** when the
phase writes up why its own counting is available. Two directions spent
(ZSHEAR, ZJACOB), two candidates struck, one re-explained, and the owed §2.5
filter checks are **DONE**.

Before (ZH-2) is dispatched it owes one further check, recorded in its own
entry and **never run**: `∆` is carried along reduction steps, and §(K-ind)
proves no move of `pencil_reduction` relates two class members. That is not a
kill — a potential-function induction may legitimately descend out of the class
— but a dispatch spec must say which. *Row: gap-map **(K-ind)**.*

**The shelf stays UNPRICED — off §8's board — and that is a priority call, not
a prohibition** (2026-09-03 user ruling): re-opening any entry here needs a
**mathematical reason, not permission**. The unrefereed / AI-assisted /
never-independently-checked caveat at the head of §9 is a different kind of
statement — evidential, about the source — and is untouched by that ruling.

*Kill condition for this subsection: a third direction is spent here, or
(ZH-2) is struck — after which the shelf carries **no** dispatchable candidate
and should be marked **closed** rather than re-ranked. Deciding surface: §9.2's
own entry banners. **The shelf has no gap-map row**, which is exactly why
nothing but a liveness sweep can detect that this table has gone stale.*
