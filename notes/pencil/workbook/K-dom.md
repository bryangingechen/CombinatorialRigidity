## §(K-dom) — the dominance spike: the differential of `H ↦ V_bc`, why C1 is not an inductive route, and (2026-09-03) C2's satisfiability trace (**dominance HOLDS at every class habitat probed; C1's two claimed values REFUTED; C2 UNSAT as a *uniform* carry — proved off the class, measured quiet on it — and NOT shown dead as a class-only conjunct; class uniformity untouched**)

Answering `notes/pencil/strategy.md` §4-C1, the one candidate on that doc's
list nothing in the arc had run: *compute the Jacobian of the `V_bc` map with
respect to the far-realization parameters and measure its rank against
`dim Gr(3,6) = 9`.* Read against §(K-pitch) *Steps 1, 5b* (path-sum
containment and (T5)) and §(K-pure) *Step P3* ((PC-Z)), whose notation it
inherits verbatim. The strategy doc's §§2–4 are flagged there as
coordinator-authored synthesis carrying no driver; this section is the driver.

**Headline, stated up front.**

- **The rank is 9 — dominance holds — at every class habitat probed** (5 of
  them, companion lengths 4, 5, 6), so at each of those shapes the escape holds
  on a *dense open* subset of the chart. That is a genuine positive, and a new
  proof route.
- **But there is a structural cap, and it is sharp**: `rank dV ≤ min(9, 6k−14)`
  where `k` is the companion length (**(D1)**), so at `k = 3` the rank is at
  most **4**, measured to be exactly 4. `k = 3` habitats are exactly the ones
  whose split chain plus companion is a rigid `C₆`, i.e. **(K-res)** residuals —
  which `hK` carries as a byte-identical sibling.
- **Both of §4-C1's claimed values are refuted.** The far graph contributes at
  most `3(k−3)` to the rank (**(D2)**, a corollary of (T5), *attained* at every
  probed habitat and **0** at `k = 3`), so "as the far graph grows the image can
  only grow" is false: the image dimension is pinned by a purely **local**
  invariant. And the 2026-07-30 locality refutation was gated at `k = 6`, the
  *maximal* far-dependence grade, so it is not evidence for dominance in general
  — at `k = 3` the same quantity is `0` and, by (T1), the escape there is a
  **local** condition.
- **Class uniformity is untouched.** "Rank 9 at every class shape" is one
  determinantal condition per (shape, split) — the same per-shape object
  §(K-pure) *P5* identified as the wall. C1 relocates the wall; it does not
  cross it.
- **And §4-**C2** dies here too, for the same reason as C1** (2026-09-03,
  direction DSAT, *Steps D8–D14*): C2's own prescribed satisfiability trace
  returns **SAT on the class, UNSAT on (K-res)**, off an exact identity
  `dim V_bc = dim mot(G − a) − dim mot(G)` at every degree-2 index. The
  (K-res) half is **proved**, the class half **measured at five shapes** — so
  C2 is dead as a **uniform** carry and *not* shown dead as a class-only
  conjunct. `(K-dom)`'s clause *"nothing in `(K-dom)` bears on C2"* is refuted
  by its own section.

### Standing notation (on top of §(K-pitch))

Split chain `b–v–a–c` at a target-rank `G′`-seed with `b`, `c` hubs;
`H := G − v − a`; `V_bc` the relative twist system, `dim V_bc = 3`;
`T := ⟨C_ab, C_ac⟩`; `α(a)`, `Λ²π̂` the two maximal isotropic 3-spaces of
(PC-Z). The **companion length** `k` is the length of the *shortest* `b`–`c`
path of `H`; `k ≥ 3` always, since `dim V_bc = 3` needs `dim span{C_e : e ∈ P}
≥ 3`. Write `S_P := span{C_e : e ∈ P}`.

`Gr(3,6)` is `dim 9`, and at `V ∈ Gr(3,6)` its tangent space is
`Hom(V, K⁶/V)`, of dimension `3·3 = 9`. **The differential measured here is
the map (chart tangent) → `Hom(V_bc, K⁶/V_bc)`**, not the rank of a raw
coordinate Jacobian.

### Step D0 — the question, and what has to be held fixed

By (PC-Z) the escape fails exactly when `V_bc` meets `α(a)` or `Λ²π̂`; each is
the Schubert condition `σ₁` on `Gr(3,6)`, of **codimension 1**. So if the map
`H ↦ V_bc` were **dominant** — image dense in `Gr(3,6)` — a generic realization
would miss the bad locus and the escape would follow for generic reasons.

`α(a)` depends only on `pt(a)`; `Λ²π̂` only on `π̂ = plane(a,b,c)`, i.e. on
`pt(a), pt(b), pt(c)`. **Neither is far data.** So the well-posed dominance
question varies the chart with the bad locus *standing still*:

> **the FIXED scoping** — `pt(a)`, `pt(b)`, `pt(c)` and the two panels `Π(b)`,
> `Π(c)` frozen (`pt(a) ∈ M = Π(b) ∩ Π(c)` is then frozen consistently), every
> other chart coordinate free.

This resolves the `b`/`c` coupling the question carries (`b` and `c` are `a`'s
`G′`-neighbours, so `a`'s data constrains `H`'s realization at `b` and `c`): we
freeze *all* of it rather than trying to propagate it. Freezing more can only
lower the rank, so a rank of 9 in this scoping is a conservative positive.

Two further scopings are computed as **diagnostics only**: FREE (nothing
frozen — the bad locus co-moves, so a rank there bounds nothing about the
escape) and UNPINNED (the panel constraints dropped, `a,b,c` still frozen —
which isolates whether a rank deficiency is caused by the *pencil pin* or by
something pin-free).

Two scoping disciplines are load-bearing and were honoured: the differential is
taken along the **pencil-stratum chart** (the tangent space is the kernel of the
differentiated pencil condition `⟨n_u, pt(w) − pt(u)⟩ = 0` over every hub `u`
and `G′`-neighbour `w`), never along unconstrained point coordinates — the pin
removing freedom is the entire phenomenon under study; and no chart direction
is allowed to move `pt(a)`, `pt(b)` or `pt(c)` (asserted in the driver).

### Step D1 — (D1): the a-priori cap, `rank dV ≤ min(9, 6k − 14)`

This is settled **before** any numerics, because a structural cap and a
measured deficiency must agree.

> **(D1)** *(proven-informally)* In the FIXED scoping,
> `rank dV ≤ min(9, (3k − 5) + 3(k − 3)) = min(9, 6k − 14)`.
> In particular `rank dV ≤ 4` at every `k = 3` habitat, and `(D1)` is vacuous
> for `k ≥ 4`.

*Proof.* Fix a shortest `b`–`c` path `P = b x₁ … x_{k−1} c` of `H`. Path-sum
containment (§(K-pitch) *Step 1a*) gives `V_bc ⊆ S_P`, so `V_bc` is determined
by the pair (`S_P`, the annihilator of `V_bc` in `S_P*`). Two counts:

1. `S_P` is a function of `pt(x₁), …, pt(x_{k−1})` alone. In the FIXED scoping
   `x₁` is a neighbour of the hub `b`, so `pt(x₁) ∈ Π(b)`, a *frozen* plane —
   2 parameters; dually `pt(x_{k−1}) ∈ Π(c)` — 2; the `k − 3` middle interiors
   contribute `3` each. Total `3k − 5`. (If an `x_i` carries a further hub
   incidence it has *fewer* parameters, never more.)
2. `dim S_P = k` for `k ≤ 6` at a nondegenerate seed, and the annihilator of
   the hyperplane-or-deeper `V_bc ⊆ S_P` is a point of `Gr(k − 3, k)`, of
   dimension `3(k − 3)`.

The image of the chart therefore has dimension `≤ (3k − 5) + 3(k − 3)`, and the
rank of the differential is bounded by the image dimension. At `k = 3` the
containment is an **equality of 3-spaces** — `V_bc = S_P = ⟨C₁, C₂, C₃⟩`, the
§(K-pitch) *Step 5* configuration — the annihilator term is `0`, and the whole
map factors through `(pt x₁, pt x₂) ∈ Π(b) × Π(c)`: 4 parameters. ∎

**A basis-free corollary, independent of the freezing.** At `k = 3` the Gram of
`B` on `(C₁, C₂, C₃)` has a single nonzero entry `B(C₁,C₃) = [b,x₁,x₂,c]` (the
serial-chain signature, §(K-pitch) *Step 5*), so `rank B|_{V_bc} = 2` and

> `V_bc` always lies in the **discriminant hypersurface** `{det Gram_B = 0}` of
> `Gr(3,6)` — an 8-dimensional subvariety — so dominance is impossible at
> `k = 3` for a reason that no choice of frozen data can repair.

*Exact:* `--cap` asserts `rank Q|_{V_bc} = 2` at `k = 3` and `= 3` at `k ≥ 4`,
at 21 seeds over 7 habitats, together with `V_bc ⊆ S_P` at **every** `b`–`c`
path (not only the shortest).

### Step D2 — (D2): the far block is `3(k − 3)`, and it is attained

The strategy doc's inductive hope is about the *far* parameters specifically,
so they get their own bound. (T5) (§(K-pitch) *Step 5b*) already says the shape
of the answer: at a length-`k` companion **all far-graph dependence enters
through the annihilator `Λ` of `V_bc` in `S_P*`**. Counting that annihilator:

> **(D2)** *(proven-informally; a corollary of (T5) + (D1)'s count 2)*
> Restricted to chart directions that move only vertices **off** a shortest
> companion, `rank dV ≤ 3(k − 3)`. In particular the far block is
> `0` at `k = 3`, `3` at `k = 4`, `6` at `k = 5`, `9` at `k = 6`.

*Exact:* `--far` measures the far block at 14 seeds over the 7 habitats; the
per-habitat maximum is `0, 0, 3, 3, 6, 9, 9` in the table order of *Step D4* —
**the bound, attained at every habitat**. At the two `k = 3` habitats that means
all 13 resp. 41 far directions lie in `ker dV`.

Two consequences worth stating separately.

- **The far graph does not enlarge the image once `k` is fixed.** Beyond
  `3(k−3)` directions, every additional far parameter is in the kernel. At
  `k = 3` there is no budget at all: `V_bc` is *constant* along the entire far
  chart.
- **Locality is graded by `k`.** At `k = 3`, (T1) makes `⟨r⟩ = (V_bc ⊕ T)^⊥`
  with both summands functions of the six points `{b, x₁, x₂, c, a}` and
  `pt(a)`, so the escape criterion is a **local** condition there. The
  2026-07-30 route-1 locality gate (design doc §"(K) route-1 gate";
  `escape/localtest.py`) was run on the double subdivisions of `K4` and
  `K5 − M`, both `k = 6` — the *maximal* grade. Its refutation of locality is
  therefore consistent with (D2), and (D2) explains it: far-dependence rises
  from nothing to everything as `k` runs 3 → 6.

### Step D3 — `hnoRigid` forces `k ≥ 4`, so (D1) bites exactly on (K-res)

The split chain (3 edges) and a shortest companion (`k` edges) are internally
disjoint, so their union is a cycle `C_{3+k}` of `G`, and it is *proper*
(`b`, `c` are hubs, so `G` has more edges). By R3 (`def(C_j) = max(0, j − 6)`)
that cycle is **rigid iff `3 + k ≤ 6`, i.e. iff `k = 3`**. Hence:

> **(D3)** *(proven; it is §(K-slide) *Step 5*'s `ℓ₁ + ℓ₂ ≥ 7` in this
> notation)* A tight `hnoRigid` habitat has `k ≥ 4`. Equivalently, every
> `k = 3` habitat is a **(K-res)** residual, not a member of the pinned-`hK`
> class.

*Exact:* `--cap` asserts the `C_{3+k}` dichotomy at all 21 seeds and
cross-checks it against `kslide.no_rigid_branch_union` (the exhaustive
branch-union sweep) — the two certificates agree at every habitat.

So (D1) is **vacuous on the pinned `hK` class** and bites exactly on the
(K-res) half that `hK` also carries since the 2026-08-02 route-3(b)
adjudication. That is the honest scope of the negative: it does not touch the
class, and it does block C1 from covering everything `hK` must cover.

### Step D4 — the measurement

`--jac`, 7 habitats × 3 valid seeds × 3 scopings. Rank is lower semicontinuous,
so the **maximum over seeds** is a lower bound for the generic rank, and (D1) is
the upper bound; where the two meet the generic rank is *determined*.

| habitat | `k` | status | FIXED | FREE | UNPINNED | (D1) cap |
|---|---|---|---|---|---|---|
| θ(3,3,6) | 3 | (K-res) | **4** | 8 | 6 | 4 |
| NT21c3 | 3 | (K-res) | **4** | 8 | 6 | 4 |
| θ(3,4,5) | 4 | class | **9** | 9 | 9 | 9 |
| NT21 | 4 | class | **9** | 9 | 9 | 9 |
| NT16k5 | 5 | class | **9** | 9 | 9 | 9 |
| `K4` dbl-subdiv | 6 | class | **9** | 9 | 9 | 9 |
| `K5−M` dbl-subdiv | 6 | class | **9** | 9 | 9 | 9 |

Readings:

- **`k = 3`: rank exactly 4**, i.e. (D1) is *sharp*, at both habitats and every
  seed. Dropping the pencil pin (UNPINNED) raises it only to **6** = the
  `2 × 3` parameters of the two companion interiors freed of their panels, so
  **the deficiency is path-sum containment, not the pin**: C1 would fail at
  these shapes in KT's unpinned world too.
- **`k ≥ 4`: rank 9 at every habitat**, at 1–3 of the 3 seeds each (a seed
  giving 8 is a non-generic point of an irreducible chart, which
  semicontinuity handles). The map is **dominant** at θ(3,4,5) — the
  §(K-Λ)/(K-wit) exemplar — at two non-theta class shapes and at both control
  double subdivisions.
- The escape itself holds at **all 21** seeds (`V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0`,
  asserted), *including* the rank-capped `k = 3` ones. So dominance is
  **sufficient and very far from necessary** for the escape.

### Step D5 — what dominance buys at a shape, exactly

> **Proposition (D4).** Let a (shape, split) have a rational FIXED-scoping seed
> at which `rank dV = 9`. Then on a dense open subset of that shape's pencil
> chart the seed is target-rank, nondegenerate, and satisfies
> `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0` — hence, by (PC-Z) and (T2)/(T3), `Q(r) ≠ 0`
> and the escape holds on **both** KT routes.

*Proof.* The chart with `pt(a), pt(b), pt(c), Π(b), Π(c)` frozen is an
irreducible tower of affine-linear fibres (§(K-slide) *Step 1(e)*, with the
first stages frozen). Rank is lower semicontinuous, so `rank dV = 9` at one
point makes the generic rank `9 = dim Gr(3,6)`; in characteristic `0` that is
dominance, so the preimage of the codimension-1 bad locus is a proper closed
subset. The remaining requirements (target rank, `dim V_bc = 3`, the (T2) side
conditions) are open and nonempty at the witness seed. A finite intersection of
dense opens in an irreducible variety is dense open. ∎

**Calibrate this honestly.** §4-C1's own caveat — "dominance *at one habitat* is
per-shape again" — is correct, and the driver's numbers do not weaken it. What
(D4) adds over §(K-flank)'s per-shape `∃`-witnesses is that it certifies a
*dense open* set of good seeds rather than one, and does so **uniformly in the
bad locus**: the same rank-9 statement kills *every* codimension-1 obstruction
at that shape, not just the two of (PC-Z). It is a strictly stronger per-shape
statement. It is not a more *useful* one for `hK` as pinned, because one
`Q(r) ≠ 0` witness plus chart irreducibility already gives the escape at a
generic seed — which §(K-flank) has at 16/16 probed splits.

### Step D6 — assessment of §4-C1's two claimed values

The strategy doc gives two reasons to prefer dominance over a pointwise
condition. Both fail, and (D2) is why.

**Claim (i) — "it is inductive in the right direction: as the far graph grows by
a generating move, parameters are *added*, so the image can only grow."
REFUTED.** By (D2) the far parameters' contribution is capped at `3(k−3)`, a
function of the *local* companion length only. Once that budget is saturated —
and `--far` shows it is saturated at every habitat probed — every further far
parameter lies in `ker dV`, so growing the far graph does not enlarge the image.
At `k = 3` the budget is `0`: the image is a fixed 4-fold no matter how large
the far graph is. What would actually have to be carried inductively is `k ≥ 4`,
and by (D3) that is *exactly* `hnoRigid` — already an antecedent of `hK`. The
inductive content C1 hoped to gain is therefore already in the hypothesis, and
C1 adds nothing to it.

**Claim (ii) — "it reframes route 1's refutation as an asset: the escape's zero
locus moves with the far graph, so the map is highly non-constant." REFUTED as
an inference.** The route-1 gate measured the *stress*-side zero locus at
`k = 6` habitats (`escape/localtest.py`, double subdivisions of `K4` and
`K5 − M`), which by (D2) is the maximal far-dependence grade. The same
measurement at `k = 3` would return the opposite verdict: far-dependence `0`,
and by (T1) a fully local escape criterion. So "the map is highly non-constant"
is not a property of the class — it is a property of high `k`, and the correct
statement is the **grading** (D2), not a global non-constancy.

**And the wall is not crossed.** Suppose one wanted the uniform statement
"`rank dV = 9` at every class (shape, split)". That is the non-vanishing of a
`9 × 9` minor of a matrix built from one shape's chart — **one determinantal
condition per (shape, split)**, with no subset-indexed family, no exchange, no
matroid: precisely the ingredient-2 failure §(K-pure) *P5* isolates. C1
*relocates* the crux from `Q(z) ≢ 0` to `rank dV = 9` — a strictly stronger and
equally per-shape condition. It is not a route to class uniformity.

### Step D7 — what this leaves, honestly

- **(K-dom)**, the uniform form — "`rank dV = 9` at every class (shape,
  split)" — is **open**, verified at 5 class habitats spanning `k ∈ {4,5,6}`,
  and provably **false** on the (K-res) `k = 3` family. Because a
  counterexample on the class would be a shape whose entire chart maps into a
  proper subvariety of `Gr(3,6)`, and none is known, the statement is plausible
  — but it is not a *weaker* target than `hK`, so closing it is not progress
  unless a mechanism appears.
- The `k = 3` family is not a loss: it is exactly where §(K-pitch) *Step 5*'s
  bracket monomial **closes** the pitch (θ(3,3,6)). So the two mechanisms are
  complementary — a **companion-length dichotomy** (`k = 3` by the monomial,
  `k ≥ 4` by dominance) covers every habitat probed. Whether that dichotomy can
  be made uniform is exactly the open (K-dom) plus the already-open `k ≥ 4`
  side; the dichotomy is an *organizing* observation, not a proof.
- Not probed: `k = 4, 5, 6` habitats with a **parallel `G°` edge** (`P21`-type),
  where §(K-pure) *P4* locates a separate obstruction; and whether any class
  shape has `rank dV < 9`.

### Step D8 — the C2 satisfiability trace: the consumer's object, and three readings

`notes/pencil/strategy.md` §8.2 carried **C2** — *carry `V_bc` general position
as a motive conjunct* — as **live and unpriced** while naming its own
prerequisite: *"a stronger motive can be **unsatisfiable** — needs a
satisfiability trace first (the L6b/F10 precedent)."* *Steps D8–D14* run that
trace (2026-09-03, direction DSAT). Everything below is read against the
**landed Lean**, not against §4-C2's prose.

**What the consumer hands the motive.** `pencilPair_of_splitOff_of_habitat`
(`Molecule/Pencil/Escape.lean:334`) is the split arm's producer. In its
**feasible** branch (`:396`, `by_cases hfeas`) it takes
`HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` from the induction
hypothesis (`:400`) and feeds it to `hK` (`:419`). So the conjunct would have to
hold of a pencil realization of the **split-off graph**
`G′ := G.splitOff v a b e₀`, and `V_bc` there is the relative twist system of
`H := G′ − a` — (T1), §(K-pitch) *Step 1*. Two consequences fix the question's
shape:

- `V_bc` is an object of a **vertex-deleted subgraph of the motive's own
  object**, which is §4-C2's first stated problem, now located exactly.
- `G′` does not know which of its vertices was the split partner `a`, so a
  **carried** conjunct must quantify over an index set of its own — and
  `Graph.pencil_reduction` (`Induction/ForestSurgery/Reduction.lean:850`)
  concludes `∀ G, V(G).Nonempty → P G`, so the motive gets **no habitat
  hypothesis** and the index set cannot be narrowed by fiat. Pinning it is
  *Step D9*.

**Three readings of "general position", which are not equivalent.** **ESC** —
`V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0`, exactly (PC-Z) (§(K-pure) *Step P3*), the
condition `hK` consumes; decided by *Steps D11–D12*. **GEN** — `V_bc` a
*general* point of `Gr(3,6)`, needing in particular `det Gram_B(V_bc) ≠ 0`,
i.e. `rank Q|_{V_bc} = 3`; decided by *Step D13*. **IDX** — the index set;
decided by *Step D9*. A trace that silently picks one reading and reports for
all three is the defect these steps exist to avoid, so the three get separate
driver modes and separate verdicts.

### Step D9 — (DM-5): the index set is forced to the degree-2 triples

> **(DM-5)** *(structural half proven; measured half enumerated)* The C2
> conjunct is well-posed only at indices `(a, b, c)` with `deg_G(a) = 2`,
> `N_G(a) = {b, c}`. Its index set is therefore the **adjacent edge pairs** of
> `G`, derived from `E(G)`, so the **growing-ground-set filter** (strategy §4.6)
> is **passed**. The *unrestricted* form — every `a`, every neighbour pair — is
> **unsatisfiable at every habitat probed**.

*Structural half.* (T1)'s two-port derivation uses `deg_{G′}(a) = 2` in **both**
directions: the stress restriction has exactly two deleted fibres (`b` receives
`−r`, `c` receives `+r`), and the converse extends an `H`-motion by
`m(a) := m(b) − ω₁C_ab = m(c) + ω₂C_ac`, which at a third neighbour `d` would
also have to satisfy `m(a) − m(d) ∈ ⟨C_ad⟩` and does not. The measured
consequence, asserted per triple: `dim mot(H/bc) > dim mot(G′)` at **180 of
180** `deg(a) ≥ 3` triples, so (DM-6)'s identity below **does not reach degree
`≥ 3` at all**. ∎

*Measured half.* At `deg(a) ≥ 3`, `dim V_bc ≥ 4` at **172 of 180** triples, and
`4 + 3 > 6` then forces `dim(V_bc ∩ S) ≥ 1` for both 3-dimensional isotropic
spaces — **0 exceptions** to that Grassmann implication, and every
(habitat, seed) carries at least one such triple (asserted). So the
unrestricted conjunct is false at every realization drawn, at every habitat.

**A negative worth recording, because the driver first got it wrong.** The
discriminator is **not** `dim T`. `T = span{C_ax : x ∈ N(a)}` is
**2-dimensional at every body of a pencil realization whatever its degree** —
concurrency at `pt(a)` plus coplanarity in the panel *is* the pencil pin —
asserted at all **350** triples of the census, `deg(a)` = 2, 3 and 4 alike. So
**the local hinge data is blind to the two-hinge hypothesis**: the restriction
cannot be read off `T`, and a first attempt to assert it that way failed at
θ(3,3,6)'s degree-3 hub. The restriction has to be carried as an explicit
`deg = 2` guard rather than discovered from the geometry.

### Step D10 — (DM-6): `dim V_bc` is a rigidity count, exactly

> **(DM-6)** *(proven)* Let `(F, normal, point)` be a pencil realization of `G`
> at the rank target (so `dim mot(G) = 6 + def₃(G)`), and let `a` be a
> **degree-2** vertex with `N_G(a) = {b, c}`, `H := G − a`. Then
> `dim V_bc = dim mot(G − a) − dim mot(G) ≥ def₃(G − a) − def₃(G)`. In
> particular at an infinitesimally rigid `G` (`def₃(G) = 0` at the target rank)
> `dim V_bc = dim mot(G − a) − 6`.

*Proof.* Three steps, none numerical.

1. **Definitional.** `V_bc` is the image of `mot(H)` under `m ↦ m(b) − m(c)`,
   whose kernel is `{m ∈ mot(H) : m(b) = m(c)} = mot(H/bc)`, the motion space
   of `H` with `b` and `c` welded into one body. So
   `dim V_bc = dim mot(H) − dim mot(H/bc)`.
2. **The welded space is `G`'s own motion space.** Given `m ∈ mot(H/bc)`, set
   `m(a) := m(b) = m(c)`. Both hinge conditions at `a` read
   `m(a) − m(b) = 0 ∈ ⟨C_ab⟩` and `m(a) − m(c) = 0 ∈ ⟨C_ac⟩`, and `a` has no
   other neighbour, so the extension is a motion of `G`; it is injective
   (inverse to restriction). Hence `dim mot(H/bc) ≤ dim mot(G)`, and
   `dim mot(H/bc) ≥ 6` always, so at a rigid `G` the two coincide. **This is the
   one place `deg(a) = 2` is indispensable** — at a third neighbour the
   extension is not a motion, which is (DM-5)'s structural half.
3. **Deficiency floors the flex count at every realization.**
   `def₃(H) = 6(|V(H)|−1) − rank_{(6,6)}(5H)` and `rank R(H)` is maximised
   generically, so `dim mot(H) = 6|V(H)| − rank R(H) ≥ 6 + def₃(H)` — **no
   genericity hypothesis anywhere**. ∎

*Exact:* `--gate` asserts the identity at **255 of 255** degree-2 triples over
7 habitats × 3 seeds — **0 violations** — with `dim mot(H/bc)` computed
**directly** each time (six welding rows appended to `R(H)`, an independent
nullspace), so step 2's extension argument is *tested*, never assumed. It also
asserts `dim mot(G′) = 6 + def₃(G′)` at every seed (the rank-target hypothesis)
and `dim mot(H) ≥ 6 + def₃(H)` at every triple.

**Corollary, and the reason (DM-6) earns a label.** `dim V_bc` — the whole
subject of §2.4's image problem, of C1 and of C2 — is at every degree-2 index a
**rigidity count of `G − a`**, and generically a purely combinatorial one:
`--validate` check (7) finds `dim V_bc = def₃(H) − def₃(H/bc)` at **85 of 85**
triples, 0 disagreements.

### Step D11 — (DM-7)/(DM-8): the UNSAT gate, and the stratum it fires on

> **(DM-7)** *(proven)* If `def₃(G − a) − def₃(G) ≥ 4` at a degree-2 vertex `a`,
> then at **every** pencil realization of `G` at the rank target
> `V_bc ∩ α(a) ≠ 0` **and** `V_bc ∩ Λ²π̂ ≠ 0`. The C2 conjunct at `a` is
> **unsatisfiable** — UNSAT *proved*, off a combinatorial trigger, not a failed
> search.

*Proof.* (DM-6) gives `dim V_bc ≥ 4`. Both `α(a)` and `Λ²π̂` are 3-dimensional
— the second by the **fourth landed conjunct** at the non-hub `a`, which is
exactly `rank[pt a, pt b, pt c] = 3` (*Step D14*) — so
`dim(V_bc ∩ S) ≥ 4 + 3 − 6 = 1 > 0` for each. By (PC-Z) the escape fails, and
ESC failing makes GEN fail a fortiori. ∎

> **(DM-8)** *(measured, exhaustive per habitat, over a 7-shape family)* The
> gate fires at **54 of 255** degree-2 indices, and the split is **exactly class
> vs (K-res)**: at **both** (K-res) habitats it fires (θ(3,3,6) 5 of 8, at
> `a ∈ {16,…,20}`; NT21c3 13 of 16, at `a ∈ {104,…,116}`), and at **all five**
> class habitats it fires at **none** (0 of 8, 16, 11, 11, 15). Census of
> `def₃(G′−a) − def₃(G′)` over the 255: **3 at 201 indices, 4 at 54**, nothing
> else.

**The two halves of the kill have different evidential status, and the
distinction is load-bearing.** The **(K-res) half is PROVED**: (DM-7) is an
argument with a combinatorial trigger, and the 18 firing indices per seed are
exhibited. The **class half is MEASURED at five shapes** — 0 firings at 62
degree-2 indices is a *shape-family cap*, not a theorem, and the shape family
is precisely the axis this trace did not vary. Two readings follow, and only
the first is a result:

- **The uniform conjunct is UNSAT at objects the consumer hands the motive.**
  `hK` carries the (K-res) residual (the 2026-08-02 route-3(b) adjudication), so
  a conjunct required at every index of every object the reduction reaches is
  refuted at θ(3,3,6) and NT21c3 outright. **This is C2's own kill condition,
  and it fires.**
- **C2 is NOT shown dead as a class-only conjunct.** Nothing above touches
  *"carry `V_bc` general position, restricted to the pinned class habitat"*: on
  the class the conjunct is satisfiable (*Step D12*) and the gate is measured
  quiet at five shapes. A future pass proposing the class-restricted form is
  **not** answered by (DM-7)/(DM-8); what answers it is the open successor
  below, plus §(K-ind) *Step I6* on the transport side.

**And it is (D1)'s split, not a new one.** (D1) made C1 provably false exactly
off the class, on the (K-res) `k = 3` family; (DM-7) makes C2 provably false
exactly off the class, on the `def₃(G−a) ≥ 4` family. Same section, same habitat
split, two different mechanisms — so §8.2's *"nothing in `(K-dom)` bears on
C2"* is **refuted** (struck there in the same commit).

**The stratifying invariant is NOT `k`.** (D3) makes the companion length the
arc's organizing local invariant for the *escape at a split chain*, and (D2)
grades far-dependence as `3(k−3)`. Neither governs the *carried* conjunct: the
54 forced indices have `k` = **6, 8 and 9** (`--gen` reports per-habitat `k`
ranges `[3,6]` and `[3,6,8,9]` at the two (K-res) habitats), and the three
`k = 3` indices of each are precisely the ones the gate does **not** fire on.
One object mixes `k` = 3 through 9, so no single `k`-stratum is the right frame
here; the conjunct's invariant is `def₃(G − a)`, a different function of the
same object.

**The open successor, and it is the whole class-side question.** *Which class
shapes, if any, have a degree-2 vertex with `def₃(G − a) − def₃(G) ≥ 4`?*
Measured: **none** at 5 habitats / 62 degree-2 indices. (SD-6)'s branch bound
`ℓ ≤ 5` on class members is the obvious candidate mechanism and is **not** it —
NT21c3's forced index `a = 110` sits on a branch of length **3** — so the
class-side gate needs its own argument.

### Step D12 — (DM-9): ESC is satisfiable on the class, simultaneously

> **(DM-9)** *(exhibited, per shape)* At each of the five class habitats there is
> a single exact-ℚ pencil realization of `G′` at which reading ESC holds at
> **every** degree-2 index at once: θ(3,4,5) 8/8 (seed 1), NT21 16/16 (seed 2),
> NT16k5 11/11 (seed 2), `K4` dbl-subdiv 11/11 (seed 2), `K5−M` dbl-subdiv 15/15
> (seed 2). At the two (K-res) habitats the best any seed achieves is 3/8 and
> 3/16, and **every** failure is one of (DM-7)'s forced indices.

**Why this needs its own mode.** A carried conjunct is a statement about **one**
realization at **all** indices, and no landed measurement in the arc has that
shape: §(K-dom) *Step D4* measures **one split per habitat**; §(K-flank) *Step
F2* exhibits one witness per shape for the four conjuncts plus the rank target;
*Step F5* runs 16 `e₀`-end splits. None asserts a single realization good at
every index of one graph. Simultaneity was the live risk and it is **discharged
on the class** — a finite intersection of dense opens in an irreducible chart is
dense open ((D4)'s argument, applied per index), and the witness makes the
intersection nonempty at a rational point. A `SAT` verdict here is an
**existence** claim about a named seed, never *"the conjunct holds"*.

*Exact:* `--sim`, 7 habitats × 3 seeds, every degree-2 index enumerated. The
class-vs-(K-res) split of the verdicts is **asserted**, not merely printed: a
SAT habitat off the class, or an UNSAT habitat on it, halts the run.

### Step D13 — (DM-10): reading GEN is unsatisfiable, class exemplar included

> **(DM-10)** *(the `k = 3` half proven; the rest measured over a seed sweep)*
> Reading `V_bc` *general position* as *a general point of `Gr(3,6)`* is
> **unsatisfiable at five of the seven habitats, including the class exemplar
> θ(3,4,5)**. At **22 of 85** degree-2 indices `rank Q|_{V_bc} = 2` at every one
> of 6 seeds, so `V_bc` lies in the discriminant hypersurface
> `{det Gram_B = 0}` of `Gr(3,6)`; per habitat θ(3,3,6) 3/8, NT21c3 3/16,
> **θ(3,4,5) 6/8**, NT21 6/16, NT16k5 4/11, and 0/11, 0/15 at the two double
> subdivisions.

Two strata, two epistemic statuses, and they must not be merged.

- **`k = 3`: a theorem.** (D1)'s basis-free corollary applies at every index
  whose *own* companion length is 3, not only at the split chain: path-sum
  containment is an equality of 3-spaces, so `V_bc = S_P = ⟨C₁, C₂, C₃⟩`, and
  the **ordered chain** Gram has zero diagonal (line extensors) and only
  `B(C₁, C₃) = [b, x₁, x₂, c]` off it. `--gen` asserts that **shape**, not
  merely the rank — `nz == [(0,2)]` at all **6** `k = 3` indices, plus
  `span(C) = V_bc`. *The basis matters*: `span_basis`' RREF basis of the same
  3-space has a different (equally rank-2) Gram, and asserting the shape in the
  wrong basis is the first thing the driver got wrong.
- **`k ≥ 4`: measured, and the cap is the whole claim.** `rank` is lower
  semicontinuous in the realization, so the **maximum over seeds** is a lower
  bound for the generic rank; a `2` there means *"rank 2 at every seed drawn"*,
  and the sweep was deepened to **6 seeds** precisely because the claim is a
  maximum (the counts are identical at 3 and at 6). This is **not** a proof that
  the generic rank is 2, and a `0` count at the two double subdivisions is *"no
  failure witness under cap"*, never a proof that GEN is satisfiable there.

**Consequence for C2.** The only surviving reading anywhere is **ESC**, the
(PC-Z) escape — which is the crux `hK` already needs. So C2's *"carry the
crux"* framing is exact in a way the entry did not intend: there is no weaker,
more generic-sounding condition available to carry instead, because the
generic-sounding one is false at the class exemplar.

### Step D14 — (DM-11): the motive's own shape, and what a fifth conjunct owes

Read against landed source; **no driver**, and this step says so rather than
borrowing another mode's authority.

> **(DM-11)** *(source-derived, `Motive.lean` / `Escape.lean`)*
> `IsNondegPencilRealization` occurs in the motive **twice, with opposite
> variance**: inside `PencilNondegFeasible` (`Motive.lean:133`), an
> **antecedent** of `PencilPair`'s first conjunct (`:160`), and inside
> `HasGenericPencilRealization` (`:140`), its **consequent**. Adding a fifth
> conjunct therefore does not simply strengthen the motive: it (i) strengthens
> the consequent, (ii) **narrows the antecedent**, and (iii) thereby moves
> graphs across `Escape.lean:396`'s `by_cases hfeas` from the `hK` branch
> (`:419`) into the **`hbareSplit`** branch (`:427`) — C2 buys a stronger `hK`
> input by **enlarging kernel (K-bare)'s habitat**.

Three consequences, each checkable at source.

1. **The (K-bare) cost is real but currently absorbed.** (BE-14)'s target is
   *direct attainment* — unconditional, discharging `hbareSplit` **and**
   `PencilPair`'s bare conjunct — so a widened `¬PencilNondegFeasible` costs
   nothing *against that target*. It would cost something against any
   antecedent-using route to `hbareSplit`. Worth pricing before, not after.
2. **The transport residual lands on the cut arm's known sharp boundary.**
   `IsNondegPencilRealization.mono` (`Motive.lean:245`) restricts the four
   conjuncts along `H ≤ G` with an explicit residual `hdemote` for the fourth
   conjunct at a **demoted** hub, and `PencilNondegFeasible.mono` (`:272`)
   discharges it only at demotions to `H`-degree **≤ 1**, its docstring
   recording that at `H`-degree `2` the residual *"genuinely has no source in
   `G`'s witness"*. A fifth conjunct indexed by the **degree-2** vertices of `H`
   needs its residual at precisely the demotions the landed infrastructure
   already calls unavailable, and its content — `V_bc` of `H − v` — is an object
   `G`'s witness does not determine. **The cut arm's recorded sharp boundary is
   the new conjunct's index set.**
3. **The fourth conjunct is what makes the new one well-formed.** At a degree-2
   `a` — hence a non-hub, so conjunct 4 does apply — `LinearIndepOn point
   (closedNbhd a)` reads `closedNbhd a = {a, b, c}` and says exactly that
   `pt a, pt b, pt c` are independent, i.e. `dim Λ²π̂ = 3`, the hypothesis
   (PC-Z) needs. Derived from the definition body (`Motive.lean:115` with
   `Graph.closedNbhd`, `:92`), **not** from `repin.star_span_ranks`' docstring,
   which identifies rank 3 at *every* vertex with conjunct 4 and thereby
   overstates it at a hub (where conjunct 4 is not imposed and a `≥ 5`-member
   closed neighbourhood is never LI in `K⁴`); at a **degree-2 non-hub** the two
   do coincide, which is the only case the new conjunct indexes. `--validate`
   check 5 asserts the rank **directly** at **85 of 85** degree-2 indices, so no
   docstring is load-bearing. The new conjunct is therefore *supported* by a
   landed one rather than in tension with it.

**Filters.** The **growing-ground-set** test is **passed** ((DM-5): adjacent
edge pairs, derived from `E(G)`); what is non-local is the conjunct's *value* at
an index, `V_bc` being a global object of `G − a`, which is the honest form of
§4-C2's first bullet. **§2.5 counting saturation** does **not** bar the
conjunct — it is a rank/incidence condition on a realization, not a
count-expressible invariant, and §2.5 is a **negative** result supplying nothing
either way. But (DM-6) sharpens the picture in §2.5's direction: `dim V_bc`
**is** a count at every degree-2 index, so the *dimension* half of "general
position" is exactly as combinatorially certifiable — and as useless — as
§(K-ind) *Step I5*(1) found the Jacobian rank to be. What is not a count is
*which* 3-space of `Gr(3,6)` one lands on, and that is the whole remaining
problem.

**Verdict for the option board.** C2 **dies as a uniform carry** by its own kill
condition. What survives is *"prove the conjunct at every class shape
independently"* — **not refuted here** — which is (a) not an invariant carried
along an induction, the §4 gate having already fired on that, (b) still blocked
at the `hcontract` arm by §(K-ind) *Step I6*, and (c) resting on a class-side
gate (*Step D11*'s open successor) that has 62 confirmations and no argument.

### Verification

`notes/scripts/w4/dominance.py` (tracked, new this pass; exact-ℚ, stdlib-only,
no CAS; sits beside `flanks`/`pure`/`lambda` on `repin`/`pitch`/`kslide`; every
sampled object rank/dimension asserted, including `repin.star_generic` as the
`plane_basis` genericity guard; all rng seeded, `PYTHONHASHSEED=0` pinned;
all four modes verified byte-deterministic across repeated runs). Run from the
repo root:

> **RE-BASELINED 2026-08-06 (slice S2), and every figure below is UNCHANGED or
> STRONGER.** `base_seed`'s guard was `star_span_ranks` alone, and its
> docstring's promise *"a seed failing this is rejected, not measured"* was
> false for the free-rotor half of the `plane_basis` artifact ((OC-7), F13);
> it is now the composite `repin.star_generic`. Effect: **the seeds moved**
> (the first clean seed per habitat is a later integer) and **three per-seed
> readings improved to the bound** — `--jac`'s FIXED rank is now **9 at every**
> `k ≥ 4` seed (three contaminated seeds used to report 8), `--far`'s far
> block is now `3(k−3)` at **every** seed (`k = 6` used to report 5 and 7 of
> 9), and `--cap`'s `dim span(P)` at `K4` dbl-subdiv is now `[6]`, not
> `[5, 6]`. So the *table below is untouched*, and what changed is that
> "attained at every habitat" is now "attained at every **seed**": the
> exceptions were the contaminated draws.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --cap       # (D1), (D3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --jac       # the rank table
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --far       # (D2)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --validate  # the machinery
```

**The model, and why the differential is computable in exact ℚ.** `V_bc` is the
image under `m ↦ m(b) − m(c)` of the kernel of the **augmented** system in
unknowns `(m_x)_{x ∈ V(H)}`, `(ω_e)_{e ∈ E(H)}`

```
m_x − m_y − ω_e·C_e = 0      (6 rows per edge e = (x,y)),
```

whose entries are *polynomial* in the chart coordinates. So each directional
derivative is implicit differentiation of a kernel: `A u = 0` and
`A u′ = −(∂A) u`, a derived linear system solved at the base point, with
`dV(δ)` the class of `u′[m_b] − u′[m_c]` in `K⁶/V_bc`. Solvability of every such
system is itself asserted (it is exactly the local constancy of `rank A`). The
chart tangent is `ker` of the differentiated pencil condition, so the derivative
never leaves the stratum. This is §(K-pitch) *Step 1(b)*'s "`V_bc` needs only a
kernel computation" made differentiable.

**The C2 satisfiability trace (2026-09-03, direction DSAT, *Steps D8–D14*)**
is `notes/scripts/w4/dsat.py` (tracked, new this pass; exact-ℚ, stdlib-only, no
CAS; sits **beside** `dominance` rather than on it, taking `dominance`'s
`HABITATS` / `seeds_for` / `simple_paths` / `path_span` / `bad_locus_meets` /
`class_status`, `repin`'s `span_basis` / `lambda2_through` / `star_generic`,
`pitch`'s `klein` / `Q` / `H_motions_vbc`, `pencil_escape.build_rigidity`,
`nogood_subdiv.deficiency` and `kbare_common.verts_of`; it reimplements nothing
and imports **no** `bimage`/`bwin`/`binduc` device, so all three of *Harness
debt*'s recorded silent hazards are **unreachable** from it rather than merely
avoided). No new source of randomness — every configuration is
`dominance.base_seed(edges, v, s)` at a printed integer `s` — and all five modes
verified **byte-deterministic** across repeated runs with `PYTHONHASHSEED=0`.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/dsat.py --index      # (DM-5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dsat.py --gate       # (DM-6), (DM-7), (DM-8)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dsat.py --sim        # (DM-9)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dsat.py --gen        # (DM-10)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dsat.py --validate   # the machinery + one guard
```

Per mode, what is asserted:

- `--index`: every `(a, {b,c})` triple of `G′` enumerated exhaustively;
  `dim span{C_ax} = 2` at **every** body whatever its degree; at `deg(a) ≥ 3`,
  `dim mot(H/bc) > dim mot(G′)` (so (DM-6) does not reach there) and
  `dim V_bc ≥ 4 ⟹` both meets nonzero; at least one forced-bad `deg ≥ 3` triple
  per (habitat, seed).
- `--gate`: `dim mot(G′) = 6 + def₃(G′)`; `dim V_bc = dim mot(H) − dim
  mot(H/bc)` with the welded space computed **independently**;
  `dim mot(H/bc) = dim mot(G′)`; `dim mot(H) ≥ 6 + def₃(H)`;
  `dim V_bc ≥ def₃(H) − def₃(G′)`; and the gate's own conclusion at every
  firing index.
- `--sim`: the escape at every degree-2 index of one realization, and the
  class-vs-(K-res) split of the verdicts.
- `--gen`: `rank Q|_{V_bc} ≤ dim V_bc`; at `k = 3`, `V_bc = S_P`, the ordered
  chain Gram's **shape** (zero diagonal, single off-diagonal entry at `(1,3)`)
  and rank 2.
- `--validate`: `vbc_of` vs `pitch.H_motions_vbc` (two call paths); `escape_at`
  vs `dominance.bad_locus_meets` (two `α(a)` constructions); `meet_dim` vs a
  brute-force intersection basis; both (PC-Z) spaces 3-dimensional and
  **totally** `B`-isotropic; conjunct 4 at every degree-2 index; a
  **constructed** collinear adversarial witness with its pinned counter-fact
  and a negative control; and `dim V_bc = def₃(H) − def₃(H/bc)` at every index.

**Figures (the trace).**

| figure | value |
|---|---|
| `--index` triples enumerated | **350** (7 habitats × 2 seeds); `dim T = 2` at **350/350** |
| `--index` `deg(a) ≥ 3` forced-bad | **172/180**; **0** Grassmann exceptions; `dim mot(H/bc) > dim mot(G′)` at **180/180** |
| `--index` `deg(a) = 2` bad | **36/170** — the degree-2 restriction is necessary and not sufficient |
| `--gate` identity violations | **0 of 255** degree-2 indices (7 habitats × 3 seeds) |
| `--gate` gate firings | **54/255**, all 54 with both meets nonzero; census `def₃(G′−a) − def₃(G′)` = 3 at 201, 4 at 54 |
| `--gate` per habitat | θ(3,3,6) **5/8**, NT21c3 **13/16**, θ(3,4,5)/NT21/NT16k5/`K4`/`K5−M` **0** |
| `--sim` simultaneous SAT | **5/5 class habitats**: 8/8, 16/16, 11/11, 11/11, 15/15 at seeds 1, 2, 2, 2, 2 |
| `--sim` (K-res) | best 3/8 and 3/16; every failure a (DM-7) forced index |
| `--gen` GEN-dead indices | **22/85** at the max over **6** seeds; **6** by the `k = 3` theorem; θ(3,4,5) **6/8** |
| `--validate` | 7 checks; 85/85 conjunct 4; adversarial witness `rank = 2`, `dim Λ²π̂ = 1`; 85 agree / 0 disagree |

**Caps on the trace, and the one figure that does not depend on one.** Three
caps bind, and none is a proof of nonexistence (§4 convention 8): the **habitat
family** is the seven of *Step D4*, not a sweep — and that is exactly the axis
(DM-8)'s open successor lives on, since whether a *class* shape can fire the
gate is a statement about the family and five class shapes is the cap; **seeds**
are the first `n` integers of `dominance.base_seed`'s `1..400` range accepted by
its `repin.star_generic` gate, so every *"at every seed"* is *"at every seed
drawn"*; and `simple_paths` runs to a length bound of 9. The exception is
**(DM-7)**, an argument off a combinatorial trigger that holds at every
realization — the driver asserts it rather than searching for it. Every other
negative here is *"not found under cap"*, and **(DM-10)'s `k ≥ 4` half is not an
UNSAT proof**: it is a maximum over six seeds, and it is the figure in this
section most likely to need a successor's correction.

Habitats (7): θ(3,3,6) and **NT21c3** (`k = 3`; NT21c3 is the NT21 hub
multigraph with the companion shortened to 3 — `b`–`c` paths 3 and 3, plus
`b–u:4, u–c:4, b–w:3, w–c:3, u–w:4`; `|V| = 21`, `|E| = 24` — so the `k = 3`
cap is not a θ artifact); θ(3,4,5) and NT21 (`k = 4`); **NT16k5** (`k = 5`; hubs
`b,c,u,w`, one `b`–`c` path of length 3 plus `b–u:2, u–c:3, b–w:2, w–c:3,
u–w:5`; `|V| = 16`, `|E| = 18`); and the double subdivisions of `K4` and
`K5 − M` (`k = 6`, the arc's control habitats and route 1's locality-gate
shapes). Every one is asserted tight (`5|E| = 6(|V|−1)`), `def = 0`,
`hcard_ok`, triangle-free at load; class-vs-(K-res) is decided per habitat by
the two agreeing certificates of *Step D3*.

Per mode, what is asserted:

- `--cap`: `V_bc ⊆ S_P` at **every** `b`–`c` path of `H` (not only shortest);
  at `k = 3`, `V_bc = S_P` exactly; `rank Q|_{V_bc} = 2 ⟺ k = 3`; the
  `C_{3+k}` rigidity dichotomy, cross-checked against
  `kslide.no_rigid_branch_union`; and `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0` (the
  escape) at every seed.
- `--jac`: `dim V_bc = 3`; no FIXED/UNPINNED direction moves `a`, `b` or `c`
  (the bad locus stands still); every implicit-differentiation system solvable;
  `rank dV ≤` the (D1) cap; at `k = 3` the cap **attained** and the UNPINNED
  rank `≤ 6`; at `k ≥ 4` rank 9 attained.
- `--far`: `rank dV|_{far} ≤ 3(k−3)` at every seed, and `= 0` at `k = 3`.
- `--validate`: three independent models for `V_bc` agree (the rigidity matrix
  via `pitch.H_motions_vbc`, the augmented system, the cycle kernel), with
  `dim ker(augmented) = dim mot(H)` and `dim Z = dim mot(H) − 6`; the
  augmented-system and **cycle-kernel differentials agree entry by entry** on
  every chart direction (two different matrices, two different solves); and an
  exact secant quotient `φ(t)/t` on a chart-*exact* ray (directions moving no
  hub normal keep `θ₀ + tδ` in the chart identically) converges to the computed
  differential, error halving at `t = 2^{−3..−6}`.

**Figures.**

| figure | value |
|---|---|
| `--cap` seeds | **21** over 7 habitats; containment at every `b`–`c` path; `rank Q\|_{V_bc}` = 2 at `k = 3`, 3 at `k ≥ 4`; escape holds at **21/21** |
| `--jac` FIXED rank, `k = 3` (θ(3,3,6), NT21c3) | **4** at 6/6 seeds = the (D1) cap, attained |
| `--jac` UNPINNED rank, `k = 3` | **6** at 6/6 seeds — the pin is not the cause |
| `--jac` FIXED rank, `k ≥ 4` (5 habitats) | **9** attained at each; `dim Gr(3,6) = 9`, so **dominant** |
| `--far` far block at `k = 3,4,5,6` | **0, 3, 6, 9** = `3(k−3)`, the (D2) bound, attained at every habitat |
| `--far` far directions in `ker dV` at `k = 3` | **13/13** (θ(3,3,6)), **41/41** (NT21c3) |
| `--validate` habitats | **7**; three `V_bc` models agree; two differentials agree on all 9 entries × every direction; secant errors halve |

**Confidence verdict.**

- **(D1) (the `min(9, 6k−14)` cap), (D2) (the `3(k−3)` far block), (D3)
  (`hnoRigid ⟹ k ≥ 4`), (D4) (dominance ⟹ the escape on a dense open set):
  proven-informally**, each with a driver mode asserting that sentence.
- **Dominance at the 5 probed class habitats: proven-informally per shape**
  (rank 9 at a rational seed + chart irreducibility + semicontinuity).
- **Dominance as a class-uniform statement, (K-dom): open** — and **false** on
  the (K-res) `k = 3` family, so it cannot serve `hK` in the form `hK` is
  carried.
- **§4-C1's claims (i) and (ii): REFUTED** (Step D6). C1 is **not** an
  inductive route and does not escape the ingredient-2 failure; it is not
  recommended as the phase's direction.
- **Class uniformity is untouched.** No uniform gap closes here.
- **(DM-5)'s structural half, (DM-6), (DM-7): proven.** (DM-6)'s three steps are
  linear algebra plus the definition of `def₃`; (DM-7) is Grassmann. Each has a
  driver mode asserting its sentence.
- **(DM-8), (DM-9), (DM-10)'s `k ≥ 4` half: measured**, exhaustive over each
  object's index set, capped at 7 habitats and 3 (resp. 6) seeds. **(DM-10)'s
  `k = 3` half: proven** — (D1)'s corollary, asserted through the chain Gram's
  shape. **(DM-11): source-derived**, no driver.
- **§4-**C2**: DEAD as a uniform carry**, by its own kill condition — the
  (K-res) half **proved**, the class half **measured at five shapes**. **Not
  shown dead as a class-only conjunct.** `hK`, `hbareSplit`, (GR-15), (D1)–(D4)
  and every landed figure above are unmoved, and C1's strike is unaffected.

**What would change this.** *(i)* A class habitat (`k ≥ 4`, `hnoRigid`) whose
FIXED rank is `< 9` at *every* seed — that would be a sharp new obstruction and
would make (K-dom) false outright; none found, and the driver's `--jac` is the
place to add shapes. *(ii)* A far-direction rank exceeding `3(k−3)` — that would
refute (D2) and, with it, Step D6's refutation of claim (i); asserted per seed.
*(iii)* An error in the differentiation itself — guarded by two independent
derivative routes agreeing entry by entry plus the secant test, so an error
would have to be shared by the augmented and cycle models. *(iv)* A `k = 3`
class habitat — impossible by (D3), whose two certificates agree at every
habitat; a disagreement would be the finding. *(v)* A mechanism making
`rank dV = 9` *combinatorially* certifiable at every class shape — that, and
only that, would turn C1 into a uniform route; nothing in the arc suggests one,
and §(K-pure) *P5* is the reason to expect none. *(vi)* A **class** habitat with
a degree-2 vertex `a` and `def₃(G−a) − def₃(G) ≥ 4` — that would make C2 UNSAT
on the class too and would be a sharp new obstruction; none at 62 indices over 5
habitats, and `--gate` is where to add shapes. *(vii)* A **proof** that no class
member has such a vertex — that would upgrade (DM-9) from per-shape to
class-wide for the *dimension* half of the conjunct, leaving only the Schubert
half; (SD-6)'s `ℓ ≤ 5` is **not** the mechanism. *(viii)* A realization of an
infinitesimally rigid `G′` at which `dim mot(H/bc) > 6` for a degree-2 `a` —
that would refute (DM-6) step 2; asserted at 255 indices. *(ix)* An index with
`k ≥ 4` and `rank Q|_{V_bc} = 3` among the 22 (DM-10) reports dead — that would
make the max-over-6-seeds reading a cap artifact rather than a generic value.
