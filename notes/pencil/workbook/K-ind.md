## §(K-ind) — can a numerical invariant of the failure locus be carried along the generating moves? (**NO — the transport graph on the class is edgeless; the one genuine chart relation runs the wrong way and bottoms out at `k ≤ 3`**)

Answering the question `notes/Pencil-strategy.md` §4's framing correction raises
but never poses: *the induction is already the framework, so strengthen the
inductive invariant — can a **numerical** invariant of the failure locus
(equivalently of the image of `H ↦ V_bc`) be **carried along the generating
moves**?* Read against §(K-dom) (the grading), §(K-pitch) *Steps 1, 5, 6*
(path-sum containment, the bracket monomial, the refuted naive collapse),
§(K-pure) *P3* ((PC-Z)), and the **landed** induction skeleton
`Graph.pencil_reduction` (`Molecular/Induction/ForestSurgery/Reduction.lean:850`).

**Headline.**

- **No move of the phase's induction takes one class member to another.**
  Tightness pins `(|V|,|E|) = (5c+1, 6c)` in the cycle rank `c` **(I1)**; every
  arm of `pencil_reduction` strictly drops `(|V|,|E|)`; the split arm preserves
  `c` and therefore raises `index` by exactly `1` **(I2)**, leaving the tight
  locus irreversibly; and the only index-preserving arm — rigid contraction — is
  unavailable at a class member by `hnoRigid`. So the relation "reachable by one
  generating move", restricted to the `hK` habitat, is **empty**. There is
  nothing to transport *along*.
- **The one genuine chart relation the moves do give is real, new, and runs the
  wrong way.** Un-subdividing (= `splitOff`) embeds the shorter shape's chart
  into the longer shape's chart as a closed sub-locus on which `V_bc` is
  *literally the shorter shape's* `V_bc` **(I3)** — so `Image(V_bc)` is
  **monotone under subdivision**. But the induction *descends*, so the usable
  direction is the one monotonicity does **not** give, and every descending chain
  reaches `k ≤ 3`, where §(K-dom) **(D1)** proves the invariant is `≤ 4` and
  dominance is impossible. **The base case of the only available induction is a
  proven failure of the invariant.**
- **"Numerical invariant of the failure locus" is one bit.** `F` is the pullback
  of `σ₁(α(a)) ∪ σ₁(Λ²π̂)`, i.e. a **divisor**. Its only numerical invariant is
  `codim F ∈ {0,1}`, and `codim F = 1` **is** `hK` **(I0)**. Every genuinely
  numerical candidate lives on the image side, where it is `dim Image` — i.e.
  **(K-dom)**, already run and struck.
- **The class's infinitude is entirely in the hub multigraph `G°`, and no move
  touches `G°`** **(I4)**. Within one `G°` the class is a **finite antichain**.
  So even a perfect subdivision-transport theorem compresses a finite set to a
  smaller finite set and cannot reach class uniformity.

### Standing notation (on top of §(K-dom))

Split chain `b–v–a–c` at a target-rank `G′`-seed, `b, c` hubs,
`deg v = deg a = 2`; `G′ = G.splitOff v a b e₀`; `H := G − v − a = G′ − a`;
`V_bc` the relative twist system, `k` the companion length (shortest `b`–`c`
path of `H`). `index(G) := 5|E(G)| − 6(|V(G)| − 1)`; `c(G) := |E| − |V| + 1` the
cycle rank. For a class member (2EC, `hnoRigid`, `hcard`), (R4) makes `G` a
subdivision of its **hub multigraph** `G°` (vertices = hubs, edges = branches);
`ℓ_P` are the branch lengths, `m := |E°|`, `n := |V°|`, `c° = m − n + 1 = c(G)`.
`Chart(G)` = the nondegenerate pencil chart (`IsNondegPencilRealization`,
`Molecule/Pencil/Motive.lean:110-115`), `F(G) ⊆ Chart` the failure locus.

### Step I0 — the failure locus has no numerical content beyond `hK`

By (PC-Z) (§(K-pure) *P3*) the escape fails at a seed exactly when `V_bc` meets
`α(a)` or `Λ²π̂`. "Meets a fixed 3-space" is the Schubert condition `σ₁` on
`Gr(3,6)`, which **is the hyperplane class** of the Plücker embedding
(classical); so each condition is a single hyperplane section, and

> `F(G) = Φ^{-1}(σ₁(α(a))) ∪ Φ^{-1}(σ₁(Λ²π̂))` = `{Q₁ Q₂ = 0}`,  `Φ := (H ↦ V_bc)`,

the zero divisor of **one** polynomial `Q = Q₁Q₂` on the irreducible chart. Two
consequences, both worth stating because they bound the whole question:

1. **`F` is a divisor or everything.** `codim F ∈ {0, 1}`, with `0` iff `Q₁ ≡ 0`
   or `Q₂ ≡ 0`. So *every* numerical invariant of `F` — dimension, degree of its
   components, multiplicity, Hilbert polynomial — is either constant on the class
   for trivial reasons or is a re-encoding of the single bit `Q ≢ 0`. **Carrying
   a numerical invariant of `F` inductively is carrying `hK` inductively.** The
   question as literally posed is circular, and its own parenthetical ("or
   equivalently of the image") is the only non-circular reading.
2. **On the image side the only transportable number is `dim Image Φ`.**
   `deg Image Φ` is not monotone under any containment and is unavailable
   without a description of the image (`Pencil-strategy.md` §2.4's open
   problem); `dim Image Φ = 9` is exactly **(K-dom)**.

> **Four objects, kept apart** (coordinator scrutiny, 2026-08-05; the arc's prose
> had been conflating them). **(1)** `V_bc(p)` is a **point** of `Gr(3,6)`, not a
> locus. **(2)** The graph-dependent object is the **map**
> `φ_G : chart(G) → Gr(3,6)` and its **image** — the thing `Pencil-strategy.md`
> §2.4 says we have no description of. **(3)** The bad locus `B ⊆ Gr(3,6)` is the
> union of the two Schubert divisors `σ₁(α(a))`, `σ₁(Λ²π̂)`, each the
> **hyperplane class** in the Plücker embedding, so `B` is cut by a *single
> degree-2 form that factors into two hyperplanes*, and — the point that is easy
> to miss — `B` is **graph-independent** (§(K-dom) *D0*: it depends only on
> `pt(a)` and `plane(a,b,c)`). **(4)** `F = φ_G^{-1}(B) ⊆ chart(G)` is a
> hypersurface exactly when `hK` holds there, and the whole chart when it fails.
>
> **The connection the workbook did not make.** That global factorization is
> precisely the shadow of §(K-Λ) **(Λ1)**'s local result — `Φ_loc` is always
> rank 2, a product of two distinct rational linear forms, *"the local quadric is
> a pair of rational hyperplanes"*. **The two computations are the same geometry
> at two scales**: a degree-2 form on `Gr(3,6)` cutting `B`, and the degree-2
> form on the far covector cutting the local bad locus, both factoring into two
> hyperplanes for the same reason — the two isotropic completions of (PC-Z).
>
> Orientation, not used: `deg Gr(3,6) = 42` in the Plücker embedding (the
> classical hook-length count). **Flagged UNVERIFIED, do not assert it:** whether
> the discriminant hypersurface `{det Gram_B = 0} ⊆ Gr(3,6)` — the locus §(K-dom)
> *D1* puts every `k = 3` habitat into — has class `2σ₁`. Nothing in the arc
> depends on it.

### Step I1 — (I1): a tight graph's size is a function of its cycle rank

> **(I1)** *(proven; two lines)* For any finite graph, `index(G) = 0` (tight) is
> equivalent to `|E(G)| = 6c(G)` **and** `|V(G)| = 5c(G) + 1`.

*Proof.* `c = |E| − |V| + 1` gives `|V| = |E| − c + 1`; substituting into
`5|E| = 6(|V| − 1)` gives `5|E| = 6(|E| − c)`, i.e. `|E| = 6c`, and then
`|V| = 6c − c + 1 = 5c + 1`. ∎

This is the equality case of the dictionary's **(R2)** size bound `|V| ≤ 5c + 1`,
and for a subdivision it is the recorded tightness budget `Σ_P ℓ_P = 6c°`
(§(K-pitch) *Step 6*, `index(G) = 6c° − Σℓ_P`) in disguise: `|E| = Σℓ_P`.

*Cross-check against the recorded habitats* (all six agree; re-derived
independently by the coordinator, 2026-08-05):

| habitat | `G°` | `c` | `Σℓ = |E|` | `|V|` | `6c` / `5c+1` |
|---|---|---|---|---|---|
| θ(3,4,5) | theta | 2 | 12 | 11 | 12 / 11 |
| θ(3,3,6) | theta | 2 | 12 | 11 | 12 / 11 |
| NT16k5 | 4 hubs, 6 branches | 3 | 18 | 16 | 18 / 16 |
| `K4` dbl-subdiv | `K4` | 3 | 18 | 16 | 18 / 16 |
| NT21 | 4 hubs, 7 branches | 4 | 24 | 21 | 24 / 21 |
| `K5−M` dbl-subdiv | `K5−M` | 4 | 24 | 21 | 24 / 21 |

(`P21`, `Σℓ = 24`, `|V| = 21`, `c = 4` also fits; the W4 test shapes `W19`/`S29`
have `f(V) = 2 ≠ 0` and correctly do **not** — they are not tight.)

**Immediate corollary, used throughout.** Two tight graphs of the same cycle rank
have **the same** `|V|` and `|E|`. Since every arm of `pencil_reduction` hands
its IH only graphs with `|V′| < |V|` (the loop arm being the sole
`|V|`-preserving one, and class members are `Simple`), **no arm can relate two
tight graphs of equal cycle rank at all** — before any geometry is considered.

### Step I2 — (I2): the split move raises `index` by exactly 1, and fixes `G°`

Read off the landed definition **body**, not its docstring (`Graph.splitOff`,
`Molecular/Induction/Operations.lean:769`): `splitOff v a b e₀` has
`V(G) ∖ {v}` and carries every `G`-edge avoiding `v`, plus one fresh edge `e₀`
joining `a, b`. At `deg v = 2` with distinct non-loop edges `eₐ, e_b` that is
`|V| − 1` vertices and `|E| − 1` edges; **the inverse move is exactly edge
subdivision**.

> **(I2)** *(proven)* For `deg_G v = 2`:
> `index(G.splitOff v a b e₀) = index(G) + 1`, `c(G.splitOff v a b e₀) = c(G)`,
> and the hub set, the hub multigraph `G°`, and every branch length except the
> one containing `v` are unchanged (that one drops by 1).

*Proof.* `5(|E|−1) − 6(|V|−2) = [5|E| − 6(|V|−1)] + 1`; `c = |E|−|V|+1`, both
drop by 1. `splitOff` changes no vertex's degree except deleting `v` (`a` trades
`eₐ` for `e₀`, `b` trades `e_b` for `e₀`), so `{deg ≥ 3}` — the hub set — is
untouched, and the branch through `v` merely loses one interior vertex. ∎
(Checked numerically at NT21: `index 0 → 1`, `c` preserved.)

Consequences, in the descending direction the induction actually runs:

- **The tight locus is left irreversibly by splitting.** `index` strictly
  increases at every step, so a class member (`index = 0`) is the **top** of its
  chain and no class member sits below another.
- **`G°` and `c` are constant along a split-descent**, which shortens branches
  and terminates at `G°` itself (all branches length 1) at `index = 6c° − m`.
- **The descent is short.** By (R3) every cycle of length `≤ 6` is rigid, so a
  class member has girth `≥ 7`; each split drops by 1 the length of every cycle
  through the shortened branch, so after at most `girth − 6` splits on one cycle
  a rigid `C_{≤6}` appears and `hnoRigid` fails — the descent switches to the
  **contraction** arm. (`K4` double subdivision: girth 9, so at most **3** split
  steps.)

### Step I3 — (I3): the subdivision-monotonicity lemma (the genuine positive)

> **(I3)** *(proven-informally; **not** driver-tested)* Let `H̃` be `H` with edge
> `xy` subdivided by a new degree-2 body `u`, terminals `b, c` unchanged. Then
> the locus `Z := {pt(u) ∈ line(pt x, pt y) ∖ {pt x, pt y}} ⊆ Chart_full(H̃)` is a
> nonempty closed sub-locus on which `mot(H̃)|_{V(H)} = mot(H)` **exactly**,
> hence `V_bc(H̃)|_Z = V_bc(H)`. Consequently
> `Image(V_bc(H)) ⊆ closure(Image(V_bc(H̃)))`, and
> `dim Image(V_bc(H̃)) ≥ dim Image(V_bc(H))`.

*Proof.* Write `pt u = λ pt x + μ pt y`, `λμ ≠ 0`. Then
`C(xu) = pt x ∧ pt u = μ·(pt x ∧ pt y)` and `C(uy) = λ·(pt x ∧ pt y)`, both
`∝ C(xy)`. A body-hinge motion satisfies `m(p) − m(q) ∈ ⟨C(pq)⟩` per hinge, so on
`Z` the two hinges at `u` give `m(x) − m(y) = (ω₁μ + ω₂λ)C(xy)` — precisely
`H`'s constraint at `xy` — and conversely any `H`-motion extends by
`m(u) := m(x) − ω₁μ C(xy)`. Every other edge is shared. So the restriction map
`mot(H̃) → mot(H)` is onto with the `m(u)`-fibre, and `V_bc` agrees. `Z` is in
the pencil stratum: `u` has degree 2 so it is not a hub and carries no panel
condition; at a hub endpoint (say `x`) the hinge `C(xu) ∝ C(xy)` already lies in
`Π(x)` provided `pt y ∈ Π(x)`, one further equation on `Chart(H̃)`, satisfiable
because two planes always meet in a line. Finally `Chart_full(H̃)` is irreducible
(§(K-slide) *Step 1(e)*: a tower of affine-linear fibres) and the nondegenerate
locus is dense open in it, so `Z ⊆ closure(nondeg)`; `V_bc` is regular near any
point where `dim V_bc` attains its generic value 3 (upper semicontinuity), and
`Φ(closure(U)) ⊆ closure(Φ(U))` for a regular `Φ`. ∎

**Why this does not contradict §(K-pitch) *Step 6(a)*.** That step refutes the
naive collinear collapse as a chart move, and its refutation is *simultaneous*:
"making chords panel-resident **along every `G°`-edge** forces each closed hub
star coplanar", impossible when the chords at a hub span 3-space. (I3) makes
exactly **one** edge's endpoints panel-resident, and only when an endpoint is a
hub — for an edge interior to a branch there is no panel condition at all and `Z`
is unconstrained. *One edge vs every edge* is the whole difference, and it is
worth recording because Step 6(a) reads, at a glance, as if it forbade (I3) too.

**And it is consistent with (D2).** Subdividing a **far** edge leaves `k` fixed
and (D2) caps the far block at `3(k−3)`; (I3) only claims `≥`, so the added
parameters may (and by (D2), beyond the budget must) land in `ker dV`.
Subdividing a **companion** edge raises `k` by 1 and raises the (D1) cap. No
tension.

### Step I4 — (I4): the class is a finite antichain inside each `G°`

By (I2) the split move fixes `G°`. By (I1) every class member over `G°` has
`Σ_P ℓ_P = |E| = 6c°` — a **fixed** total. Hence:

> **(I4)** *(proven)* The class members over a fixed hub multigraph `G°` are the
> length vectors `(ℓ_P)_{P ∈ E°}` with `ℓ_P ≥ 1`, `Σℓ_P = 6c°`, satisfying
> `hnoRigid` (every branch-union cycle has length `≥ 7`) and `hcard`. This set is
> **finite**, and it is an **antichain** for the componentwise (refinement)
> order, since all its members have the same coordinate sum.

The arc already computes with exactly this set without naming it: §(K-flank)
*F3*'s `210 = C(10,4)` all-`{3,4}` `K5` shapes (`Σℓ = 36 = 6·6`), the `155`
6v11e shapes, and §(K-slide-comb)'s **877 exhaustive `K4` shapes**
(`Σℓ = 18 = 6·3`) are enumerations of (I4)'s level set for one `G°` each.

**This is the decisive deflation of (I3), and it is independent of any geometry.**
An invariant transported by (I3) can only compare a class member to shapes with
*strictly smaller* `Σℓ` — i.e. to non-class shapes. Two class members over the
same `G°` are incomparable, so (I3) transports **nothing** between them. And the
infinitude of the class is entirely in the `G°` direction (`c° → ∞`), which by
(I2) no split move reaches. *The subdivision order compresses a finite set into a
smaller finite set, and the moves never cross between finite sets.*

### Step I5 — the three cheap kill-checks, answered

**(1) The `Pencil-strategy.md` §2.5 saturation trap — evaded in form, re-entered
in substance.** `dim Image Φ` is a Jacobian rank, not a count, so §2.5's blanket
ruling does not literally apply. But the split is the familiar §2.3 asymmetry:
the **upper** bound `dim Image ≤ min(9, 6k−14)` is (D1), a pure count, *proven*;
the **lower** bound `dim Image = 9` is the open per-shape determinantal
condition. Worse, the count-predicted value and the measured value coincide at
all seven §(K-dom) habitats (`4,4,9,9,9,9,9` against `min(9,6k−14)`), so the
count is **saturated as a predictor and useless as a certificate**.

**(2) The companion-length grading — the move changes `k`, in the fatal
direction.** A split on a branch carrying a shortest `b`–`c` path lowers `k` by
1. Since the induction **descends**, the move it performs *lowers* `k`, hence
*lowers* the (D1) cap. Any dimension-carrying argument would need
`dim Image(G) ≥ dim Image(G′)`, i.e. the `≤` direction of (I3), false in general
and provably false at the `k: 4 → 3` step (`9` down to `4`). At that step the
map's *type* changes: at `k ≥ 4` `V_bc = ker Λ ∩ S_P` with far data entering only
through `Λ` ((T5)); at `k = 3` `V_bc = S_P` is forced, `rank B|_{V_bc} = 2`, and
`V_bc` lies in the discriminant hypersurface of `Gr(3,6)`.

**(3) Does the move preserve the class? No, and (I2) says by how much.** `index`
rises by exactly 1 per split, so the successor is never tight; and by (R3) the
descent hits a rigid `C_{≤6}` after at most `girth − 6` splits, so `hnoRigid`
fails too. The `k = 3` boundary is *exactly* where the split chain plus its
shortest companion closes a rigid `C₆` — which is **(D3)** — so the descent from
the class lands on the **(K-res)** family precisely when `k` reaches 3. That
gives a structural reading of a packaging decision the phase made on other
grounds: the 2026-08-02 route-3(b) adjudication had to carry (K-res) as a
byte-identical `hK` sibling because **(K-res) is the boundary of the class under
the induction's own move**, not merely a residual with the same `dim R_a`.

### Step I6 — the contraction arm has no chart morphism (why C2 inherits the same wall)

`hcontract` is the only arm that can *lower* `index` and hence the only one that
can return to the tight locus. It is unavailable at a class member (`hnoRigid`),
but any *strengthened motive* `P := PencilPair ∧ Inv` must re-establish `Inv`
there. It cannot be done by transport:

> A pencil realization of `G` does **not** induce one of `G/H₀`. Contracting `H₀`
> merges its bodies into one, whose hinges are the `G`-hinges leaving `H₀` —
> sitting at *different* points of `H₀` with *different* panels. For the
> contracted body to be a **pencil** body they must all become concurrent and
> coplanar, a positive-codimension condition on `Chart(G)` that a general
> realization does not satisfy. In the other direction a `G/H₀`-realization does
> not determine the internal geometry of `H₀`.

So the contraction move relates the two charts by **no** morphism in either
direction. This is the structural half of `notes/Pencil-strategy.md` §4-C2's
first bullet: the obstruction is not only that the conjunct would quantify over
subgraphs — it is that the arm which would have to re-establish it has no map to
pull it back along.

**C2 now has a SECOND, independent kill, so this step is no longer the only
reason** (added 2026-09-03, direction DSAT). §(K-dom) *Steps D10–D11*
((DM-6)/(DM-7)) show the strengthened motive is **unsatisfiable at every
realization** at any degree-2 index with `def₃(G − a) − def₃(G) ≥ 4`, and
(DM-8) finds such indices at **both** (K-res) habitats — objects `hK` carries —
and at **none** of the five class habitats. So C2 dies as a *uniform* carry on
satisfiability grounds, quite apart from transport, and *Step I6* is the reason
the **class-restricted** conjunct (which the trace does **not** refute) is still
not dispatchable: the `hcontract` arm has no map to pull it back along. The
deciding row for C2 is therefore **(K-dom)**, not this one; §4-C2's *Row:*
pointer is repointed in the same commit.

### Verification

**No numerics this pass.** (I0)'s Schubert/hyperplane identification is classical
(per the project's "classical" convention); (I1)–(I4), (I3)'s proof and *Step I6*
are derived arguments and carry no driver — a successor should attack them rather
than assume them. What *is* checked against landed source:

- `Graph.pencil_reduction` (`Reduction.lean:850`) — five arms
  (`hloop`/`hbase`/`hcut`/`hcontract`/`hsplit`), the lexicographic `(|V|,|E|)`
  measure, and each non-loop arm handed the IH only at strictly `|V|`-smaller
  graphs.
- **Correction to the record** (coordinator-confirmed, 2026-08-05): the pencil
  side does **not** run KT Theorem 4.9 (`Graph.minimal_kdof_reduction`,
  `Reduction.lean:673`). `pencil_conjecture_of_arms_pair` (`Pair2.lean:1222`)
  instantiates **`Graph.pencil_reduction`** at `P := PencilPair K 3` — five arms,
  no minimality, each arm handed an *arbitrary* smaller graph — and **`hK` enters
  only through `pencilPair_of_splitOff_of_habitat` (`Escape.lean:334`), i.e. only
  in the split arm**. Every statement above is against `pencil_reduction`;
  (I1)/(I2) hold verbatim for `minimal_kdof_reduction` too, since its two moves
  are the same `splitOff` and `rigidContract`.
- `Graph.splitOff` body (`Operations.lean:769`): `V(G) ∖ {v}` plus the fresh
  `a`–`b` edge `e₀`; the definition does **not** require `ab ∉ E(G)` (a split can
  create a parallel pair; irrelevant to (I1)/(I2), which are pure counts).
- `IsNondegPencilRealization` (`Motive.lean:110-115`): conjunct 4 is
  `∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)`. At a
  degree-2 body that is exactly "`pt v`, `pt x`, `pt y` not collinear" — so
  (I3)'s locus `Z` is precisely the conjunct-4 boundary, in the *closure* of the
  nondegenerate chart but not in it. (I3) is stated with that closure,
  deliberately.
- (I1)'s arithmetic against θ(3,4,5), θ(3,3,6), NT16k5, `K4` dbl-subdiv, NT21,
  `K5−M` dbl-subdiv, `P21` — 7/7 — and correctly *failing* at `W19`/`S29`.

**Confidence verdict: the negative is proven-informally** (I0–I2, I4 are counting
and definition-chasing against landed Lean; I5's `k`-drop is (D3) restated).
**The positive by-product (I3) is proven-informally but NOT driver-tested.**

**What would change this.** *(i)* A generating move, not on `pencil_reduction`'s
list, relating two class members — this would require changing the induction
skeleton. *(ii)* A class habitat whose un-subdivision chain stays at `k ≥ 4` all
the way to a shape where dominance is provable; (I4) shows this cannot happen
inside one `G°`, but a proof that some `k ≥ 4` shape is dominant *for a
structural reason* would revive (I3). *(iii)* An error in (I1)'s arithmetic — it
is four lines and cross-checked against seven recorded habitats.

**The one honest well-posed computation this pass identifies, NOT run.** (I3)
predicts a *containment*, hence a falsifiable inequality: take `H₄` := two
`b`–`c` paths of lengths 4 and 4, and `H₅` := lengths 4 and 5 (the `H` of
θ(3,4,5), where `dominance.py --jac` already measures rank 9 in the FIXED
scoping). (I3) asserts `rank dV(H₄) ≤ rank dV(H₅) = 9`, with the sharp
prediction `rank dV(H₄) = 9`; plus `V_bc` on the collinear locus `Z` of `H₅`
equalling `V_bc(H₄)` entry by entry, and `dim V_bc = 3` preserved on `Z`. Cost:
one new mode on `dominance.py`. It confirms (I3) but cannot revive the route,
because (I4) already shows the transport has no class-level consumer — worth
landing only if a successor wants (I3) as a standalone lemma, or wants the
**short-shape-first** disproof search it suggests (a class habitat with
`dim Image < 9` would force `dim Image < 9` at *every* un-subdivision of it, so
an adversarial (K-dom) counterexample hunt should search short shapes and lift).
