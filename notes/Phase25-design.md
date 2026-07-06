# Phase 25 — projective duality + the molecule modelling equivalence: layer design recon

**Status: LIVE** — the layer-level design pass for Phase 25 (opened
2026-07-06, `notes/Phase25.md`), run before any node build per
`DESIGN.md` *Scale-up: design the LAYER, not just the node*. It settles
the phase's two open decisions (OD-25-1, OD-25-2), confirms the
single-integer-phase cut, and re-cuts the blueprint chapter
`blueprint/src/chapter/molecule-modelling.tex` to the corrected shapes.
Once the phase closes, compress closed arcs to verdicts per
`notes/CLAUDE.md` *One canonical home per content type*.

**Audience:** the agent building the first Phase-25 leaf (and every
dispatch that decomposes the chapter into build slices).

**Scope note (user directive, 2026-07-06):** the project formalizes
*every* result it uses — citing or axiomatizing an external is never an
option. OD-25-1 is therefore a **route** question (how to formalize
Crapo–Whiteley's projective invariance, and in what statement shape),
not a formalize-vs-cite question. The Lemma-5.4 precedent (23g's
`cycle_realization`) was itself fully formalized and is the precedent
for exactly this kind of hard geometric brick.

**Source-verified, 2026-07-06.** Every load-bearing claim below was
checked against (i) the papers directly — KT §1.2 (pp. 650–651), the
p. 671 reconciliation, §5.1 (the `c`-map and *nonparallel*, p. 668),
§5.2 (Theorems 5.5/5.6, pp. 669–670); Crapo–Whiteley 1982 §3.6
(pp. 68–69, English column of the OCR'd scan); Jackson–Jordán 2008
(Conjectures 2.1/2.2, Theorems 4.1/4.3 and their §3 machinery) — and
(ii) the landed Lean `def`/`theorem` bodies named inline (file:line as
of `c77853c9`). Where a claim is design-level (a proof sketched here
but not yet machine-checked), it is marked **[design]**.

---

## 0. What Phase 25 must deliver, in one paragraph

KT §1.2 / p. 671: in `ℝ³` the chain *bar-joint of `G²` ↔ molecular
(hinge-concurrent body-hinge) of `G` ↔ panel-hinge of `G`* lets the
panel-hinge rank theorem (Thm 5.6, Phase 23) speak about the
3-dimensional generic bar-joint rank of the square graph (Phase 24's
`genericRank`), producing Corollary 5.7:
`r(G²) = 3|V| − 6 − def(G̃)` for `G` simple of min degree ≥ 2
(Jackson–Jordán's statement; KT resolve the conjecture feeding it).
Phase 25 owns the two links of the chain; Phase 26 assembles.
**The recon's central verdict (§2): both links must be delivered at
the *rank/motion-space* level, not the realizability-iff level** — the
iff-level chain cannot reach Cor 5.7 without formalizing most of two
further Jackson–Jordán papers (§2.1), while the rank-level chain closes
on machinery already in tree.

---

## 1. OD-25-1 — the projective-invariance route (`thm:projective-invariance`)

### 1.1 What the sources actually say

Crapo–Whiteley 1982 §3.6 (*Projective transformations*, verified
against the OCR'd scan, English text on pdf p. 26): a non-singular
collineation "is expressed by a non-singular linear transformation on
the projective coordinates of the points. This transformation induces a
linear transformation on the vector space of screws and lines which
will carry a panel structure to a new panel structure by transforming
the hinges. This linear map will transform an instantaneous motion into
an instantaneous motion. Since the collineation has an inverse, we
conclude that the instantaneous motions and infinitesimal rigidity of a
panel structure are projectively invariant." The next paragraph extends
this verbatim to **correlations/polarities** (point ↔ plane duality
maps): "Once more the maps preserve instantaneous motions and have
inverses, so the infinitesimal rigidity of a panel structure is
invariant under the correlations."

That is: CW's *proof* is exactly "a projective transformation (or
polarity) induces an invertible linear map on the screw space; applying
it bodywise carries motions to motions." KT use [4, §3.6] twice — in
Thm 5.6's proof (to make panels pairwise intersect; the landed 22k
proof is projective-move-free, so **no debt there**) and at the p. 671
duality (a *correlation*, carrying panels to points).

### 1.2 Verdict: formalize as the extensor-transport lemma family

The landed rigidity theory reads a framework entirely through its
supporting extensors: `BodyHingeFramework k α β` is
`(graph, supportExtensor : β → ScrewSpace k)`
(`Molecular/RigidityMatrix/Basic.lean:307`), and every motion/rank
notion is built from `hingeConstraint S e u v ↔ S u − S v ∈
span ℝ {supportExtensor e}` (`Basic.lean:406`). So CW §3.6's argument
formalizes as a **transport lemma**, with no analytic projective
geometry at all:

```lean
/-- Transport a body-hinge framework along a linear automorphism of the
screw space (CW 1982 §3.6: the linear map a projective transformation
or polarity induces on screws). -/
def BodyHingeFramework.mapExtensor (F : BodyHingeFramework k α β)
    (Λ : ScrewSpace k ≃ₗ[ℝ] ScrewSpace k) : BodyHingeFramework k α β where
  graph := F.graph
  supportExtensor e := Λ (F.supportExtensor e)

theorem BodyHingeFramework.infinitesimalMotions_mapExtensor
    (F : BodyHingeFramework k α β) (Λ : ScrewSpace k ≃ₗ[ℝ] ScrewSpace k) :
    (F.mapExtensor Λ).infinitesimalMotions
      = F.infinitesimalMotions.map
          (LinearEquiv.piCongrRight fun _ : α => Λ : (α → ScrewSpace k) ≃ₗ[ℝ] _)
```

**[design]** proof: `Λ S u − Λ S v = Λ (S u − S v)` and
`Λ (span {C}) = span {Λ C}` — a `Submodule.map_span`-level argument.
Corollaries (each a 2-liner): `finrank` of the motion space is
preserved (`LinearEquiv.finrank_eq` on the mapped submodule);
`RankHypothesis k'` transfers; `IsInfinitesimallyRigid` transfers
(trivial motions are the *constant* assignments, `Basic.lean:2126`, and
`piCongrRight Λ` carries constants to constants);
`IsInfinitesimallyRigidOn s` transfers; genuine hinges transfer
(`Λ C ≠ 0 ↔ C ≠ 0`).

This is the full strength the program consumes from CW §3.6, faithful
to CW's own proof structure (the induced linear screw map), and it is
dimension-general for free. **It is deliberately NOT a theory of
projective transformations acting on `ℝ³` bar-joint frameworks** — no
consumer anywhere in the program (checked: Thm 5.6 landed
projective-move-free; the p. 671 use is the polarity, handled in §1.3;
the bar-joint side of Cor 5.7 never moves projectively). The blueprint
node keeps the label `thm:projective-invariance` and the CW citation,
restated in this transport form; the reshaped chapter (this commit)
carries it.

A second, small transport sibling is needed once (§3, W2c): motions are
also unchanged under **per-edge nonzero rescaling** of the support
extensors (`span {c • C} = span {C}` for `c ≠ 0`) — the normalization
step from projective (homogeneous) to affine data.

### 1.3 The polarity itself is already in tree

The landed panel layer factors through the projective polarity already:
`panelSupportExtensor n₁ n₂ = complementIso (normalsJoin n₁ n₂)`
(`PanelLayer.lean:232`), where `normalsJoin n₁ n₂ =
exteriorPower.ιMulti ℝ 2 ![n₁, n₂]` is the **join** (wedge) of the two
normal 4-vectors and `complementIso (j := 2) :
⋀[ℝ]²(Fin (k+2) → ℝ) ≃ₗ[ℝ] ⋀[ℝ]^k (Fin (k+2) → ℝ)` (`Meet.lean:471`)
is a *fixed linear equivalence* — at `k = 2` an automorphism of
`⋀²(ℝ⁴)`. Under the standard polarity (KT §5.1's convention: the panel
`Π(v) = {x : x·c(v) + 1 = 0}` has homogeneous plane coordinates
`(c(v), 1)`, which are *also* the homogeneous point coordinates of its
pole `c(v)` — `homogenize` in `Extensor.lean:110` is exactly
`Fin.snoc · 1`), the dual line of the panel-meet `Π(u) ∩ Π(v)` is the
join of the poles — and that is literally the equation above with
`Λ := complementIso` (wrapped through `ScrewSpace.equivExteriorPower`,
`Basic.lean:183`, into a `ScrewSpace 2 ≃ₗ ScrewSpace 2`). So
`lem:panel-hinge-dual-molecular` needs **no new duality machinery**:
the 21a/22f meet layer already carries it.

---

## 2. OD-25-2 — the `G²` dictionary must be rank-level (the central verdict)

### 2.1 Why the realizability-iff shape is a dead end for Cor 5.7

The chapter as opened stated `thm:molecular-iff-square-bar-joint` as a
realizability iff (rigid molecular realization exists ⟺ rigid
bar-joint realization of `G²` exists) — Whiteley's unpublished [35]
statement as KT p. 671 quotes it. **Verified against JJ 2008:** the
step from that iff to the *rank formula* is NOT free. JJ 2008 prove
(their Theorem 4.3, p. 10) that the iff-level Molecular Conjecture
(their Conjecture 2.1) implies the rank formula (their Conjecture 2.2 =
KT Cor 5.7) by an induction on `def(G)` that consumes:

- **Theorem 4.1** (p. 9): the *unconditional* upper bound
  `r(G²) ≤ 3|V| − 6 − def(G)`, whose proof runs through independent
  2-thin covers — their Lemma 3.1 is quoted from **another paper**
  ([5, Lemma 3.2], the JJ *d-dimensional rigidity matroid of sparse
  graphs* machinery) plus their Theorem 3.4 (brick partitions, quoted
  from [10], a third paper);
- brick partitions, ear attachment (`ux₁x₂x₃x₄u′`), Claim 4.4, and
  vertex-addition rank lemmas for squares (their Lemma 3.3, Franzblau's
  Lemma 4.2(a)).

Reaching Cor 5.7 through that route means formalizing the better part
of two further JJ papers of genuinely new combinatorial matroid theory.

### 2.2 The rank-level route closes on landed machinery

KT's p. 671 sentence — "it follows from Theorem 5.6 that a simple graph
`G` can be realized as a molecular framework `(G,p)` which satisfies
`rank R(G,p) = D(|V|−1) − def(G̃)`" — points at the escape: Thm 5.6 is
a *rank* statement, strictly stronger than the def-0 iff, and the
project owns it (`rankHypothesis_of_theorem_55_d3`,
`Theorem55.lean:2840`: `∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
Q.toBodyHinge.RankHypothesis (G.deficiency 3)`, i.e.
`dim Z = D + def`). If the two Phase-25 links carry *motion-space
dimensions* (equivalently ranks) rather than just rigidity, Cor 5.7
falls out arithmetically:

- **(≥, attainment)** Thm 5.6 (in a general-position form, §2.4) gives
  a nonparallel panel realization at `dim Z = 6 + def(G̃)`; the §1.3
  polarity transport gives a **molecular** realization at the same
  `dim Z`, hinges the lines through the poles `c(v)`; the dictionary
  iso Φ (§2.3) then exhibits a bar-joint placement `c` of `G²` with
  `dim ker R(G², c) = 6 + def`, i.e. rank `3|V| − 6 − def`; and
  `genericRank` dominates the rank at any placement (matroid glue,
  Phase 26).
- **(≤, upper bound)** at a placement `p` that is simultaneously
  generic (Phase 24 `IsGenericPlacement`) and in general position
  (§2.5), `genericRank = rank R(G², p)`
  (`genericRank_eq_finrank_span`, `GenericRigidityMatroid.lean:241`);
  the dictionary iso Φ run in reverse identifies
  `dim ker R(G², p) = dim Z` of the molecular framework with hinges
  `p(u)p(v)`, whose hinges are genuine (`p` injective); and the landed
  genericity-free lower bound
  `D + def(G̃) ≤ dim Z` (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`,
  `PanelLayer.lean:2083`, hypotheses `[Nonempty α] [Finite α] [Finite β]`
  + genuine hinges — **no rigidity, no genericity**) closes
  `genericRank ≤ 3|V| − 6 − def`. **This replaces JJ's whole §3–4.**

No 2-thin covers, no bricks, no ear induction, no new combinatorics.
Both directions consume the *same* dictionary iso Φ, which is the
phase's crux and gets the full leaf decomposition below.

### 2.3 The dictionary iso Φ, traced to ground **[design]**

Fix `G` simple on `V`, min degree ≥ 2, and a placement `c : V → ℝ³`
in *general position up to order 4* (every ≤ 4-point subfamily affinely
independent; §2.5). Let `M_c` be the molecular framework: the
`BodyHingeFramework 2` on (a `Graph`-carrier of) `G` with
`supportExtensor e := ScrewSpace.mk (affineSubspaceExtensor ![c u, c v])`
at `ends e = (u,v)` — i.e. `BodyHingeFramework.ofHinge`
(`Basic.lean:382`) with hinge points the two endpoint centres. Note
`affineSubspaceExtensor ![c u, c v] = extensor ![homogenize (c u),
homogenize (c v)]` (`Extensor.lean:380`) — **the same object** the §1.3
polarity produces from panel normals with last coordinate 1, so the two
links of the chain compose with no translation layer (binding-clause
(iii) check).

The two motion spaces:

- body-hinge: `S : V → ScrewSpace 2` with
  `S u − S v ∈ span {C(c u, c v)}` per edge (`infinitesimalMotions`,
  `Basic.lean:1021`);
- bar-joint: `x : V → ℝ³` with `⟪c u − c v, x u − x v⟫ = 0` per edge of
  `G²` (`ker (G².RigidityMap c)`, `Framework.lean:98`; `EuclideanSpace ℝ
  (Fin 3)` vs `Fin 3 → ℝ` is PiLp-coercion glue at the boundary).

**Φ : S ↦ (v ↦ vel_{S v} (c v))**, where `vel : ScrewSpace 2 → (ℝ³ → ℝ³)`
is the screw's velocity field (§3 W1: linear in `S`; concretely
`vel_S x = ω_S ×₃ x + t_S` with `(ω_S, t_S)` the graded Plücker
coordinates of `S`; for a line 2-extensor,
`vel_{â∨b̂} x = (b−a) ×₃ x + a ×₃ b`).

Ground facts making the two index families correspond (each a W1 brick,
elementary cross-product algebra):

1. *(skew)* `⟪x − y, vel_S x − vel_S y⟫ = 0` for all `S, x, y`.
2. *(line characterization)* for `a ≠ b`:
   `vel_S a = 0 ∧ vel_S b = 0 ↔ S ∈ span ℝ {mk (extensor ![â, b̂])}`.
   (⟸: `vel_{â∨b̂}` vanishes at `a, b` by the formula. ⟹: `vel_S a = 0`
   forces `t = a × ω`; then `vel_S b = ω × (b − a) = 0` forces
   `ω ∥ b − a`; the span is 1-dimensional.)
3. *(kill)* `vel_S` vanishing at three non-collinear points forces
   `S = 0` (from 2: `ω` parallel to two independent directions).
4. *(body determination)* if a finite point family contains three
   non-collinear points, every further point is affinely independent
   from each triple (the ≤ 4 general-position hypothesis), and
   `x` satisfies all pairwise bar constraints on the family, then
   `∃! S, ∀ i, vel_S (p i) = x i`. (Triangle case: the map
   `S ↦ (vel_S q₀, vel_S q₁, vel_S q₂)` is injective by 3 from the
   6-dimensional `ScrewSpace 2` (`screwSpace_finrank`, `Basic.lean:209`)
   into the ≥/= 6-dimensional constrained space — rank `R(K₃)` = 3 at a
   non-collinear triangle — so it is onto. Extra points `w`: subtract
   the triangle's screw; the residual velocity at `w` is orthogonal to
   `w − qᵢ`, `i = 0,1,2`, which span `ℝ³` by affine independence of
   `{w, q₀, q₁, q₂}`, so it is zero. **The coplanar-`K₄` flex is the
   sharp counterexample** — 4 coplanar points admit the vertical flex —
   which is exactly why the placement condition must be affine
   independence up to order **4**, not injectivity + non-collinearity.)

**Φ lands in the bar-joint motions:** for `uv ∈ E(G)`,
`x u − x v = vel_{S u}(c u) − vel_{S u}(c v) + vel_{S u − S v}(c v)`;
the first difference is `⟂ (c u − c v)` by (1), the second term is `0`
by (2) applied to the hinge constraint. For a distance-2 edge `uw` via
`v`: `u, w ∈ N[v]`, and (2) gives `vel_{S u}(c u) = vel_{S v}(c u)`
(the hinge `c(u)c(v)` vanishes `S u − S v` at `c u` too), likewise at
`w`, so `x u − x v ... = vel_{S v}(c u) − vel_{S v}(c w) ⟂ (c u − c w)`
by (1). This is where `E(G²) = E ∪ {distance-2}` is consumed, edge
family to edge family — every `G²`-edge lies inside some closed
neighborhood clique `N[v]`, and the constraint is discharged by body
`v`'s single screw.

**Φ is injective on motions:** `Φ S = 0` gives `vel_{S v}(c v) = 0`;
for `u ∼ v`, (2) on the hinge plus `vel_{S u}(c u) = 0` gives
`vel_{S v}(c u) = 0`; min degree ≥ 2 gives ≥ 3 such points per body,
non-collinear by general position, so (3) kills each `S v`.

**Φ is surjective onto `ker R(G², c)`:** given a bar-joint motion `x`,
each closed neighborhood `N[v]` is a clique of `G²` (this is the
KT-p. 650 sentence "in the square of a graph a vertex and its neighbors
form a complete graph"), so `x` restricted to `c(N[v])` satisfies all
pairwise constraints; (4) with `|N[v]| ≥ 3` gives a unique `S v` with
`vel_{S v} = x` on `c(N[v])`. Hinge constraints: for `uv ∈ E`,
`vel_{S u − S v}` vanishes at `c u` and `c v` (both `∈ N[u] ∩ N[v]`,
both velocities pinned to `x u`, `x v`), so (2) puts `S u − S v` in the
hinge span. `Φ S = x` since `v ∈ N[v]`.

Endpoint: `dim Z(M_c) = dim ker R(G², c)`, hence
`rank R(G², c) = 3|V| − dim Z(M_c)` by rank–nullity
(`Framework.finrank`, `Framework.lean:67`).

### 2.4 The ≥ leg needs a general-position form of Thm 5.6 (W6)

The landed `rankHypothesis_of_theorem_55_d3` output says nothing about
the normals, but the dictionary needs the *poles* (normals read as
homogeneous points) affine (`n_v` last coordinate ≠ 0), and in general
position up to order 4. **Verified route on landed machinery**, all in
`GenericityDevice.lean` / the `Matrix/Rank.lean` mirror:

1. From `RankHypothesis (def)`: `finrank span rigidityRows =
   D(|V|−1) − def` via the complement identity
   `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`
   (`GenericityDevice.lean:503`).
2. Extract a literal independent `panelRow` subfamily of that size:
   `exists_independent_panelRow_subfamily_of_le_finrank`
   (`GenericityDevice.lean:718`; hypotheses only linking-`ends` +
   linking transversality).
3. Turn it into a **rank polynomial** in the normal coordinates:
   template `exists_rankPolynomial_of_rigidOn`
   (`GenericityDevice.lean:1303`) — its proof consumes rigidity *only*
   to get the full-size subfamily, so a `RankHypothesis (def)`-seeded
   sibling with target size `D(|V|−1) − def` is a near-verbatim
   restatement on top of step 2. The B0 coordinatization
   (`annihRowPoly`, the `g/c/φ/hg` package) is reused as-is.
4. Multiply by the **general-position avoidance polynomial**: the
   product, over vertex tuples, of (last-coordinate variables
   `X (a, 3)`) × (sums of squares of the `2×2`/`3×3` minors of the
   normal-variable matrices) × (`4×4` determinants). Each factor is a
   nonzero polynomial — witnessed by normals
   `homogenize (t_a, t_a², t_a³)` at distinct parameters (Vandermonde);
   the product is nonzero over the domain `ℝ[σ]`, and
   `MvPolynomial.exists_eval_ne_zero`
   (`Mathlib/Algebra/MvPolynomial/Funext.lean:40`) produces a point
   `q*` where the rank polynomial and every avoidance factor are
   simultaneously nonzero. (This mirrors exactly the multiply-legs
   pattern the 22-era witness transfer used; the doc comment at
   `Matrix/Rank.lean:1046` names it.)
5. At `q*`: rows LI ⟹ `dim Z ≤ D + def` (step-1 identity read
   backwards, `panelRow_mem_rigidityRows_of_link`); genuine hinges
   (from pairwise normal independence) ⟹ the landed genericity-free
   bound `D + def ≤ dim Z` (`PanelLayer.lean:2083`); so
   `RankHypothesis (def)` holds at `q*` **with** poles affine and in
   general position up to order 4.

KT compress this entire strengthening into the word "nonparallel" (and
Whiteley's [35] manuscript is unpublished) — flag for
`notes/BlueprintExposition.md` at phase close.

### 2.5 The ≤ leg needs a general-position generic placement (W5)

Phase 24's `IsGenericPlacement` (`GenericRigidityMatroid.lean:49`) does
not give injectivity, let alone order-4 affine independence. Define

```lean
def IsGeneralPositionPlacement (p : V → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ s : Finset V, s.card ≤ 4 → AffineIndependent ℝ (fun i : s => p i)
```

and strengthen the Phase-24 existence proof: `∃ p, IsGenericPlacement p
∧ IsGeneralPositionPlacement p`. The proof re-runs
`exists_isGenericPlacement`'s finite-family induction
(`GenericRigidityMatroid.lean:67`) with the affine-independence
conditions added to the avoided sets: along the interpolation path
`p₀ + t • r`, each ≤ 4-tuple's affine independence is the
non-vanishing of a polynomial in `t`, nonzero at a moment-curve
witness, so it contributes finitely many bad `t` (the scalar-polynomial
sibling of `LinearIndependent.finite_setOf_not_along_affine_path`).
**[design]** — the packaging may prefer a one-shot "avoid finitely many
proper subvarieties along a path" helper; builder's choice.

### 2.6 Statement shapes Phase 26 will consume

Phase 25's two endpoint theorems (chapter nodes
`thm:molecular-iff-square-bar-joint` + `thm:panel-hinge-iff-molecular`,
restated rank-level):

```lean
-- the dictionary (both legs consume this one iso, W4):
theorem molecular_finrank_motions_eq_square_ker
    [Fintype V] {G : SimpleGraph V} (hdeg : ∀ v, 2 ≤ G.degree v)
    {β : Type*} [Finite β] {G' : Graph V β} {ends : β → V × V}
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    {c : V → EuclideanSpace ℝ (Fin 3)} (hgp : IsGeneralPositionPlacement c) :
    Module.finrank ℝ (molecularOfCentres G' ends c).infinitesimalMotions
      = Module.finrank ℝ (LinearMap.ker (G.square.RigidityMap c))

-- the panel ↔ molecular rank carry (W2 + W6 composed):
theorem exists_molecular_rankHypothesis_generalPosition (…) :
    ∃ (ends : β → α × α) (c : α → Fin 3 → ℝ),
      (molecularOfCentres G ends c).RankHypothesis (G.deficiency 3)
      ∧ IsGeneralPositionPlacement c   -- (poles of the §2.4 normals)
```

(Exact binder shapes are the builder's; the load-bearing content is:
the dictionary is an equality of motion-space dimensions at a shared
placement `c`, the molecular producer outputs `RankHypothesis` at
`deficiency 3` *plus* the general-position side conditions the
dictionary needs. `hshadow` ties the `Graph`-carrier to the
`SimpleGraph` without a general bridge API; whether Phase 26 instead
builds a small `SimpleGraph → Graph` constructor is deferred to its
open — flag, not a blocker.)

Phase 26 then owns: `SimpleGraph.square`'s `genericRank` glue
(rank-at-a-placement ≤ `genericRank`, via a matroid base transported
through `genericRigidityMatroid_indep_iff`), the `β`-label supply for
Thm 5.6 (`hcard : 6 (|α| − 1) < |β|`), the carrier bridge, and the
Cor 5.7 statement (additive form; attribute the formula to
Jackson–Jordán 2008, conjecture-resolution to KT).

---

## 3. Leaf decomposition (the build order)

All at `d = 3` (`k = 2`) per the phase's scope choice. New Lean lives
in a new file (suggested `Molecular/Molecule/Dictionary.lean`, plus
`Molecular/Molecule/ScrewVelocity.lean` for W1 if it grows); the square
graph on the `SimpleGraph` side (suggested near `Framework.lean`'s
consumers, new file `SquareGraph.lean`).

| # | Leaf | Content | Reuse anchor | Grade |
|---|---|---|---|---|
| W1 | screw-velocity API | `vel` (concrete, via `screwBasis`/cross product `Mathlib.LinearAlgebra.CrossProduct`), bricks (1)–(4) of §2.3 | `screwBasis` (`PanelLayer.lean:1429`), `ScrewSpace.mk/val`, `extensor` | **crux**, elementary but fiddly; 1–2 sessions |
| W2 | extensor transport (`thm:projective-invariance`) | `mapExtensor` + motions/finrank/`RankHypothesis`/rigidity corollaries; (W2c) per-edge nonzero rescaling invariance | §1.2; `infinitesimalMotions` | small |
| W3 | square graph | `SimpleGraph.square`, closed-neighborhood cliques, every `G²`-edge in some `N[v]`, min-degree transfer | mathlib `SimpleGraph` | small |
| W4 | dictionary iso Φ | §2.3 end-to-end (well-defined, injective, surjective, finrank equality); PiLp boundary glue | W1, W3, `ofHinge` | **crux**; 2–4 sessions |
| W5 | general-position placements | `IsGeneralPositionPlacement`, moment-curve witness, strengthened `exists_isGenericPlacement` | `GenericRigidityMatroid.lean:67` | 1 session |
| W6 | Thm 5.6, general-position form | §2.4 route 1–5 (deficiency-grade rank polynomial + avoidance product) | `GenericityDevice.lean:503/718/1303`, `Funext.lean:40` | moderate; 1–2 sessions |
| W7 | dual correspondence + endpoints | `molecularOfCentres`; `lem:panel-hinge-dual-molecular` via `Λ := complementIso` (§1.3); the two §2.6 endpoint theorems | W2, W6, `panelSupportExtensor`, `normalsJoin_coe` | small–moderate |

Dependency order: W2, W3, W5 are independent leaves (start anywhere);
W1 → W4; W6 independent; W7 last. The two cruxes (W1, W4) carry the
genuinely new geometry; everything else is composition on landed
machinery.

## 4. Phase-cut and chapter verdicts

- **Single integer phase, confirmed.** W1–W7 is one coherent chain
  (~6–10 sessions), not the multi-body bundles that sub-lettered
  Phases 22–23; the opening default stands. Re-cut on contact if W4
  splits badly.
- **Blueprint chapter re-cut in this commit** (12 nodes; same file).
  The two theorem nodes restate at rank level (§2.6); the
  realizability-iff forms KT/Whiteley state survive as corollary
  prose, not the load-bearing nodes. `thm:projective-invariance`
  restates in transport form (§1.2). New leaf nodes for W1
  (`def:screw-velocity`, `lem:screw-velocity-line`,
  `lem:screw-determination`), W5 (`def:general-position-placement`,
  `lem:exists-generic-general-position`), and W6
  (`lem:theorem-56-general-position`). All red (no `\lean` pins yet).
- **No cite-fallback anywhere**: every node above is scheduled for full
  formalization; W1's cross-product bricks and W4 are the "hard
  geometric content" analogues of 23g's `cycle_realization`.

## 5. Open decisions / honest flags

- **(F1)** The W6 template restatement (§2.4 step 3) was verified
  against `exists_rankPolynomial_of_rigidOn`'s *proof body* (it uses
  rigidity only through the N7b-0 subfamily extraction), but the
  deficiency-grade variant is not machine-checked; if the linking-edge
  span identity (`span_panelRow_linking_eq_rigidityRows`) needs
  all-`β` hypotheses the Thm 5.6 output can't supply, fall back to the
  `_linking` sibling (`GenericityDevice.lean:1396`) — both variants
  exist.
- **(F2)** The triangle-onto step of §2.3 brick (4) needs
  `rank R(K₃) = 3` at a non-collinear triangle on the *bar-joint* side
  — a small new `Framework.lean`-adjacent lemma; if the direct row
  computation is unpleasant, the dimension count via
  `IsInfinitesimallyRigid` of the triangle works too. Not a route
  risk, just unscheduled glue.
- **(F3)** `EuclideanSpace ℝ (Fin 3)` ↔ `Fin 3 → ℝ` PiLp glue at the
  W4 boundary: known-idiom friction, budget a slice for it.
- **(F4)** The `hshadow`-vs-carrier-bridge choice (§2.6) is deferred
  to Phase 26's open; the dictionary is stated so either works.
- **(F5)** Whiteley's [35] (*The equivalence of molecular rigidity
  models…*, manuscript 2004) is unpublished and not in `.refs/`; the
  §2.3 proof is reconstructed from KT's p. 650 sketch + JJ 2008's §2.1
  description and verified internally here, not against [35]. The
  chapter attributes the equivalence to Whiteley (via
  \cite{whiteley1999}'s published treatment and JJ 2008 as the citable
  anchors), and the *proof written here is the project's own
  reconstruction* — exposition-ledger candidate at phase close.
