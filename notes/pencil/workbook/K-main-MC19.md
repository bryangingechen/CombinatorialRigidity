## §(K-main) — Step MC19 — the generic motive: feasibility, the hub-plane chart, and the reduction to (MC-10)(a)

#### Step MC19 — the generic motive: feasibility, the hub-plane chart, and the reduction to (MC-10)(a)

*Worked 2026-09-24 by a read-only agent (W4-reopen P1, open direction 5, "outside `X₀`"; the third
2026-09-24 session's Track E). **Second-read 2026-09-25** by a fresh reader, who re-derived every
claim and opened every Lean predicate's definition body (the readings match). No refutation. One
real gap: (MC-130)'s proof sent cycles to (MC-128)(b), whose base is a ℚ-exact certificate, so the
reduction was not hypothesis-free as stated; it is repaired in place (cycles `C_n`, `n ≥ 4`, are base
graphs). The other repairs are precision and scope, each marked where it sits. The reader added
(MC-157), `HasDistinctPencilRealization` at every graph satisfying (H) with no feasibility
hypothesis, and (MC-158), the bridged populations the other drivers exclude (`w4/zbridged.py`).
Two different 46s: (MC-125)'s 46 is the feasible non-A′ graphs of `exh8`; (MC-130)'s is the
feasible `exh8` graphs with a `def₂`-rigid subgraph, the 33 A′ ones plus 13 non-A′. Drivers `w4/zcore.py` (shared core),
`w4/zsurvey.py`, `w4/e3check.py`, `w4/zears.py`, `w4/zlemma.py`, `w4/zdirect.py`, `w4/zk2k.py`,
`w4/zrand.py`, `w4/zstuck.py` (new). The Lean objects are read from their definition bodies in
`Motive.lean`: `IsNondegPencilRealization`, `PencilNondegFeasible`, `HasGenericPencilRealization`,
`PencilPair`, `Graph.PencilHub`, `Graph.closedHubNbhd`.*

**Verdict.** The A′ exposure (MC-9) is **not** an extra obstruction.
- **Feasibility, characterized** (MC-123): a simple graph over an infinite field is
  `PencilNondegFeasible` iff (F1) every hub has at most 2 hub neighbours and (F2) no triangle contains
  two hubs. This weakens L6b's triangle-freeness to (F2).
- **One irreducible family carries every nondegenerate realization** (MC-124): the hub-plane chart
  `Z(G)`. The generic motive holds iff one point of `Z(G)`'s closure, with adjacent points distinct,
  attains the target. At `K_{2,3}`, `Z` is (MC-9)'s jump stratum. Where `X₀` is nondegenerate,
  `X₀ = Z(G)` (MC-125).
- **Ears transfer to `Z`** (MC-126), with dominance automatic. Three reduction steps (MC-127),
  together with (MC-129), give **the reduction theorem** (MC-130): the generic motive at every
  feasible simple graph satisfying (H) reduces, with no hypothesis, to feasible graphs with no
  `def₂`-rigid subgraph. On those graphs `X₀` is nondegenerate ((MC-14), modulo Jackson–Jordán), so
  the base is (MC-10)(a). Every `K_{2,k}` has the generic motive over every infinite field (MC-128).
- **With (MC-89)** (coordinator's combination, (MC-133)): every feasible simple connected graph of
  minimum degree `≥ 2` has the generic pencil motive, modulo Jackson–Jordán, in characteristic 0.

> **(MC-133)** `[PROVED-MOD]` *((MC-33); the coordinator's combination of (MC-130) with (MC-89) and
> (MC-14); Step MC19 second-read 2026-09-25, confirmed with repairs)* Let `K` have characteristic 0 and let
> `G` be finite, simple and connected, with minimum degree `≥ 2`.
> **(i)** `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` ((MC-89)). It gives a
> rank-attaining pencil configuration with adjacent points distinct ((MC-2)): the rank and
> distinctness content of `HasDistinctPencilRealization K 3 G`.
> **(ii)** If `G` is `PencilNondegFeasible` ((MC-123): (F1) and (F2)), then `HasGenericPencilRealization
> K 3 G`.

*Proof of (ii).* By (MC-130) it suffices to treat feasible `G°` satisfying (H) with no `def₂`-rigid
subgraph. There (F1) holds and no `def₂`-rigid subgraph contains two hubs of a common
`closedHubNbhd`, so `X₀(G°)`'s generic point is nondegenerate ((MC-14), mod JJ). By (MC-89) it
attains. Both are dense open conditions on the irreducible `X₀(G°)`, so one point has both, and
(MC-124)(ii) applies (`X₀(G°) = Z(G°)` by (MC-125)(ii)). ∎ *(Second reading: the final appeal to
(MC-124)(ii)/(MC-125)(ii) is unnecessary, since the `X₀` point is already a Lean witness.)*

*Scope (second reading, 2026-09-25).* (ii) supplies `PencilPair`'s generic conjunct
`G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G` only at `n = 3`, only at
graphs satisfying (H), and only for `K` of characteristic 0. The Lean predicates carry no
connectivity, minimum-degree or vertex-count condition, and the consumers (`Escape.lean`) take
`[Infinite K]`. Beyond characteristic 0, each input is available modulo (MC-33)(i): (MC-130) is
characteristic-free (after its cycle bullet's repair), (MC-89) holds via (MC-141), and (MC-14) holds
via (MC-13)(c)'s own field note.

*The Lean route (2026-09-28, MOTIVES recon):* (ii) is proved inside the pencil reduction's induction,
not by (MC-130)'s own; see *Route B* below, (MC-183)–(MC-189), second-read 2026-09-28, and EARS'
(MC-190)–(MC-192), 2026-09-29, awaiting a second read. The planned fibre argument from (i) alone
fails at A′ graphs ((MC-187)).

> **(MC-157)** `[PROVED-MOD]` *((MC-33); from (MC-89); the second reader's, 2026-09-25; strengthens
> (MC-133)(i))* Let `K` have characteristic 0, let `G` satisfy (H), and let `α`, `β` be finite. Then
> **`HasDistinctPencilRealization K 3 G`**. Feasibility is not needed. This is `PencilPair`'s second
> conjunct at the graphs satisfying (H).

*Proof.*
- Take a `K`-point `(q, z)` of `X₀(G)` at which the rank attains. It exists by (MC-89): the attaining
  points are a dense open subset of `X₀`, and `K`-points are dense.
- Put `point v := (x_v, y_v, z_v, 1)`, and let `normal v` be the normal of the plane `π_v ⊇ p(N[v])`,
  which exists and is unique by (MC-1).
- Put `supportExtensor e := extensor ![p_u, p_v]` for a fixed orientation of each link, and any
  nonzero value off `E(G)`.
- `HasPencilPanelRealization` holds: `p_u, p_v ∈ π_u ∩ π_v` for every edge; `p_v ∈ π_v`; points and
  normals are nonzero; the extensor is nonzero because `q_u ≠ q_v`.
- Adjacent points are independent, for the same reason.
- The rank is `≥` the target at the chosen point, and `≤` it by the landed
  `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`. ∎

**The hub-plane chart.**

**Notation.** Put `Hub := {v : deg v ≥ 3}` and `C(v) := closedHubNbhd v = Hub ∩ N[v]`. For
normals `n = (n_h)_{h ∈ Hub}` in `K⁴`, put `F_v(n) := ⋂_{h ∈ C(v)} n_h^⊥`. Define
`Y′_3(G) := {(n, p) : {n_h : h ∈ C(v)} independent for every v; p_v ∈ F_v(n) for every v}`
(points `p_v ∈ K⁴`), and let `Z(G)` be its Zariski closure.

**Observation (what a realization is).** Let `(normal, point)` be a pencil panel realization with
adjacent points independent (conj. 2). Then:
- Each support extensor is forced to be `p_u ∧ p_v`: it is a nonzero decomposable extensor
  through both points.
- Conjunct 1 then says exactly that `n_v ⊥ p_w` for every `w ∈ N[v]`.
- Conjunct 3 involves only hub normals, because `C(v) ⊆ Hub`. Conjunct 4 involves only points.
  The rank involves only points.
- A non-hub's normal is any nonzero vector orthogonal to the at most 3 points of `N[v]`, and such
  a vector always exists.

So a realization with conjuncts 1–3 is exactly a point of `Y′_3(G)` with adjacent points
independent, together with an arbitrary choice of non-hub normals.

> **(MC-123)** `[PROVED]` *(feasibility, characterized)* Let `K` be infinite and `G` finite and simple.
> Then `PencilNondegFeasible K G` **iff (F1)** every hub has at most 2 hub neighbours (equivalently,
> every `|closedHubNbhd v| ≤ 3`) **and (F2)** no triangle contains two hubs.

*Proof.* (⇒) (F1) is `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`. It is stated
under `[Finite α]`; for a finite `G` in a larger `α` the same argument runs on the finite set
`closedHubNbhd v ⊆ V(G)`. (F2) is `not_pencilNondegFeasible_of_triangle_two_hubs`: any two vertices
of a triangle are adjacent, so its hubs `y`, `z` can be any two hubs of the triangle. Both are landed
Lean theorems, and neither has a hypothesis on `K`. *(Precision repair, second reading 2026-09-25.)*

(⇐) Take hub normals on the moment curve, `n_h = (1, t_h, t_h², t_h³)`, with distinct `t_h`, so that
any four of them are independent. This gives three facts:
- **(g1)** `dim F_v = 4 − |C(v)| ≥ 1`.
- **(g2)** If `S ≠ T` are sets of hubs of size at most 3, then `span n_S ≠ span n_T`. Pick `h` in the
  symmetric difference, say `h ∈ T ∖ S`. Then `S ∪ {h}` is independent, so `n_h ∉ span n_S`.
- **(g3)** If `h ∉ S` and `|S ∪ {h}| ≤ 4`, then `F_S ⊄ n_h^⊥`.

With `n` fixed, the points range over the vector space `Φ := ∏_v F_v`. Every condition below is
the nonvanishing of a minor, so it is Zariski-open in `Φ`. A finite intersection of nonempty open
subsets of `Φ` is nonempty because `K` is infinite, so it suffices to show that each condition
holds somewhere.
- **`p_v ≠ 0`.** Clear.
- **Conjunct 2 at an edge `uv`.** This fails everywhere only if `F_u = F_v` is 1-dimensional. By
  (g2) that means `C(u) = C(v)`, both of size 3. A non-hub has `|C| ≤ 2`, so `u` and `v` are both
  hubs. Then `C(u) = {u, v, w}` and `C(v) = {u, v, w}`, so `uvw` is a triangle of hubs, which (F2)
  excludes.
- **Conjunct 4 at a degree-2 vertex `v` with neighbours `a`, `b`.**
  - First choose `p_a` and `p_b` independent. The obstruction would be `F_a = F_b` 1-dimensional,
    that is, `C(a) = C(b)` of size 3. Then `a ∈ C(b)`, so `a ∼ b`, and `avb` is a triangle with
    the two hubs `a`, `b`, which (F2) excludes.
  - Then we need `F_v ⊄ span(p_a, p_b)`. This is automatic if `|C(v)| ≤ 1`, since then
    `dim F_v ≥ 3`.
  - If `C(v) = {a, b}`, then `a ≁ b` by (F2). Inclusion would force `F_v = span(p_a, p_b)`, hence
    `p_a ∈ n_b^⊥`. By (g3) we may take `p_a ∉ n_b^⊥`, since `b ∉ C(a)`.
- **Conjunct 4 at a vertex of degree `≤ 1`.** Here `closedNbhd v` is `{v}` or `{v, u}`, so the
  conjunct is `p_v ≠ 0` or conjunct 2 at `vu`. (The claim is stated without (H). *Added at the
  second reading, 2026-09-25.*)
- **Conjunct 3.** Holds by the choice of normals.

Complete with non-hub normals as in the Observation. The Lean-level conjunct 1 needs a nonzero
extensor at every `e : β`; take `p_u ∧ p_v` on the links and anything nonzero elsewhere. ∎

*Remarks.*
- (MC-123) generalizes the landed L6b (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`):
  triangle-freeness is weakened to (F2). Under (H) the triangles that (F2) allows are pendant
  triangles, a hub with two degree-2 vertices, and `C₃` itself. So the census's `middle` zone,
  hcard with a triangle, is feasible. `zsurvey.py` exhibits nondegenerate points at all 18
  `exh8` members of that zone.
- **Corollary.** A feasible graph of minimum degree ≥ 2 has a vertex of degree 2, and every hub
  has at least `deg − 2` neighbours of degree 2. If every degree were ≥ 3, every vertex would be a
  hub with at least 3 hub neighbours, against (F1).

> **(MC-124)** `[PROVED]` *(the nondegenerate locus is irreducible; the reduction)* Let `G` be simple,
> satisfying (F1) and (F2), with `K` infinite.
> **(i)** `Y′_3(G)` is the image of a nonempty Zariski-open subset of an affine space `K^N` under a
> polynomial map `Ψ`, so `Z(G)` is irreducible and its `K`-points are dense. The nondegenerate
> realizations, with non-hub normals forgotten, form a nonempty open dense subset of `Y′_3(G)`.
> **(ii)** `HasGenericPencilRealization K 3 G` holds **iff** some point of `Z(G)` with adjacent
> points independent has rank `≥ 6(|V| − 1) − def₃(G)`. In particular it suffices that one point of
> `Y′_3(G)` with adjacent points independent attains. It also suffices that a limit of points of
> `Y′_3(G)` along a polynomial curve (after rescaling each point by a power of `t`) has adjacent
> points independent and attains. Conjunct 4 need not hold at the point, and conjunct 3 need not hold
> at the limit. *(Repaired at the second reading, 2026-09-25: the first wording dropped adjacent
> independence and said conjunct 3 "need not hold" on `Y′_3(G)`, where it holds by definition.)*

*Proof.*
- (i), the map `Ψ`. For `C(v) = {h₁, …, h_s}`, put `p_v := c_v · ⋆(n_{h₁} ∧ … ∧ n_{h_s} ∧ y_{v,1} ∧ … ∧ y_{v,3−s})`,
  where `⋆ : Λ³K⁴ ≅ K⁴` is `p_i = det(·, …, ·, e_i)`. This is orthogonal to every `n_{h_j}`.
- Over normals in `O′` (independent on every `C(v)`), this map is onto `F_v`:
  - `s = 3`: the scalar `c_v` sweeps the line.
  - `s = 2`: `y ↦ ⋆(n₁ ∧ n₂ ∧ y)` has kernel `span(n₁, n₂)`, so its image is the 2-dimensional
    `F_v`.
  - `s = 1`: every `p ∈ n^⊥` is `⋆(n ∧ y ∧ y′)` with `{n, y, y′}` a basis of `p^⊥`.
  - `s = 0`: `p_v = y`.

  So `Ψ(Ω) = Y′_3(G)` for the nonempty open set `Ω = {n ∈ O′}`. Nondegeneracy is a finite
  conjunction of nonvanishing minors, and it is nonempty by (MC-123).
- (ii) ⇒: a nondegenerate attaining realization is such a point.
- (ii) ⇐: the Lean rows (`hingeRowBlock e`, the dual annihilator of `span{C_e}`) have no basis
  polynomial in `C_e`. So use (MC-3)'s augmented motion matrix `A` instead. Its entries are linear in
  the `C_e = p_u ∧ p_v`, hence polynomial in the points, and `rank A = |E| + rank R` wherever every
  `C_e ≠ 0`. At the given point adjacent points are independent, so every `C_e ≠ 0`. Let `M` be an
  `(|E| + target)`-minor of `A` that is nonzero there. Then `M ∘ Ψ` is not identically zero;
  otherwise `M` would vanish on `Ψ(K^N) ⊇ Y′_3`, hence on its closure. *(Repaired at the second
  reading, 2026-09-25: the first wording took a minor of "the rigidity matrix", which the Lean rows
  do not make polynomial.)*
- Let `D` be the product of the finitely many minors certifying conjuncts 2–4 and `p_v ≠ 0` at
  (MC-123)'s witness. Then `D ∘ Ψ ≢ 0`. Since `K` is infinite, some `θ` has `(M D)(Ψ(θ)) ≠ 0`. There
  the realization is nondegenerate, after completing the non-hub normals.
- There every `C_e ≠ 0` (conjunct 2), so its rank `rank A − |E|` is `≥` the target. It is `≤` the
  target at every realization by the partition bound, landed as
  `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le` (under `[Finite α] [Finite β]`,
  `bodyBarDim 3 = screwDim 2`, `V(G)` nonempty and nonzero hinges at links). A curve
  `p(t)` in `Y′_3` for `t ≠ 0` has its limit in the closure, and rescaling `p_v` preserves the
  incidences and the lines. ∎

*Reading.* This is the answer to "which component carries the generic motive": **exactly one, `Z(G)`.**
At `K_{2,3}` it is (MC-9)'s collinear jump stratum.

> **(MC-125)** `[PROVED]` *(dimension; where `X₀` and `Z` coincide)* Under (H) and (F1), (F2):
> **(i)** `dim Z(G) = 3|Hub| + Σ_v (3 − |C(v)|) = 3|V| − Σ_{h ∈ Hub}(deg h − 2) = 5|V| − 2|E|`, the
> expected dimension. `X₀` has `dim X₀ = 2|V| + ℓ₀ ≥ 2|V| + 3 + def₂ ≥ 5|V| − 2|E|`, where the last
> step is the all-singletons partition. *(Second reading, 2026-09-25: dimensions here are projective.
> `Y′_3` and `Z` are read in `(P³)^{Hub} × (P³)^V`, each normal and each point up to scale, which is
> how the count `3|Hub| + Σ_v (3 − |C(v)|)` is taken. `X₀` embeds there through
> `p_v = (x_v, y_v, z_v, 1)` and its hub planes, with the same dimension `2|V| + ℓ₀`.)*
> **(ii)** If `X₀`'s generic point is nondegenerate (`G` is not A′), then **`X₀ = Z(G)`**. In
> particular `ℓ₀ = 3 + def₂(G)`, which is Jackson–Jordán's equality at `G`, obtained here from
> dimensions alone, and `def₂(G) = 3|V| − 3 − 2|E|`. Moreover, **the hub planes at `X₀`'s generic
> point are generic**: `Z → O′` is onto.
> **(iii)** `[PROVED-MOD]` *((MC-33))* Hence, at a feasible non-A′ graph, no two hubs lie in a common
> `def₂`-rigid subgraph. The translation from "planes forced equal on `X₀`" to "common rigid
> subgraph" is (MC-13)(c)'s "if" direction.

*Proof.* (i) is the fibration `Y′_3 → O′` with fibres `∏ P(F_v)`, together with
`Σ_v |C(v)| = Σ_h |N[h]|`.

(ii) Embed `X₀` in the joint (normals, points) space. At an admissible `q` the hub planes are
determined by the points. A nondegenerate generic point lies in `Y′_3`, so `X₀ ⊆ Z`. Both are
irreducible and closed, and `dim X₀ ≥ dim Z`, so they are equal and every inequality in (i) is an
equality. Dimensions are taken over `K̄`, as in (MC-2); both sets have dense `K`-points. ∎

`[MEASURED]` *(`e3check.py --exh 8`)* All 46 feasible non-A′ `exh8` graphs have `def₂ = 3|V| − 3 − 2|E|`
and no hub pair in a common `def₂`-rigid subgraph.

**Ears: the transfer.**

**Setting.** `G = G′ + ear`, with `a − x₁ − ⋯ − x_k − b`, `k ≥ 1`. It is open if `a ≠ b`; closed if
`a = b`, and then `k ≥ 2`. `G` is feasible and simple, and `G′` satisfies (H). Then `G′` is feasible
(F1 and F2 are monotone). An end `a` may have `deg_{G′} a = 2`: it is then a **new hub** of `G`.
Put `Hub⁺ := Hub(G) ∩ V(G′)` and `C⁺(v) := Hub⁺ ∩ N_{G′}[v]`.
- Ear vertices are non-hubs of `G`, so **`C_G(v) = C⁺(v)`** for every `v ∈ V(G′)`, and
  `|C⁺(v)| ≤ 3` by (F1) at `G`.
- `π_a` denotes `a`'s plane in a configuration of `G′`: the hub normal if `a ∈ Hub(G′)`, otherwise
  the plane of the 3 points of `N_{G′}[a]`.
- The **placement** space is `p_{x₁} ∈ π_a`, `p_{x_k} ∈ π_b`, the middle points free; for `k = 1`,
  `p_x ∈ π_a ∩ π_b`.
- `Y := closure{(C′, placement) : C′ ∈ Y′_3(G′) satisfying (MC-126)(i)}`. By (i) this is a closure
  over a nonempty open subset of `Y′_3(G′)`. There `π_a ≠ π_b`, so every placement space has the
  dimension counted in (iv). (Over all of `Y′_3(G′)`, the `k = 1` placement space jumps to a plane
  where `π_a = π_b`, and (iii) does not cover those points.) *(Repaired at the second reading,
  2026-09-25.)*

> **(MC-126)** `[PROVED]` *(the ear transfer)* In this setting:
> **(i)** *(formal hubs)* At a generic point of `Y′_3(G′)`, the planes `π_h` for `h ∈ Hub⁺`
> satisfy independence on every `C⁺(v)`. New hubs use their non-hub plane. Also `π_a ≠ π_b`.
> **(ii)** *(flag genericity)* If `a ≠ b` and `a ≁ b`, the generic flag pair
> `(p_a, π_a; p_b, π_b)` of `Y′_3(G′)` is in **orbit (i)**: `p_a ∉ π_b` and `p_b ∉ π_a`. So `m := π_a ∩ π_b`
> and `n := p_a p_b` are skew.
> **(iii)** At every point `(C′, placement)` over a `C′` satisfying (i), `G`'s incidences and
> conjunct 3 hold. **So `Y ⊆ Z(G)`**, with no condition on `dim U` or on `G′` being non-A′.
> **(iv)** `dim Y = dim Z(G)`, so `Y = Z(G)`: at `Z(G)`'s generic point the `G′`-part is generic in
> `Z(G′)` and the placement is generic.
> **(v)** *(the second component of (MC-18)(b))* Take `k = 1`, `a, b ∈ Hub(G′)`, and `G′` not A′, so
> that `Z(G′) = X₀(G′)`. If `dim U ≥ 2`, then `Y = X₀(G)`. If `dim U = 1`, then `Y` is the
> **second** component `{φ₀ = 0} × L_{G′}` of (MC-18)(b)'s incidence, and `G` is A′ at `x`. Either
> way, the rank question on `Y` is the same: `X₀(G′)`'s generic point with `p_x` generic on `m`.
> (MC-9)'s `K_{2,3} = C₄ + x` is the instance with new hubs, where `m = p_c p_d`.

*Proof.* (i), (ii): take `Y′_3⁺(G′)`, which is `Y′_3` for the incidence structure with hub set
`Hub⁺`: every new hub `a` gets a *formal* free normal `n_a`, with `p(N_{G′}[a]) ⊥ n_a`. By
`C⁺ ⊇ C_{G′}` it maps into `Y′_3(G′)`. It is enough to exhibit one point of `Y′_3⁺` at which
`N_{G′}[a]` is non-collinear for each new hub `a`, and at which (ii)'s two conditions hold. At such
a point:
- the plane of `N_{G′}[a]` is `n_a`, so (i)'s independence holds;
- the conditions are open on the irreducible `Y′_3(G′)`, since the plane of three non-collinear
  points is polynomial in them;
- the generic point of `Y′_3(G′)` satisfies them together with any other nonempty open condition,
  for instance "`G′` attains".

Use moment-curve normals on `Hub⁺`, so (g1)–(g3) hold, and let `u, w` be `a`'s two neighbours in
`G′`. All three flats lie in `n_a^⊥`. The case split is on `C⁺(a) ∋ a`:
- **`C⁺(a) = {a, u, w}`.** Here `p_a` spans `n_a^⊥ ∩ n_u^⊥ ∩ n_w^⊥`.
  - Take `p_u ∈ F⁺_u ∖ ⟨p_a⟩`. `F⁺_u = F⁺_a` would force `w ∈ C⁺(u)`, i.e. `u ∼ w`, and then the
    triangle `auw` has three hubs of `G`, which (F2) excludes.
  - Then `span(p_a, p_u) = n_a^⊥ ∩ n_u^⊥`. Take `p_w ∉ n_u^⊥`, which is possible by (g3) since
    `u ∉ C⁺(w)`.
- **`C⁺(a) = {a, u}`.** Pick `p_a, p_u` independent in `n_a^⊥ ∩ n_u^⊥`, and `p_w ∉ n_u^⊥` by (g3).
  Here `u ∼ w` would give a triangle with the hubs `a`, `u`.
- **`C⁺(a) = {a}`.** Pick `p_u, p_w` independent: their flats have `|C⁺| ≤ 2`. Then pick
  `p_a ∈ n_a^⊥ ∖ span(p_u, p_w)`.

For (ii): `b ∉ C⁺(a)` and `|C⁺(a) ∪ {b}| ≤ 4`, so by (g3) we may take `p_a ∉ n_b^⊥`; symmetrically
`p_b ∉ n_a^⊥`. Every condition used is open and nonempty in the fibre over the fixed normals,
which is irreducible, so they hold simultaneously. `n_a ∦ n_b` holds on the moment curve.

(iii) The incidences hold:
- `π_a ⊇ N_{G′}[a] ∪ {p_{x₁}}`;
- an ear vertex has at most 3 closed neighbours;
- `C_G(v) = C⁺(v)` for old vertices, and `C_G(x_i) ⊆ {a, b}`, where `π_a ≠ π_b` by (i).

(iv) The dimension of `Z(G)` exceeds that of `Z(G′)` by `5k − 2(k + 1) = 3k − 2`. That is the
placement dimension: `2 + 2 + 3(k − 2)` for `k ≥ 2`, and `1` for `k = 1`. Then use (iii) and
irreducibility.

(v) Over `X₀(G′) = Z(G′)`, the pairs `(C′, placement)` are exactly (MC-18)(b)'s incidence
`{(z′, q_x) : (h_a − h_b)(q_x) = 0}`, because `p_x ∈ π_a ∩ π_b` reads `z_x = h_a(q_x) = h_b(q_x)`. If
`dim U ≥ 2`, the incidence is irreducible and equals `X₀(G)`. If `dim U = 1`, it factors, and `Y` is
the component `{φ₀ = 0} × L_{G′}`: its generic point lies over a generic `z′`, where `P_a ≠ P_b`.
Then use (iv). ∎ *(Rewritten at the second reading, 2026-09-25; the first sentence was garbled, its
content unchanged.)*

*Consequence* `[INFORMAL]` *(gap: not re-derived lemma by lemma)*. By (iv), Step MC10/MC13's ear-step
lemmas (MC-16)–(MC-26) and (MC-43)–(MC-47), (MC-54), (MC-44) and (MC-49) hold with `X₀` replaced
by `Z`. Their proofs use only three things: the generic point lies over a generic point with
generic placement; attainment at the base; and placement or flag statements. On `Z`:
- dominance holds for every `k`, including `k = 1` whatever `dim U` is;
- orbit (i) is automatic at non-adjacent ends by (ii);
- for (MC-44) and (MC-49), the chord gadget `G′ + ab` must be feasible, and then
  `Z(G′ + ab) ⊆ Z(G′)`.

So `Z` has fewer open ear cells than `X₀`: the `dim U = 1` cells and the orbit (ii)–(iv) cells at
`a ≁ b` disappear. Nothing below depends on this paragraph.

> **(MC-127)** `[PROVED]` *(the three reduction steps)* Let `G` be feasible and simple, with (H).
> **(a)** *(1-ear at `δ = 0`)* `x` has degree 2 with hub neighbours `a`, `b`. By (F2), `a ≁ b`.
> `G′ := G − x` satisfies (H), and `δ := def₃(G′) − def₃(G′/ab) = 0`, for instance when `a` and
> `b` lie in a common `def₃`-rigid subgraph of `G′`. **If `Z(G′)` attains, `Z(G)` attains.**
> **(b)** *(pendant triangle, closed ear)* `a y₁ y₂` is a triangle with `deg y_i = 2`, and
> `deg a ≥ 4`. `G′ := G − {y₁, y₂}`. If `Z(G′)` attains, `Z(G)` attains.
> **(c)** *(pendant triangle at a degree-3 hub: lollipop)* As in (b), but `deg a = 3`. Its third
> edge starts a bridge chain `a − x₁ − ⋯ − x_j − b` to a hub `b`. `G₂ := G` minus the triangle, `a`
> and the chain. If `Z(G₂)` attains, `Z(G)` attains.

*Proof.* (a) Take `C′ ∈ Y′_3(G′)` generic: it satisfies (MC-126)(i), (ii), and `G′` attains there. Put
`p_x ∈ m`; then `p_x ∉ n`, so the lines `p_a p_x` and `p_x p_b` are distinct (`λ = 2`). The point
is in `Y′_3(G)` by (MC-126)(iii).
- *Motions* (MC-16), re-derived: `X_x = X_a + sL_{ax}` and `X_b = X_x + tL_{xb}`. So
  `dim M_G = dim{X ∈ M_{G′} : X_b − X_a ∈ Λ} + (2 − λ)`.
- `G′` attains, so `dim M_{G′} = 6 + f`. The partition bound for the welded framework on `G′/ab`,
  with the same lines, gives `dim M_weld ≥ 6 + g`. So `r := dim{X_b − X_a} ≤ f − g = δ = 0`.
  Every motion of `G′` has `X_a = X_b`, and `dim M_G = dim M_{G′} = 6 + f`.
- *Target:* `def₃(G) = f`. A partition with `x` alone scores `val − 4`. `x` in the part of `a`
  (resp. `b`) scores `val − 5` if `a`, `b` are separated. With `a ∼_P b` and `x` joining them it
  scores `val`. The maximum is `max(f − 4, g) = f`, since `g = f`.
- The last hypothesis example: merging the parts that meet a `def₃`-rigid `K ∋ a, b` in a
  maximizing partition keeps it maximizing ((MC-35)'s argument), so `g = f`.
- Conclude with (MC-124).

(b) Take `y₁, y₂` generic in `π_a`. The three sides of a nondegenerate triangle in `π_a` are
independent, so `sL₁ + tL₂ + uL₃ = 0` forces `s = t = u = 0` and `dim M_G = dim M_{G′}`. Also
`def₃(G) = f`. Membership in `Y′_3(G)` is (MC-126)(iii), with `a` possibly a new hub.

(c) This is (MC-53)(i)–(ii), with `G₁` the triangle `a y₁ y₂` (which satisfies (H)), `G₂`, and the
path `a − x₁ − ⋯ − x_j − b`: `def₃` and the rank each gain `j + 1` over `G₁ ⊔ G₂`, and `C₃` attains at
three independent points. Every bridge hinge adds exactly 1 to `dim M` and to `def₃`, and the
triangle adds 0 as in (b). So `G` attains iff `G₂` does. If `b` is a new hub of `G`
(`deg_{G₂} b = 2`), (MC-126)(i)'s case analysis at `b` makes `N_{G₂}[b]` non-collinear at the generic
point of `Y′_3(G₂)`. *(Precision added at the second reading, 2026-09-25.)* Membership:
- place the chain as an ear placement at `b` (formal hub if new);
- `π_a` is generic, through `p_b` when `j = 0`;
- conjunct 3 at `a` and `b` holds generically, since at most 3 generic planes pass through a
  point. ∎

> **(MC-128)** `[PROVED]` *(class theorems, no hypothesis)* **(a)** Every `K_{2,k}`, `k ≥ 3`, has the
> generic pencil motive over every infinite field. **(b)** So does every feasible graph that reduces
> to a cycle by steps (MC-127)(a)–(c): in characteristic 0 by (MC-19)(a)'s certificates, and over
> every infinite field by (MC-134)(a) (Step MC20). *(Scope made explicit at the second reading,
> 2026-09-25.)*

*Proof.* (a) `K_{2,3} = C₄ + x` at the opposite, new-hub pair `a`, `b`. `C₄` is `def₃`-rigid, so
`δ = 0`. `Y′_3(C₄)` is every configuration. At four points in general position the hinges
`e₀₁, e₁₂, e₂₃, e₀₃` are independent, so `C₄` is rigid and `ρ = 0` literally. Then
`K_{2,k} = K_{2,k−1} + x`, with `K_{2,k−1}` rigid and `δ = 0`. Apply (MC-127)(a) at each step.

(b) Induction, with the base `Y′_3(C_n)` = every configuration. It attains by (MC-19)(a). Its
certificates are exact over ℚ, which covers characteristic 0 and every prime not dividing their
minors; (MC-134)(a) is the hand proof over every infinite field. `C₃` attains over every field: its
three sides are independent at three independent points. For `K_{2,k}` those certificates are not
needed, and the argument is characteristic-free. ∎

`[CONSTRUCTED]` *(`zk2k.py`)* `K_{2,3..10}`: a nondegenerate point at the target, 24/24, …, 66/66.

> **(MC-129)** `[PROVED]` *(a minimal `def₂`-rigid subgraph has a good ear)* Let `G` be feasible and
> simple, with (H), not a cycle. Let `H₀ = G[W₀]` be inclusion-minimal among `def₂`-rigid induced
> subgraphs with `|W₀| ≥ 2`, so that `|W₀| ≥ 3`. Then `H₀` is a **pendant triangle**, or `H₀`
> contains a vertex `y` of `G`-degree 2 whose neighbours `a`, `b` are hubs and satisfy
> **`δ(G − y; a, b) = 0`**.

*Proof.*
1. `H₀` has minimum degree ≥ 2. If some `y ∈ W₀` had `deg_G y = 2`, both of its edges lie in
   `H₀`. Otherwise every vertex of `W₀` is a `G`-hub. By (F1) each then has at most 2 neighbours in
   `W₀`, so `H₀` is a cycle. A `def₂`-rigid cycle is a triangle, and a triangle of hubs is excluded
   by (F2). So such a `y` exists.
2. Walk from `y` through vertices of `G`-degree 2: the walk stays in `W₀`, so the maximal chain
   `a − y₁ − ⋯ − y_k − b` through `y` lies in `H₀`.
3. **`k ≥ 2`, open or closed.** Putting `y₁`, `y₂` in as singletons adds 3 crossing edges,
   `+6 − 6 = 0`. So `H₀ − {y₁, y₂}` is `def₂`-rigid (and connected, as any `def₂`-rigid graph is).
   It contains `a` and `b`. If `a ≠ b`, it has ≥ 2 vertices, against minimality. If `a = b`, it
   must be `{a}`, and `H₀` is a pendant triangle. (With `k ≥ 3`, the same count already gives
   `val = k − 2 > 0`.)
4. **`k = 1`** (`a ≠ b`, `a ≁ b` by (F2)).
   - `H₀ − y` is connected: `c ≥ 2` components plus `{y}` would give `val = 3c − 4 > 0`.
   - `def₂(H₀ − y) ≤ 1`: adding `{y}` to a partition subtracts 1.
   - If `H₀ − y` is bridgeless, it is `def₃`-rigid ((MC-15)(i) step 2, re-derived: for `|P| ≥ 3`,
     `6(|P| − 1) − 5d ≤ 4 − 1.5|P| < 0`; for `|P| = 2`, `d ≥ 2`). So `δ = 0` by the merge argument.
   - If `H₀ − y` has a bridge `e`, the two sides `H₁`, `H₂` have `a ∈ H₁` and `b ∈ H₂`; otherwise
     `e` would be a bridge of `H₀`.
   - Each `H_i` is `def₂`-rigid: the partition `P₁ ∪ {y} ∪ {V(H₂)}` of `W₀` has value exactly
     `val_{H₁}(P₁)`.
   - Minimality forces `|H₁| = |H₂| = 1`. Then `H₀ = {a, y, b}` with `e = ab` is a triangle with
     two hubs, which (F2) excludes. ∎

> **(MC-130)** `[PROVED]` *(the reduction theorem)* Let `K` be infinite and let `G` be simple and
> feasible, satisfying (H). **`HasGenericPencilRealization K 3 G` follows from the same statement at
> every feasible simple graph `G°` satisfying (H), with `|V(G°)| ≤ |V(G)|`, that has no
> `def₂`-rigid subgraph on ≥ 2 vertices.** At such a `G°`, X₀'s generic point is nondegenerate
> ((MC-14); its own tag is `[INFORMAL]`, the gap being Jackson–Jordán's pin-collinear theorem, (MC-33);
> characteristic 0). So there the generic motive is exactly (MC-10)(a).
> **Corollary.** Every feasible simple graph satisfying (H) has the generic motive, **modulo
> (MC-10)(a) on the feasible graphs without a `def₂`-rigid subgraph** (supplied by (MC-89); see
> (MC-133)). In characteristic 0 this
> also uses Jackson–Jordán, which is published. **The A′ graphs add nothing.** `hK`'s habitat lies
> inside that base class ((MC-15)(i)).

*Proof.* Strong induction on `|V|`.
- A cycle `C_n` with `n ≥ 4` is a base graph. It has no `def₂`-rigid subgraph on `≥ 2` vertices: by
  all-singletons partitions, a path on `j ≥ 2` vertices has `def₂ ≥ j − 1`, and `C_n` itself has
  `def₂ ≥ n − 3`; a disconnected subgraph has `def₂ ≥ 3`. So no certificate is used, and the
  reduction stays characteristic-free. `C₃` is `def₂`-rigid and is handled directly, over every
  field. At three independent points its hinges `p₁ ∧ p₂`, `p₂ ∧ p₃`, `p₃ ∧ p₁` are independent, so
  `dim M = 6` and the rank is `12 = 6(3 − 1) − def₃(C₃)`. The point is nondegenerate: there are no
  hubs, and conjunct 4 is the independence of the three points. *(Repaired at the second reading,
  2026-09-25: this bullet first sent cycles to (MC-128)(b), whose base is (MC-19)(a)'s ℚ-exact
  certificates, so the reduction was not hypothesis-free as stated.)*
- If `G` has a `def₂`-rigid subgraph, (MC-129) gives either a 1-ear at `δ = 0` (MC-127)(a), or a pendant
  triangle (MC-127)(b)/(c).
- Each step consumes one feasible simple graph satisfying (H) with fewer vertices:
  - the 1-ear `y` lies on a cycle of the 2-edge-connected `H₀`, so `G − y` is connected;
  - `a` and `b` keep degree ≥ 2;
  - in (c), `b` keeps degree ≥ 2.
- Otherwise `G` is a base graph.
- The induction hypothesis is used in the form "the generic point of `Y′_3` attains". This is
  equivalent to the generic motive by (MC-124): an attaining nondegenerate point makes the open set
  of attaining points nonempty. ∎

`[MEASURED]` *(`zlemma.py --exh 8 --stuck 1500`)* (MC-129) and the reduction are asserted at every feasible
graph in two populations:
- `exh8`: 79 graphs, 46 with a `def₂`-rigid subgraph. Steps used: 61 1-ears at `δ = 0`, 22
  pendant triangles.
- 555 zstuck-shaped random graphs on ≤ 13 vertices (sampler support: `zstuck.build` only; the count
  includes repeats), 176 with a `def₂`-rigid subgraph.

No lollipop step occurred. Both populations are 2EC, so no bridge, and hence no lollipop, can
occur. For the bridged populations, see (MC-158).

> **(MC-158)** `[MEASURED]` *(`zbridged.py`; the second reading, 2026-09-25)* The bridged
> populations, which every other Step MC19 driver excludes:
> - *Exhaustive:* every connected simple non-2EC graph with minimum degree `≥ 2` on `≤ 8` vertices.
>   There are 45; 9 are feasible.
> - *Sampled:* `zrand.build`'s sampler without its `is_2ec` filter. Seeds 1/2/3, 3 000 draws each,
>   `≤ 14` vertices: 151 + 114 + 133 distinct feasible non-2EC samples satisfying (H). Support: that
>   sampler only.
> - *Results:* (MC-129) and (MC-130)'s bookkeeping hold at every graph (`zlemma.reduce_to_base`'s
>   asserts). That includes 8 + 124 + 92 + 103 lollipop steps (MC-127)(c) and 1 + 4 + 1 + 3 steps
>   (MC-127)(a). A nondegenerate hub-plane-chart draw at the target rank is exhibited at 9/9 and at
>   151/151, 114/114, 133/133 (exact certificates over ℚ). The (MC-125)(ii) corollary holds at 8/8
>   feasible non-A′ graphs.
> - *(MC-123)(⇐):* at all 376 graphs satisfying (F1) and (F2) among the 12 112 connected simple
>   graphs on 2..8 vertices (degree-1 vertices and trees included), a draw satisfies all four
>   conjuncts with explicit normals. Among the infeasible graphs, 0 draws passed.
>
> `PYTHONHASHSEED=0 python3 notes/scripts/w4/zbridged.py --n1 8 --n2 8 --p3 3000 --seed 1` (~12 s);
> `--n1 2 --n2 3 --p3 3000 --seed S`, `S = 2, 3` (~2 s each, Part 3 only).

> **(MC-131)** `[CONSTRUCTED]` *(exhibited certificates)*
> - `zsurvey.py --exh 8`: on `exh8`, each of the **79** graphs satisfying (F1) and (F2) has a
>   nondegenerate hub-plane-chart point at the target. That is 61 `feas` (`feas` = 60 triangle-free
>   graphs + `C₃`) + 18 `middle`, **33**
>   A′ (the census's 28, plus 5 from the middle zone).
> - `zdirect.py`: 176/176 A′ graphs of the zstuck shape, with repeats.
> - `zears.py`: the Z-ear steps with closed cells reduce all 33 `exh8` A′ graphs to non-A′
>   graphs. The rank at each certified `Y`-draw equals the target at 34/34 placements. The `k = 2`
>   and `k = 3` first steps (6 of 33) are the Z-forms of (MC-46) and (MC-45). They rest on the
>   `[INFORMAL]` *Consequence* paragraph after (MC-126), so "Z-ear covered" is a reach statement. The
>   34/34 ranks (and `zsurvey`'s 79/79) are the certificates.
>
> Each certificate is exact over ℚ, since mod-`2⁶¹ − 1` rank equal to the target certifies. These
> are not needed for (MC-130); they check it.

> **(MC-132)** `[OPEN]` *(what the rest needs)*
> - (MC-10)(a) on feasible graphs without a `def₂`-rigid subgraph. This is P3's core, now also
>   the generic motive's whole content. *(Written before (MC-89) was reported; (MC-89) supplies it,
>   modulo Jackson–Jordán: (MC-133).)*
> - A proof, free of Jackson–Jordán, that such graphs have nondegenerate `X₀`. (MC-125)(ii) gives only
>   the converse direction.
> - Optionally, the remaining `Z`-ear cells. These are `k = 1` with `2 ≤ δ ≤ 4` (orbit (i) is
>   automatic; the bad set is (MC-27)'s exact criterion) and `k = 2` with `a ∼ b` (orbit (iii)).
>   (MC-130) never uses them.

*What would change this.*
- A feasible graph where `zlemma.py`'s (MC-129) assert fires. That would be a proof error in (MC-129).
- A step (MC-127)(a) where the `Y`-draw rank falls below the target while `G′` attains at the draw.
  That would be an error in the motion count, which `zears.py` cross-checks.
- A simple graph satisfying (F1) and (F2) where `zdraw` cannot find a nondegenerate point in many
  draws. That would put (MC-123)'s genericity argument in doubt.
- *(Closed at the second reading.)* The upper bound "rank ≤ target at every realization" that
  (MC-124) cites is the landed `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`.

**Route B: the generic motive inside the pencil reduction's induction (2026-09-28, found by
formalization).** *Added by the Phase-40 MOTIVES pre-build recon (opus, read-only,
compiler-checked; `notes/Phase40-design.md` §3 MOTIVES). (MC-133)(ii)'s proof runs (MC-130)'s own
strong induction over every feasible graph satisfying (H) and closes it with (MC-14) at the base.
The Lean route proves the generic motive inside the induction of the pencil reduction
(`thm:pencil-reduction`) instead, whose hypothesis is the conditioned pair at every smaller graph,
and whose cut arm (`lem:pencil-cut-case`) already covers every graph that is not 2-edge-connected.
The claims below record the route and its three changed steps, and the obstruction that rules out
the planned fibre argument. (MC-183)–(MC-187) were **second-read on 2026-09-28** by a fresh
read-only reader (opus; the PI's call, 2026-09-28, `notes/pencil/adjudications.md`: a fresh reader
before the first build that consumes one). The reader re-derived every step, opened the body of every
Lean definition the claims read, and checked every citation's hypotheses. It found no refutation and
no gap. (MC-185) and (MC-187) are confirmed; (MC-183), (MC-184) and (MC-186) are confirmed with
precision repairs, each marked in place: (MC-183)'s closing sentence omitted three landed arms,
(MC-184) mis-scoped its (MC-76) citation and left out the step from `G_e`'s pictures to `G`'s, and
(MC-186) left (a)'s witness unsettled and (c)'s two flag conditions loose. The reader added (MC-188),
which settles (MC-186)(a), and (MC-189), (MC-12)'s sufficient half under weaker hypotheses, in the form
the base consumes; both are one writer's. Everything the base needs, (MC-184), (MC-189) and the base
theorem (`thm:pencil-x0-base-generic`), and (MC-188) are kernel-checked in compiled spikes, not landed
(gitignored, local to the reader's checkout; builder sources, not evidence; `notes/Phase40n.md`), and
(MC-183)'s composition recompiles at `8a0752d7` against M0's landed declarations with three steps
open once the base is supplied. (MC-185) and (MC-187) are kernel-checked as before. The rest are hand
proofs. No driver. Notation
as in Step MC8 and above: `Hub`, `C(v) = closedHubNbhd v`, `F(G, q)` the space of pairs `(z, P)` with
`z ∈ L(q)` and `P_v` the plane of `N[v]`, and a def₂-**rigid set** is `Y ⊆ V(G)`, `|Y| ≥ 2`, with
`def₂(G[Y]) = 0`.*

> **(MC-183)** `[PROVED]` *(route B: the generic motive from the induction hypothesis; composes (MC-184)–
> (MC-186) with (MC-129) and (MC-127)(b); found by formalization, MOTIVES recon 2026-09-28; the
> composition kernel-checked with those five steps as hypotheses; second-read 2026-09-28, closing
> sentence repaired)* Let `K` be
> infinite and `G` simple and 2-edge-connected on at least three bodies, `PencilNondegFeasible K G`,
> and suppose every graph on fewer bodies (at least one) satisfies the conditioned pair `PencilPair K 3`.
> Then **`HasGenericPencilRealization K 3 G`**. Consequently, run inside the pencil reduction, every
> nonempty graph satisfies the conditioned pair, and in particular `X0Gen` holds.

*Proof.* `G` satisfies (H).
- If `G` has no def₂-rigid set, `X₀`'s general point attains ((MC-89)) and, by (MC-184) with (MC-12)
  (in the form consumed, (MC-189)), is nondegenerate at a common point of one fibre.
- If `|V| = 3`, `G = C₃`, which has no proper rigid subgraph, and the pencil conjecture's `|V| = 3` base
  case gives the realization.
- Otherwise (MC-129) applies. A pendant triangle at a body of degree 3 would be joined to the rest by
  one edge, so at a 2-edge-connected `G` the good ear is a one-body ear at hub ends with
  `δ(G − y; a, b) = 0`, or a pendant triangle at a body of degree at least 4. No lollipop, (MC-127)(c),
  arises.
- In either case `G′`, `G` minus the ear or the triangle, is simple, nonempty and smaller, and feasible
  by (MC-186)(b). The hypothesis gives its generic realization, and (MC-186)(c) with (MC-185), or with
  (MC-127)(b)'s placement of the triangle in `π_a`, extends it to `G`.

Inside the pencil reduction (`thm:pencil-reduction`, `n = 3`), a graph with a loop is the landed loop
case and one on at most two bodies the landed base case. At a loopless graph on at least three bodies,
one that is not 2-edge-connected is the landed cut case; one that is 2-edge-connected but not simple
has the generic and distinct conjuncts vacuous and its bare conjunct from the landed non-simple case
(`lem:pencil-nonsimple-case`, which consumes the same hypothesis); and a simple 2-edge-connected one
takes the generic conjunct from the step above and the distinct one from (MC-157) (`X0Dist`), the bare
one following. The contraction and split arms take this one argument. ∎ *(Repaired at the second
reading, 2026-09-28: the sentence first named only the cut case and the vacuous conjuncts, omitting
the loop and base arms and the non-simple bare conjunct.)*

> **(MC-184)** `[PROVED]` *(planes separate at a rigid-free graph, any pair; (MC-13)(a)–(c)'s "only
> if", from edges to pairs; found by formalization, MOTIVES recon 2026-09-28; second-read 2026-09-28,
> citation and picture step repaired; kernel-checked in a compiled spike, not landed)*
> Let `K` be infinite and `G` simple, with `|N[v]| ≥ 3` at every body and no def₂-rigid set. Let
> `u ≠ w` be bodies of `G`. **Off a proper Zariski-closed set of pictures `q`, some `(z, P) ∈ F(G, q)`
> has `P_u ≠ P_w`.**

*Proof.* Let `G_e` be `G` plus one new body `x` joined to exactly `u` and `w` (the (MC-13) graph; `u ∼ w`
is not assumed). In Lean it is the Matroid package's apex graph of `G` restricted to `E(G)` and the two
new edges, on `Option α`, so no label of `β` is used.
- `{(z, P) ∈ F(G, q) : P_u = P_w}` injects into `F(G_e, (q, q_x))` by `z_x := P_u(q_x)`, `P_x := P_u`:
  at `x` the plane `P_u` carries `z_u` and `z_w = P_w(q_w) = P_u(q_w)`, and at `u` and `w` the new
  neighbour lies on `P_u = P_w`. This is (MC-13)(a)'s easy half, with no condition on `q_x`.
- `def₂(G_e) ≤ def₂(G) − 1`. Take a partition of `V(G_e)` and restrict it to `V(G)`. As in (MC-13)(b),
  `x` alone costs 1, `x` in a part other than `u`'s and `w`'s costs 4, and `x` in `u`'s part costs 2 when
  `w` is elsewhere. In the remaining case `u, w` share a part `X`, `|X| ≥ 2`, and refining `X` into
  singletons raises the value by `X`'s singleton value, which is at least 1 at a rigid-free graph
  (`lem:deficiency-sparse`: (MC-76)'s direction "no rigid set ⟹ every set of two or more bodies has
  singleton value ≥ 1", which needs none of (H)); so the restriction is at most `def₂(G) − 1`.
  *(Citation repaired at the second reading, 2026-09-28: (MC-76) is stated under (H), which `G` need
  not satisfy here.)*
- Jackson–Jordán's equality (MC-172) at `G_e` and at `G`, at a picture generic for both, gives
  `dim{P_u = P_w} ≤ 3 + def₂(G_e) ≤ 2 + def₂(G) < 3 + def₂(G) = dim F(G, q)`. To state this on `G`'s
  pictures, fix the new body at a picture `q_x⁰` taken from one non-root of `G_e`'s polynomial; then
  `q ↦ P_{G_e}(q, q_x⁰)` is a nonzero polynomial in `G`'s picture coordinates, and its product with
  `G`'s is the claimed one. ∎ *(Picture step added at the second reading, 2026-09-28.)*

At a rigid-free graph every hub pair of (MC-12)(ii) and (iii) is such a pair, and (MC-12)'s affine
reading turns the finitely many resulting nonzero polynomials on `L(q)` into conjunct 3; the fibre
intersection (`lem:pencil-x0-fibre-intersection`) meets them with the attaining heights. That is the
base of (MC-183), in place of (MC-14), whose "if" direction it is at rigid-free graphs. *(Second
reading, 2026-09-28: (MC-12)'s half in the form consumed is (MC-189), below, with weaker hypotheses;
finitely many conditions meet by induction on their number from the two-condition lemma. The base
theorem, `thm:pencil-x0-base-generic`, is kernel-checked in a compiled spike, not landed.)*

> **(MC-189)** `[PROVED]` *(a configuration is nondegenerate when the named planes differ; (MC-12)'s
> sufficient half under weaker hypotheses, in the form `lem:pencil-x0-conjunct-three` consumes;
> written at the second reading, 2026-09-28, and so one writer's; kernel-checked in a compiled spike,
> not landed)* Let `G` have finitely many edge labels and every `|C(v)| ≤ 3`. Let `q` be admissible for
> `G`, with `q_v, q_{w₁}, q_{w₂}` non-collinear whenever `v` is a hub and `w₁ ≠ w₂` are hub neighbours
> of `v`. Let `z ∈ L(q)`, with `P_v` the plane of `N[v]`. Suppose **`P_a ≠ P_b`** for every edge `ab`
> joining two hubs, and for any two distinct hubs `a, b` adjacent to one body that is not a hub. Then
> **the configuration `(q, z)`, with the plane normal of an admissible triple at every body, is a
> nondegenerate pencil realization.** Neither (H) nor feasibility is used.

*Proof.* Conjuncts 1 and 2 are the configuration's (`lem:pencil-config-distinct-realization`). Each
normal is a nonzero multiple of `((P_v)₀, (P_v)₁, −1, (P_v)₂)` (`lem:pencil-condition-linear`), so
conjunct 3 on `S = C(v)` is the affine independence of `{P_s : s ∈ S}`.
- At a hub, `S = {v} ∪ T` with `T` the hub neighbours of `v`, and `|T| ≤ 2`. `|T| = 1` is the edge
  condition. For `T = {w₁, w₂}`, `d_i := P_{w_i} − P_v` is nonzero and annihilates `q̂_v` and `q̂_{w_i}`,
  since both planes carry `z` there. So `d₂ · q̂_{w₁} ≠ 0`, or `d₂` would annihilate three independent
  vectors. Dotting `s d₁ + t d₂ = 0` with `q̂_{w₁}` and with `q̂_{w₂}` gives `t = 0` and `s = 0`.
- At a non-hub, `S ⊆ N[v] ∖ {v}`, which has at most two members; two members is the second condition.
- Conjunct 4: a non-hub's closed neighbourhood has at most three members, and admissibility puts three
  independent picture points in it, so it is exactly that triple, whose configuration points are
  independent at every height. ∎

> **(MC-185)** `[PROVED]` *(the one-ear extension; (MC-127)(a)'s rank and placement, with a weaker
> flag condition than (MC-126)(ii); found by formalization, MOTIVES recon 2026-09-28; kernel-checked;
> second-read 2026-09-28)* Let `G` be simple with a one-body open ear `a − x − b` on `V₁`, `a` and `b`
> hubs of `G`, and `def₃(G[V₁]) ≤ def₃(G)`. Let `(F′, n, p)` be a nondegenerate realization of `G[V₁]`
> at its deficiency rank with **(i)** `n` independent on `C_G(v)` for every `v ∈ V₁`, **(ii)** `n_a, n_b`
> independent, and **(iii)** not both `p_a ⊥ n_b` and `p_b ⊥ n_a`. Then **`HasGenericPencilRealization
> K 3 G`**.

*Proof.* By (iii), `p_a, p_b` are independent (a dependency puts both on `π_a ∩ π_b`), and the line
`m = n_a^⊥ ∩ n_b^⊥` is not the line `p_a p_b`. Take `p_x ∈ m` off `span(p_a, p_b)`, so `p_a, p_x, p_b`
are independent; `n_x` is the plane through them, and the new hinges are `p_a ∧ p_x`, `p_x ∧ p_b`.
- Incidences: `p_x ∈ π_a ∩ π_b`, and `x`'s plane contains its three points.
- Conjunct 3: at `v ∈ V₁` it is (i), since `x` is not a hub; at `x` it is (ii), `C(x) ⊆ {a, b}`.
- Conjunct 4: at `x` by construction; elsewhere the closed neighbourhoods of non-hubs are unchanged,
  since `a` and `b` are hubs.
- Rank: the ear rank law ((MC-16) in rank form, `lem:block-rank-ear`) gives
  `rank(G) = rank(G[V₁]) + 10 + dim(ρ + Λ) − 6 ≥ rank(G[V₁]) + 6`, the two new hinges being
  independent. This is the target of `G[V₁]` plus 6, which is at least `G`'s target by
  `def₃(G[V₁]) ≤ def₃(G)`; the upper bound holds at every realization. ∎

(MC-126)(ii) asks for orbit (i), `p_a ∉ π_b` and `p_b ∉ π_a`. The step needs only that `m` and `p_a p_b`
differ, and only the independence of the two new hinges enters the rank, not where `p_x` sits on `m`.
(MC-129)'s `δ(G − y; a, b) = 0` gives the deficiency hypothesis through 40l's merge lemma
(`lem:deficiency-merge-rigid`).

> **(MC-186)** `[PROVED]` *(the formal hubs by steering; (MC-126)(i) in the form consumed; found by
> formalization, MOTIVES recon 2026-09-28; second-read 2026-09-28, (a)'s witness settled by (MC-188),
> (c) repaired)* Let `K` be infinite, `G` simple and
> feasible, `V₁ ⊆ V(G)` and `G′ := G[V₁]`. Suppose every hub `h` of `G` in `V₁` that is not a hub of `G′`
> has exactly two neighbours `u, w` in `V₁`, and every other neighbour of `h` is a non-hub of `G` (at
> (MC-127)(a) the ends of degree 3; at (MC-127)(b) the triangle's body of degree 4). Then:
> **(a)** `G` has a nondegenerate realization at which the points of `N_{G′}[h] = {h, u, w}` are
> independent, for every such `h`;
> **(b)** its restriction is a nondegenerate realization of `G′` (so `G′` is feasible), with `n`
> independent on `C_G(v)` for every `v ∈ V₁`;
> **(c)** if `G′` has a generic realization, it has one at which, besides, `n` is independent on `C_G(v)`
> for every `v ∈ V₁`, together with any finitely many further conditions that are the nonvanishing of a
> polynomial in the chart seed and hold at the restriction in (b). At (MC-127)(a) these include
> (MC-185)(ii) and (iii).

*Proof.* Phase 39's chart (`PencilSeed`): the points and hub normals are polynomial in a seed, and every
nondegenerate realization is a chart point up to per-body scalars (`exists_pencilSeed_of_nondeg`).
- (a) The independence of `N_{G′}[h]`'s points is a polynomial condition on `G`'s seeds. A
  standard-basis seed witnesses it: Phase 39's pendant witness with its cut-edge, degree and `V₁`
  hypotheses replaced by "every neighbour of `h` other than `u, w` is a non-hub" ((MC-188)). A common
  seed with `G`'s own nondegeneracy conditions (witnessed at a reseeding of `G`'s feasible realization)
  gives (a). *(Repaired at the second reading, 2026-09-28: the opening recon left the generalized
  witness as a hypothesis; (MC-188) proves it.)*
- (b) Restriction keeps every conjunct except conjunct 4 at the bodies that stop being hubs
  (`IsNondegPencilRealization.mono`), and there it is (a). Conjunct 3 on `C_G(v)` is `G`'s.
- (c) A nondegenerate realization is a chart point for **every** correct choice of selectors, not only
  the one `exists_pencilSeed_of_nondeg` picks: at each body, fill the free slots of its hub normals
  with a basis of the rest of that body's point's orthogonal complement. So the generic realization and
  the restriction in (b) are chart points of one chart of `G′`. The rank at the first, and each condition
  at the second, are nonzero polynomials on the seeds, and a common seed (Phase 39's steering, the
  pattern of the pendant cut arm) gives the realization. At (MC-127)(a), (ii) and (iii) hold at the
  restriction by `G`'s conjunct 3 and 4 at `x`: if `p_a ⊥ n_b` and `p_b ⊥ n_a`, the independent `p_x, p_a,
  p_b` would lie in the 2-dimensional `n_a^⊥ ∩ n_b^⊥`. (ii) is carried by the 2×2 minor of `(n_a, n_b)`
  nonzero at the restriction, and (iii), a disjunction, by whichever of `p_a · n_b`, `p_b · n_a` is
  nonzero there. ∎ *(Repaired at the second reading, 2026-09-28: (iii) is not the nonvanishing of one
  polynomial until that choice is made. The reseed at given selectors is not landed:
  `exists_pencilSeed_of_nondeg` returns its own selectors, so it is a new leaf, EARS' T1.)* *(Landed
  2026-09-29 as `exists_pencilSeed_of_nondeg_of_selectors`, `Pencil/Reseed.lean`.)* *(EARS
  recon, 2026-09-29: (a)–(b) in the form proved is (MC-190), and (c)'s scope as proved is (MC-191),
  below.)*

This replaces (MC-126)(i)'s moment-curve witnesses by `G`'s own feasible realization, and (MC-123)(⇐)
by restriction: feasibility of `G′` is never derived from (F1) and (F2).

> **(MC-188)** `[PROVED]` *(the pendant witness with non-hub neighbours; settles (MC-186)(a)'s witness;
> written at the second reading, 2026-09-28, and so one writer's; kernel-checked in a compiled spike,
> not landed)* Let `G` be finite, simple and feasible, let `h` be a hub of `G` with distinct neighbours
> `u, w`, and let every other neighbour of `h` be a non-hub of `G`. **For every hub selector correct at
> every body, some chart seed makes the chart points of `h`, `u` and `w` linearly independent.** No
> vertex set `V₁`, cut edge or degree condition at `h` is used.

*Proof.* Phase 39's pendant witness (`exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3`),
with a simpler index assignment. Take every hub normal to be a standard basis vector `e_{idx(y)}`, with
`idx(h) = 0`, `idx(u) = 1`, `idx(w) = 2` and `idx = 3` elsewhere. At each of `h`, `u`, `w`, fill the
free hub slots with the remaining basis vectors, so the chart point is a nonzero multiple of the one
basis vector its closed hub-neighbourhood misses.
- `C(h) ⊆ {h, u, w}`, since the other neighbours are non-hubs, so `h`'s point lies along `e₃`.
- `C(u)` misses index 2: `w ∈ C(u)` would make `huw` a triangle with the two hubs `h, w`, which (F2)
  excludes. It has at most one member outside `{h, u}`, all of index 3: by (F1) if `u` is a hub, and by
  `deg u ≤ 2` otherwise. So `u`'s point lies along `e₂`; symmetrically `w`'s lies along `e₁`.

Three distinct basis directions are independent. The Phase-39 form's cut edge served only to keep its
far body out of `C(u)` and `C(w)`, which a non-hub never enters. ∎

**EARS' three claims (2026-09-29, found by formalization).** *Added by the Phase-40 EARS pre-build
recon (opus, read-only, compiler-checked; `notes/Phase40o.md`). It compiled every EARS leaf
sorry-free at the signatures route B's assembly consumes, and needed three claims beyond
(MC-183)–(MC-189): (MC-190) is (MC-186)(a)–(b) in the form proved, (MC-191) is (MC-186)(c)'s scope as
proved, and (MC-192) is (MC-127)(b)'s rank argument in the cut-vertex form used. All three landed
in EARS' builds (B1–B4, `e7c80bba`–`306dcf15`) and were **second-read on 2026-09-29**, after the
builds, by a fresh read-only reader (opus), who checked this prose against the landed declarations,
re-derived each proof and checked each citation's hypotheses. It found no refutation and no gap.
(MC-190) is confirmed; (MC-191) and (MC-192) are confirmed with precision repairs, each marked in
place. The reader added (MC-193), off the route. `H ≤ G` is a subgraph, and a **demoted hub** of `H` is a hub of `G` that is a body but not a hub of
`H`.*

> **(MC-190)** `[PROVED]` *(the formal hubs, (MC-186)(a)–(b) in the form proved: any subgraph, no count
> of the kept neighbours; found by formalization, EARS recon 2026-09-29; landed as
> `exists_isNondegPencilRealization_restrict_of_demoted` (`Pencil/MainComponent/GenericSteer.lean`,
> `45d49861`); second-read 2026-09-29, confirmed)* Let `K` be infinite, `G` finite, simple and feasible, and
> `H ≤ G`. Suppose that at every demoted hub `h` of `H`, every neighbour of `h` in `G` that is not its
> neighbour in `H` is a non-hub of `G`. **Then `G` has a nondegenerate realization whose restriction to
> `H` is nondegenerate.** So `H` is feasible, and the restriction's normals are independent on `C_G(v)`
> for every body `v` of `G`.

*Proof.* Re-seed a nondegenerate realization of `G` (`exists_pencilSeed_of_nondeg`). Steer one chart
seed carrying the standing chart conditions and, at every demoted hub `h`, the independence of the
chart points of `N_H[h]`. Then re-choose the fills of the non-hub normals, which moves no point, and
take the chart realization. Its restriction keeps every conjunct except conjunct 4 at the demoted
hubs ((MC-186)(b)), and there it is the steered condition. The steered condition holds at some seed:
- `h` has at most two neighbours in `H`, not being a hub of `H`.
- With two, `u` and `w`, every other neighbour of `h` in `G` is not an `H`-neighbour, so it is a
  non-hub, and (MC-188) gives a seed at which the points of `h, u, w` are independent.
- With one, `y`, `N_H[h] = {h, y}` lies along an edge of `G`, independent at the re-seeded
  realization by conjunct 2. With none, `N_H[h] = {h}`, a nonzero point. ∎

At (MC-127)(a) and (b) the lost neighbours are the ear's or the triangle's bodies, of degree 2, so the
hypothesis is immediate. (MC-186)'s "exactly two neighbours `u, w` in `V₁`" is not needed.

> **(MC-191)** `[PROVED]` *((MC-186)(c)'s scope as proved; found by formalization, EARS recon
> 2026-09-29; landed as `exists_isNondegPencilRealization_steer` (`GenericSteer.lean`, `45d49861`),
> through T1 `exists_pencilSeed_of_nondeg_of_selectors` (`Pencil/Reseed.lean`, `e7c80bba`);
> second-read 2026-09-29, confirmed with repairs)* Let `K` be
> infinite, `H` finite and loopless with a body, `(F₁, n₁, p₁)` a nondegenerate realization of `H` at
> its deficiency rank (`n = 3`), and `(F₂, n′, p′)` any nondegenerate realization of `H`. Let
> `S₁, …, S_k ⊆ V(H)` be sets on which `n′` is independent, and `(u₁, w₁), …, (u_m, w_m)` pairs of
> bodies of `H` with `p′_{u_j} · n′_{w_j} ≠ 0`. Suppose every member of every `S_i`, and every `w_j`, is a hub
> of `H` or has exactly three closed neighbours in `H`. **Then `H` has a nondegenerate realization at
> its deficiency rank whose normals are independent on every `S_i`, with `p_{u_j} · n_{w_j} ≠ 0` for
> every `j`.**

*Proof.* Re-seed the first realization (`exists_pencilSeed_of_nondeg`), which fixes the selectors, and
the second at the same selectors. At each body the selected normals (at a non-hub, the selected chart
points) are independent and orthogonal to the body's point (normal); completing them to a basis of
that orthogonal complement fills the free slots, and the cross product of a basis of it is a nonzero
multiple of the target. So both realizations are chart points of one chart, up to per-body scalars.
- The rank rows at the first, and at the second each independence and each product
  `Σᵢ (p_u)ᵢ (n_w)ᵢ`, are polynomials in the seed, each nonzero somewhere; a common non-root carries
  them all together with the standing chart conditions. The rows give the steered realization at
  least the first's rank, and the upper bound (`lem:relative-deficiency-rank-bound`) holds at every
  realization, so it is at the deficiency rank.
- The seed has no coordinates of its own for the fills of the non-hub normals (`PencilSeed.ofCoord`
  reads `fillNbr` off `fillHub`'s coordinates), so they are re-chosen after steering, which moves no
  point. A normal read by a condition is unaffected by the fills — so it is a nonzero multiple of `n′`
  at the flattened second seed, and unchanged by the re-choice — when it is at a hub (a free seed
  coordinate) or at a non-hub whose three closed neighbours fill every slot (a cross product of chart
  points). The hypothesis puts every normal the conditions read in one of these two cases. ∎
  *(Repaired at the second reading, 2026-09-29: the rank's upper bound was implicit, and the
  hypothesis was said to be needed "exactly" for the re-chosen fills; it is sufficient, and it is
  also what identifies the second realization's normals at the flattened seed (the Lean's `hnm₂'`).
  (MC-193) records that it is the chart's, not the argument's.)*

This replaces (c)'s "any finitely many further conditions that are the nonvanishing of a polynomial in
the chart seed": such a polynomial need not survive the per-body scalars of the re-seeding or the
re-chosen fills. The second realization need not be (MC-186)(b)'s restriction. At (MC-127)(a) a
demoted end has degree at least 3 and loses the ear body; at (b) the triangle's hub has degree at
least 4 and loses two bodies. Either way it keeps exactly two neighbours, so it has three closed
neighbours in `G′`.

> **(MC-192)** `[PROVED]` *((MC-127)(b)'s rank in cut-vertex form; found by formalization, EARS recon
> 2026-09-29; landed as `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`
> (`Pencil/MainComponent/GenericTriangle.lean`, `306dcf15`); second-read 2026-09-29, citation
> repaired)* Let `G` be finite
> and simple with a pendant triangle `c y₁ y₂` (`deg y_i = 2`) at a hub `c`, `G′ := G − {y₁, y₂}`, and
> let `(F′, n, p)` be a nondegenerate realization of `G′` at its deficiency rank with `n` independent on
> `C_G(v)` for every body `v` of `G′`. **Then `HasGenericPencilRealization K 3 G`.**

*Proof.* Take `p_{y₁}, p_{y₂}` in `π_c` with `p_c, p_{y₁}, p_{y₂}` independent (complete `p_c` to a basis
of `n_c^⊥`), give `y₁` and `y₂` the normal `n_c`, and put point joins on the three new edges.
- Conjuncts 1 and 2: the three points lie in `π_c` and are pairwise independent.
- Conjunct 3: at a body of `G′` it is the hypothesis, `y₁, y₂` not being hubs; at `y_i`, `C(y_i) = {c}`.
- Conjunct 4: at `y_i` it is the three points. A non-hub of `G` in `G′` is not `c`, so its closed
  neighbourhood is unchanged, and it is a non-hub of `G′`.
- Rank: the triangle's three sides are three of the six joins of a basis of `K⁴`, so independent, and
  a cycle of hinges with independent lines is infinitesimally rigid (Crapo–Whiteley 1982,
  Proposition 3.4, the calculation KT cite for their Lemma 5.4; `lem:cycle-realization-rigid`,
  `theorem_55_cycle`), so the triangle has rank `12`. Ranks add at the cut vertex `c`, and
  `def₃(G) ≥ def₃(G′) + def₃(triangle) ≥ def₃(G′)`, the triangle's deficiency being nonnegative. So
  `rank(G) = rank(G′) + 12 = 6(|V(G)| − 1) − def₃(G′) ≥ 6(|V(G)| − 1) − def₃(G)`, and the upper bound
  holds at every realization. ∎ *(Citation repaired at the second reading, 2026-09-29: KT Lemma 5.4
  asserts only that a cycle on 3 to `D` bodies has some rigid realization.)*

(MC-127)(b)'s "`def₃(G) = f`" is this inequality with the upper bound, and its placement of `y₁, y₂`
"generic in `π_a`" is only the independence of the three points. With (MC-190) and (MC-191) this is
(MC-127)(b) on the route; `deg c ≥ 4` enters only through (MC-191)'s count.

> **(MC-193)** `[PROVED]` *(the count in (MC-191) is the Lean chart's; off the route; written at the
> second reading, 2026-09-29, and so one writer's; not kernel-checked)* In a chart whose seed carries
> the fills of the non-hub normals as free coordinates, (MC-191) holds without its hypothesis on the
> members of the `S_i` and the `w_j`.

*Proof.* Take `(hubNormal, fillHub, fillNbr)` all free. Fix the selectors by re-seeding the first
realization, and re-seed the second at them (T1). The second is then a well-formed chart point with
its own fills, whose chart normal is `n′` at hubs and a nonzero multiple of `n′` at every non-hub
(T1's normal clause). The standing conditions (hub-slot triples, non-hub slot triples, adjacent
points) and the rank rows are nonzero at the first seed; each independence and each dot product is
nonzero at the second. A common non-root over the infinite `K` is a well-formed chart point. Its
realization is nondegenerate, at the rank by the rows and the upper bound, and meets every condition.
No fill is re-chosen. ∎

The landed chart's seed (`PencilSeed.ofCoord`) reads `fillNbr` off `fillHub`'s coordinates, which is
where (MC-191)'s hypothesis enters. With (MC-193) the pendant-triangle step would also run at a hub
of degree 3, the lollipop (MC-127)(c), which route B never meets at a 2-edge-connected graph. Nothing
on the route changes.

> **(MC-187)** `[PROVED]` *(the fibre route's obstruction; sharpens (MC-9); found by formalization,
> MOTIVES recon 2026-09-28; kernel-checked; second-read 2026-09-28)* Let `a ≠ b` be hubs of `G`
> with three common neighbours `x, y, z`. **No realization at which `p_x, p_y, p_z` are independent
> is nondegenerate.** Hence over a planar picture at which `q_x, q_y, q_z` are not collinear, no
> height gives a nondegenerate realization with the configuration points `(q, z)`; and a witness of
> `X₀`'s attaining (a nonzero picture polynomial `P` and, over each good picture, a height polynomial)
> stays a witness after `P` is multiplied by the determinant of the three homogeneous picture points,
> so that every good picture is of that kind.

*Proof.* Conjunct 3 at `x` makes `n_a, n_b` independent, since `a, b ∈ C(x)`. Both annihilate
`p_x, p_y, p_z` (the cross-incidence along each of the six links), so the three independent points
lie in the 2-dimensional `n_a^⊥ ∩ n_b^⊥`. For the configuration points, picture independence lifts
to independence of `(x_w, y_w, z_w, 1)`. The determinant is nonzero at `q_x = (0,0)`, `q_y = (1,0)`,
`q_z = (0,1)`. ∎ At `K_{2,3}`, which is feasible by (MC-123) or L6b, every main picture has
`q_x, q_y, q_z` non-collinear ((MC-9)), so the generic motive cannot come from `X₀` fibre by fibre.
*(Re-derived at the second reading, 2026-09-28: at an admissible picture of `K_{2,3}` the hubs' two
coplanarity conditions are independent exactly when `q_x, q_y, q_z` are not collinear, so `dim L(q)` is
3 there and 4 at a collinear triple, and the main pictures are exactly the non-collinear ones.)*

Off the route, as a consequence: (MC-123)(⇐), (MC-124), (MC-125), (MC-126)(iii)–(v), (MC-127)(c),
(MC-128), (MC-130)'s own induction, (MC-131) and (MC-132), and (MC-13)(c)'s "if" and (MC-14)'s "only if"
directions. All stay proved (or measured); they are not consumed.

**Drivers** (`notes/scripts/w4/`, run from the repository root; `PYTHONHASHSEED=0`, seeds `20260924` / `1`; exact ℚ, ranks mod
`2⁶¹ − 1` only as certificates; `zcore.py` is the shared core):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/zsurvey.py --exh 8 --list` | feasible 79 (18 with a triangle), A′ 33; Z-chart nondegenerate and attaining at 79/79 | 6 s |
| `python3 notes/scripts/w4/e3check.py --exh 8` | 46/46 non-A′ feasible: `def₂ = 3|V| − 3 − 2|E|`, no rigid hub pair | < 60 s |
| `python3 notes/scripts/w4/zears.py --exh 8` | 33/33 A′ Z-ear covered (27 `k = 1`, `δ = 0`; 4 `k = 2`; 2 `k = 3` first steps); 34/34 rank cross-check | 6 s |
| `python3 notes/scripts/w4/zlemma.py --exh 8 --stuck 1500` | (MC-129) asserted at 79 + 555; every graph reduced to a base | 17 s |
| `python3 notes/scripts/w4/zdirect.py --draws 1500` | 176/176 | < 60 s |
| `python3 notes/scripts/w4/zk2k.py` | `K_{2,3..10}` nondegenerate at the target | < 5 s |
| `python3 notes/scripts/w4/zrand.py --seed S`, `zstuck.py --seed S`, `S = 1, 2, 3` (default sizes) | 33 + 25 + 40 distinct A′ graphs on ≤ 13 vertices / 24 + 30 + 31 on ≤ 16, all Z-ear covered; 0 without a closed-cell ear. (The agent's recorded "99 + 471" used sizes it did not record.) | < 5 min total |


