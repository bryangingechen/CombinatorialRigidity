## §(K-main) — the main component `X₀`: over a fixed planar picture the pencil condition is linear in the heights, the flat rank is an exact identity in `dim L(q)`, and the census of `X₀`

Answering `notes/pencil/W4-reopen.md` **P1** (the main-component census, ranked first by the
2026-09-23 strategy re-think; nothing in it commissioned beyond that ranking). Tag `MC-`
(`notes/pencil/labels.md`). Driver: `notes/scripts/w4/maincomp.py`. The object is the smark brief's
§1 pencil configuration (`notes/attacks/smark/brief.md`), read here in an affine chart; the
derivation is the hand-off's (F1)–(F3), written out and checked. **(MC-4)** was not in the
hand-off: it makes the flat rank an exact identity rather than a citation.

**Verdict.** (MC-1)–(MC-6) and (MC-9) are *proven-informally* and elementary. The one citation
any of them uses, Jackson–Jordán's pin-collinear theorem (the smark brief §3(a); published, not
formalized, checked only over `ℝ` — `notes/Phase39-design.md` field-hypothesis recon, row S5; beyond `ℝ`, (MC-33)), is
needed only for the *equality* case of (MC-4)(b), and every use of it below is flagged.
**The census RAN on 2026-09-23. Its outcome is row A′ of the decision table fixed before any run**
(*The census — results*). `X₀` attains at all 10 252 members, including every simple 2EC graph on
at most 8 vertices; there are 0 `SHORT`s. At every drawn point the first-order term alone reached
the target ((MC-7), (MC-8)). The exception is nondegeneracy: at 28 distinct certified-feasible graphs, all
with a proper rigid subgraph, `X₀` supplies the distinct motive but not the generic one ((MC-9)).
The class statements (MC-10) are *open*. What follows is the PI's call.
**2026-09-24 (no census re-run), *After the census*.**
- (MC-11): the gain is **exact** at every admissible point. So (MC-8) is a theorem, and
  (MC-10)(a) ⟺ (MC-10)(b), a plane-framework statement.
- (MC-14): settles (MC-10)(c), with its converse. `X₀` is nondegenerate iff `hcard` holds and no
  `def₂`-rigid subgraph holds two hubs of a common `closedHubNbhd`. This is modulo Jackson–Jordán,
  and it is checked on all of `exh8`.
- (MC-15): `hK`'s habitat has no `def₂`-rigid subgraph at all. So there (MC-10)(a) alone would give
  `hK`'s conclusion.
- Step MC10, the ear step on `X₀`:
  - Closed ears and open ears with `k ≥ 5` are unconditional (MC-20).
  - `k = 4` is proved under strong induction (MC-24)/(MC-25).
  - So **every θ-graph attains on `X₀`** (MC-21), the first infinite class.
  - Open ears with `k ≤ 3` were left open (MC-27). **Step MC13** (a second reading, 2026-09-24)
    closes most of them with the antecedent `X₀(G′ + ear_{k−1})`: `k = 3` in every orbit (MC-45);
    `k = 2` when the generic flags are in orbit (i)/(ii) and `dim U ≠ 1` (MC-46); the chord gives
    every (R_k) (MC-44); `k = 1` at `δ ≥ 5` (MC-49), (MC-31); every short ear at `δ = 0` (MC-54). Open: (MC-51)(a)–(c) at `δ ≥ 1`. On `hK`'s
    habitat only `k = 1`, `δ ≤ 4` remains, modulo Jackson–Jordán (MC-48).
  - The relative-dof conjecture (MC-23) is certified on ≤ 7 vertices, and reduced to (MC-10)(a)
    at `G′` and `G′ + ab` when `a ≁ b` and `δ ≤ 5` (MC-44).
  - A second reader re-derived Steps MC7–MC9; its fixes are applied.
  - The ear-step claims (MC-16)–(MC-27) were checked by the coordinator; Step MC13's second reader
    re-read (MC-16), (MC-17), (MC-22) and (MC-26), without re-deriving them.
- Step MC11 (from the 2026-09-24 feasibility recons of W4-reopen's unranked directions), the
  split-off step on `X₀`: putting the split vertex on the line of its neighbours gives rank exactly
  `+5` and a point of `X₀` (MC-28)–(MC-30), so **`X₀(G.splitOff)` attaining puts `X₀(G)` within one of
  its target, and attaining when `δ ≥ 5`** (MC-31); the missing `+1` is first order at every
  instance tested, not a class statement (MC-32).
- Step MC12, the contraction step on `X₀`: Katoh–Tanigawa's contraction case in `X₀` form. For a
  proper rigid `W` with `G/H` simple, **`X₀(H)` and `X₀(G/H)` attaining give `X₀(G)` attaining**,
  under two linear-algebra conditions checked per graph at one exact picture (MC-39); OPEN as class
  statements (MC-41). Every sampled run where they are certified attains (MC-40). **Second-read
  2026-09-24**: confirmed, (MC-37) steps 3–4 filled in, and at a `def₂`-rigid core Jackson–Jordán is
  needed only at `H` and `G/H` ((MC-59)(c3)), which makes the `K₄` necklaces citation-free (MC-60)(b).
- Step MC14, the reach of the `X₀` induction (`w4/x0arms.py`): cut vertices and bridge chains are
  fibre products (MC-52), (MC-53); an open ear with `k ≤ 4` at `δ = 0` needs no antecedent (MC-54),
  closing (MC-51)'s cells there; a `def₂`-rigid core needs no contraction certificate, modulo
  Jackson–Jordán (MC-59), so **every `K₄` necklace attains on `X₀`** (MC-60), with no citation at all
  since the second reading. **Every tested graph is
  covered** — all 7 980 simple 2EC graphs on ≤ 8 vertices (MC-57), every census population (MC-58),
  `N(3..8)` — **but that is a measurement: there is no coverage theorem** (MC-61). Proving one, both
  its structural and its certificate half, is the remaining problem for this strategy. Second-read
  2026-09-24: (MC-52)–(MC-55) and the `a ≁ b` reading confirmed; (MC-22) and (MC-55)(iii) repaired.
- *Jackson–Jordán beyond `ℝ`* (MC-33): a second reading finds every step of their proof field-free
  after two small repairs and one bypass (`INFORMAL`), and `jjchar.py` exhibits (MC-4)(b)'s
  equality in characteristics 2, 3, 101 and 10 007 at every simple 2EC graph on ≤ 8 vertices.
**What would change this:** an admissible `q` where `maincomp.py`'s (MC-4) assert fires (the
identity is false), an error in the Plücker bookkeeping of *Step MC3* (checked per instance by the
(MC-3) assert), or a `SHORT` in an extended population.

**Standing hypotheses (H).** `G` is finite, simple and connected, with minimum degree `≥ 2`. `K` is
an infinite field. A **planar picture** is `q : V → K²`, `q_v = (x_v, y_v)`; it is **admissible**
if `q_u ≠ q_v` for every edge `uv` and `q(N[v])` is not collinear for every `v` (`|N[v]| ≥ 3` by the
minimum degree). A configuration in the affine chart is `p_v = (x_v, y_v, z_v, 1) ∈ K⁴`, written
`p = (q, z)` with `z ∈ K^V` the **heights**. `Aff(q) ⊆ K^V` is the 3-dimensional space of heights
`z_w = αx_w + βy_w + γ`, the restrictions of global affine functions (dimension 3 because an
admissible `q` is not collinear).

---

### Step MC1 — the pencil condition is linear in the heights

> **(MC-1)** `[PROVED]` *(the hand-off's (F1))* Let `q` be admissible. Then `p = (q, z)` has every
> closed neighbourhood coplanar **iff** `z ∈ L(q)`, where
> `L(q) := {z ∈ K^V : for every v, z|N[v] is the restriction to q(N[v]) of an affine function of K²}`.
> Every such `p` is a pencil configuration: adjacent points are distinct, and the plane `π_v` is unique
> and non-vertical at every vertex. `L(q)` is a linear subspace containing `Aff(q)`.

*Proof.* (⇐) If `z_w = α_v x_w + β_v y_w + γ_v` on `N[v]`, the points of `N[v]` lie on the plane
`z = α_v x + β_v y + γ_v`. (⇒) Let `ax + by + cz + d = 0` contain `N[v]`'s points. If `c = 0` then
`ax + by + d` vanishes on the non-collinear set `q(N[v])`, forcing `a = b = d = 0`. So `c ≠ 0` and
`z = −(ax + by + d)/c` on `N[v]`. The plane is unique because `q(N[v])` is not collinear. Adjacent
points are distinct because `q_u ≠ q_v`. Linearity: the condition at `v` says `z|N[v]` lies in the
image of the evaluation map `Aff(K²) → K^{N[v]}`. That map is injective (non-collinear), so the
image is a 3-dimensional subspace, of codimension `deg v − 2`. ∎

So `dim L(q) ≥ max(3, 3|V| − 2|E|)`. Only hubs impose conditions: `deg v − 2 = 0` at a degree-2 vertex.

### Step MC2 — the main component `X₀`

> **(MC-2)** `[PROVED]` *(the hand-off's (F2))* Let `ℓ₀` be the minimum of `dim L(q)` over
> admissible `q`, and let `U` be the set of admissible `q` with `dim L(q) = ℓ₀`. Then `U` is a
> nonempty Zariski-open subset of `K^{2V}`, `B := {(q, z) : q ∈ U, z ∈ L(q)}` is a vector bundle over
> `U`, and its closure `X₀` is irreducible of dimension `2|V| + ℓ₀`. `X₀` contains the **flat
> configurations** `(q, 0)`, `q ∈ U`. Rank is lower semicontinuous, so the maximum of the molecular
> rank over `B` is attained on a dense open subset of `B`. One point of `B` at the target rank
> therefore proves that `X₀`'s generic point attains. It also gives, at `G`, a rank-attaining pencil
> configuration with adjacent points distinct: the rank and distinctness content of
> `HasDistinctPencilRealization K 3 G`, via the rank bridge (smark brief §3.3(a)).

*Proof.* Admissibility is a finite conjunction of non-vanishing conditions (`q_u − q_v ≠ 0`, a
nonzero `3 × 3` minor of `[1, x_w, y_w]_{w ∈ N[v]}`), so it is open. It is nonempty because `K` is
infinite. By (MC-1), over an admissible `q`, `L(q)` is the projection to `z` of the kernel of the
matrix `M(q)` of the linear system `z_w = h_v(q_w)` (`v ∈ V`, `w ∈ N[v]`) in the unknowns `(z, h)`,
`h_v ∈ Aff(K²)`. The projection is injective because `h_v` is determined by `z` on the
non-collinear `q(N[v])`. `M(q)` has entries linear in `q`, so `rank M(q)` is lower semicontinuous
and `U` (maximal rank) is open. On `U` the rank is constant, so the kernel is a vector bundle.
Its total space is irreducible because `U` is. The zero section lies in `B`. The last two sentences
of the claim are semicontinuity on the irreducible `X₀`. ∎

A point `(q, z)` with `q` admissible but `q ∉ U` is still a pencil configuration by (MC-1), so it is
still a witness for the conjecture at `G`, but it lies on a jump stratum and is not certified to be
on `X₀`. The driver certifies `q ∈ U` through (MC-4)(b): `dim L(q) = 3 + def₂` is the least value
`dim L` can take, so at such a `q` we have `ℓ₀ = 3 + def₂` and `q ∈ U`.

For the **generic** motive the point must also satisfy `IsNondegPencilRealization`'s four
conjuncts (`Motive.lean`, `IsNondegPencilRealization`). On `B`, conjunct 1 (the panel realization),
conjunct 2 (adjacent points distinct) and conjunct 4 (closed neighbourhoods of non-hubs
independent: three non-collinear points) hold by (MC-1). **Conjunct 3** (the normals of
`closedHubNbhd v` linearly independent) is not automatic on `X₀`. The census reports it per
instance.

### Step MC3 — the hinges are affine in the heights

> **(MC-3)** `[PROVED]` *(the hand-off's (F3))* For fixed `q`, the hinge extensor
> `C_e = p_u ∧ p_v` of an edge `e = uv` is affine in `z`. In the Plücker order `(01, 02, 03, 12, 13, 23)`
> of `exactcore.PL`,
> `C_e = (x_u y_v − y_u x_v, 0, x_u − x_v, 0, y_u − y_v, 0) + (0, x_u z_v − z_u x_v, 0, y_u z_v − z_u y_v, 0, z_u − z_v)`,
> and the second term is linear in `z`. Hence the **augmented motion matrix** `A(q, z)` (rows `(e, k)`:
> `(m_u − m_v − ω_e C_e)_k`; columns `6|V| + |E|`) is `A₀(q) + A₁(q; z)`, with `A₁` linear in `z` and
> supported on the `ω` columns. If every `C_e ≠ 0`, then `rank A = |E| + rank R`, where `R` is the
> 5-rows-per-hinge rigidity matrix (the landed `rigidityRows` model, `kbare_common.build_rigidity`).
> The rank at `(q, z)` is invariant under `z ↦ tz + a` for `t ≠ 0` and `a ∈ Aff(q)`, so on the fibre
> it depends only on the class of `z` in `P(L(q)/Aff(q))`.

*Proof.* `p = (x, y, z, 1)`. Each Plücker coordinate `p_u[i] p_v[j] − p_u[j] p_v[i]` has at most one
of `i, j` equal to `2` (the `z` index), so it has no `z_u z_v` term. On `ker A`, `ω_e` is determined
by `m` whenever `C_e ≠ 0`. So `ker A ≅ {m : m_u − m_v ∈ span C_e for all e} = ker R`, and
`rank A = 6|V| + |E| − dim ker R = |E| + rank R`. The map `(x, y, z) ↦ (x, y, tz + αx + βy + γ)` is an
affine, hence projective, transformation of `K³` when `t ≠ 0`, and the molecular rank is
projectively invariant. ∎

The quadric condition on hinge lines (the Klein quadric) never appears: the parametrization by
`(q, z)` absorbs it, and the rank question over a fixed `q` is the generic rank of an affine matrix
family over the linear space `L(q)`. The last sentence of (MC-3) says the fibre is effectively
`P^{ℓ₀ − 4}`. Under Jackson–Jordán (MC-4(b)) that is `P^{def₂ − 1}`: at `def₂ = 1` (for example `C₄`)
every non-flat point of the fibre has the same rank.

### Step MC4 — the flat rank is an identity in `dim L(q)`

> **(MC-4)** `[PROVED]` Under (H), at every admissible `q`:
> **(a)** `rank R(q, 0) = 6|V| − 3 − dim L(q)`, exactly;
> **(b)** `dim L(q) ≥ 3 + def₂(G)`, where `def₂(G) = max_P [3(|P| − 1) − 2d(P)]` (Lean `deficiency G 2`);
> **(c)** hence `rank R(q, 0) ≤ 6(|V| − 1) − def₂(G)`, with **equality iff `dim L(q) = 3 + def₂(G)`**.
> The corpus's flat law `rank(flat) = 6(|V|−1) − def₂` (§(K-bare-ext) (BE-20)(ii), inheriting
> (BE-13); the smark brief §3(a)) is therefore **exactly** the statement that equality holds in (b)
> at generic `q`. That equality is where the Jackson–Jordán theorem enters, and it is the only place.

*Proof.* At `z = 0`, (MC-3)'s formula puts every `C_e` in `W_Π := span(e₀₁, e₀₃, e₁₃)`, the Plücker
coordinates of lines in the plane `Π = {z = 0}`. Split `K⁶ = W_Π ⊕ W′`, with
`W′ = span(e₀₂, e₁₂, e₂₃)`, and write `m_v = (m_v^Π, m_v′)`. The motion condition
`m_u − m_v ∈ span C_e` splits into `m_u′ = m_v′` (three conditions) and
`m_u^Π − m_v^Π ∈ span C_e` (two conditions, since `C_e ≠ 0`).
*The glued block.* Because `G` is connected, `m′` is constant: a 3-dimensional contribution to the
kernel.
*The 2-condition block.* `W_Π = Λ²Π̂` with `Π̂ = span(e₀, e₁, e₃) ≅ K³`, and `p̂_w = (x_w, y_w, 1)`.
Identify `Λ²K³ ≅ (K³)^∨` by `a ∧ b ↦ det(a, b, ·)`, and `(K³)^∨` with the affine functions `h` on
`K²` (`h(x, y) = ⟨h, (x, y, 1)⟩`). Under this identification `span(p̂_u ∧ p̂_v)` is the line of affine
functions vanishing at `q_u` and `q_v`. So the block's kernel is
`F(q) = {(h_v)_v : (h_u − h_v)(q_u) = (h_u − h_v)(q_v) = 0 for every edge uv}`.
*The bijection `F(q) ≅ L(q)`.* Define `Φ(h)_w := h_w(q_w)`. For `u ∈ N(v)`: `Φ(h)_u = h_u(q_u) = h_v(q_u)`,
and `Φ(h)_v = h_v(q_v)`. So `Φ(h)|N[v] = h_v|q(N[v])` is affine, and `Φ(h) ∈ L(q)`. Conversely, for
`z ∈ L(q)` let `Ψ(z)_v` be the unique affine interpolant of `z` on the non-collinear `q(N[v])`. For an
edge `uv`, both `q_u` and `q_v` lie in `N[u] ∩ N[v]`, so `Ψ(z)_u` and `Ψ(z)_v` agree there, and
`Ψ(z) ∈ F(q)`. The composites are the identity: `Φ∘Ψ` by construction, `Ψ∘Φ` by uniqueness of the
interpolant. Hence `dim ker R(q, 0) = 3 + dim L(q)`, which is (a).
*(b).* The 2-condition block has 3-dimensional bodies and 2 rows per edge. For a partition `P`, the
rows of edges inside a part vanish on part-wise constant `h` (a `3|P|`-dimensional space), so they
have rank `≤ 3|V| − 3|P|`. The crossing edges contribute `≤ 2d(P)`. So
`dim F(q) ≥ 3|P| − 2d(P) = 3 + [3(|P| − 1) − 2d(P)]`; maximize over `P`.
*(c)* is (a) and (b) together. ∎

The bijection `Φ` is the classical correspondence between liftings of a plane picture and
motions of its dual framework: the projective duality of Maxwell–Cremona and scene analysis
(Whiteley; Crapo–Whiteley). **Citation to be verified before transcription.** The proof above is
self-contained and does not use it.

### Step MC5 — consequences, none of which uses Jackson–Jordán

> **(MC-5)** `[PROVED]` Under (H):
> **(i)** `def₃(G) ≤ def₂(G)`. Partition by partition, `[6(|P|−1) − 5d] − [3(|P|−1) − 2d] =
> 3(|P| − 1 − d(P)) ≤ 0`, because the parts of a connected graph are joined by `≥ |P| − 1` crossing
> edges. (This is BZAVOID's `def₂ ≥ def₃`, §(K-bare-ext) (BE-15); recorded here with its one-line
> proof because (ii) uses it.)
> **(ii)** The flat configuration at an admissible `q` attains `6(|V|−1) − def₃` **iff**
> `dim L(q) = 3 + def₃`, iff equality holds in (MC-4)(b) at `q` **and** `def₂ = def₃`.
> **(iii)** *(the W4-reopen "dichotomy worth trying to prove", on `X₀`)* If `X₀` is **flat** — that
> is, `ℓ₀ = 3`, so every configuration of `B` is planar — then `def₂ = def₃ = 0`, and the flat
> configuration at every admissible `q` with `dim L(q) = 3` has rank `6(|V| − 1)`: `G` is rigid, and
> `X₀` attains.

*Proof of (ii), (iii).* (ii): (MC-4)(a) gives flat rank `= 6|V| − 3 − dim L(q)`, which equals
`6(|V| − 1) − def₃` iff `dim L(q) = 3 + def₃`. By (MC-4)(b) and (i), `dim L(q) ≥ 3 + def₂ ≥ 3 + def₃`.
(iii): `ℓ₀ = 3` and (MC-4)(b) give `def₂ ≤ 0`, so `def₂ = 0`, and `def₃ = 0` by (i). Then
(MC-4)(a) gives flat rank `6|V| − 6`. ∎

**What (MC-5)(iii) does to §(K-bare-ext) (BE-23)(ii).** BINDUC measured *"forced flat ⇒
`def₂ = def₃`"* under an *aggressive* combinatorial plane-forcing closure. It reported the largest
`def₂` at a forced-flat graph as **5**, and flagged the closure as over-claiming. (MC-5)(iii) proves
the `X₀` form outright: flatness of `X₀` forces `def₂ = 0`, not merely `def₂ = def₃`. Any graph a
forcing closure flags as flat with `def₂ > 0` therefore has **non-flat** configurations on `X₀`,
because `dim L(q) ≥ 3 + def₂ > 3` at every admissible `q`. Such a flag is an over-claim of the
closure, as BINDUC said it might be. That section's statement is not changed; its measured
*"forced flat ⇒ `def₂ = def₃`"* is subsumed on `X₀`.

**The by-product for (α), restated with its dependency.** The W4-reopen hand-off's by-product —
*"wherever `def₂ = def₃` the flat configuration already attains with adjacent points distinct"* —
is (MC-5)(ii) **plus Jackson–Jordán at `G`**. Without the citation, what holds is: wherever
`dim L(q) = 3 + def₃` at some admissible `q`, the flat configuration at `q` attains with adjacent
points distinct. The census measures that equality directly (the `JJ` column).

### Step MC6 — the first-order structure at the flat point is a symmetric form on the lifting space

*Written after the spec commit `9e8aaec2`, while the census ran.* It changes no row of the decision
table.

At `(q, 0)` the motion space is the glued block (3 dimensions, trivial) plus `F(q) ≅ L(q)`, and the
perturbation directions are `L(q)` too. The **first-order gain** in direction `z` is
`rank(S₀ᵀ A₁(z) K₀)`, with `K₀` and `S₀` the kernel and left kernel of `A₀`. It lower-bounds
`rank A(q, z) − rank A₀` (and, by (MC-11)(ii), equals it). The reason: `P(A₀ + tA₁)Q` in a basis adapted to `A₀` has Schur
complement `t(S₀ᵀA₁K₀ + O(t))`, and by (MC-3) `rank A(q, tz)` does not depend on `t ≠ 0`. The
needed gain is `def₂ − def₃`. The step below computes it.

**Notation.** An affine function `h = αx + βy + γ` is written as the vector `ĥ = (α, β, γ)`, so that
`h(q_w) = ĥ · p̂_w` with `p̂_w = (x_w, y_w, 1)`. For an edge `e = (u, w)` (in `edges` order), set
`ℓ_e := p̂_u × p̂_w ≠ 0`. A flex `h ∈ F(q)` has `ĥ_u − ĥ_w = ω_e(h) ℓ_e`. `Z₁(G)` is the cycle space
(signed edge vectors, zero net flow at every vertex).

> **(MC-6)** `[PROVED]` Under (H), at an admissible `q`, define the bilinear map
> `β : F(q) × F(q) → (Z₁(G) ⊗ K³)^∨` by `β(k, h)(μ) := Σ_{e = (u,w)} det(μ_e, k̂_w, ĥ_u − ĥ_w)`.
> **(i)** `β` is **symmetric**. **(ii)** `β(k, h) = 0` whenever `k` or `h` is a trivial (constant)
> flex, so `β` descends to `Sym²(L(q)/Aff(q)) → (Z₁ ⊗ K³)^∨`. **(iii)** For `z ∈ L(q)`, the
> first-order gain in direction `z` equals `rank β(Ψz, ·)`, with `Ψ` the bijection of *Step MC4*.
> So `X₀` attains **to first order** iff some `z ∈ L(q)` has
> `dim ker β(Ψz, ·) = 3 + def₃` on `F(q)`, i.e. `def₃` beyond the trivial flexes.

*Proof.* (iii) first. By the block split of *Step MC4*, the left kernel of `A₀` is the direct sum
of the 2-condition block's stresses (supported on `W_Π`) and the glued block's stresses. The
latter are `λ′ ∈ (K³)^E` with zero net flow at every vertex, i.e. `Z₁ ⊗ K³`, supported on `W′`
(the `ω`-column constraint `λ_e · C_e = 0` involves only `W_Π`). `A₁(z)` is supported on the `ω`
columns, and by (MC-3) its values `−C′_e(z)` lie in `W′`, where
`C′_e = (x_u z_w − z_u x_w, y_u z_w − z_u y_w, z_u − z_w) = J a_e`,
`a_e := z_w p̂_u − z_u p̂_w`, `J = diag(1, 1, −1)`. So only glued-block stresses pair. In `K₀`, the
trivial `W′` motions have `ω = 0` and pair to zero. What is left is
`sᵀA₁(z)f = −Σ_e ⟨Jλ′_e, a_e⟩ ω_e(h)`. With `k = Ψz`, (MC-1) gives `z_u = k̂_w · p̂_u` and
`z_w = k̂_w · p̂_w`, because `u, w ∈ N[w]`. Hence `a_e = k̂_w × ℓ_e` by `a × (b × c) = b(a·c) − c(a·b)`,
and `ω_e(h) a_e = k̂_w × (ĥ_u − ĥ_w)`. Put `μ := −Jλ′`; `J` preserves zero net flow. Then
`sᵀA₁(z)f = Σ_e det(μ_e, k̂_w, ĥ_u − ĥ_w) = β(k, h)(μ)`. The identification of the `W_Π`-coordinates
of a flex with `ĥ` is the linear map `(c₀₁, c₀₃, c₁₃) ↦ (c₁₃, −c₀₃, c₀₁)`. It sends
`C_e|_{W_Π}` to `ℓ_e`, so `ω_e` is the same scalar in both pictures.
(i). Write `ĥ_u = ĥ_w + bℓ_e` and `k̂_u = k̂_w + aℓ_e`. Then
`det(μ_e, k̂_u, ĥ_u) − det(μ_e, k̂_w, ĥ_w) = det(μ_e, k̂_w, ĥ_u − ĥ_w) − det(μ_e, ĥ_w, k̂_u − k̂_w)`,
because the `ab` term has `ℓ_e` twice. Summing over `e`, the left side is
`Σ_v det(net flow of μ at v, k̂_v, ĥ_v) = 0`. So `β(k, h)(μ) = β(h, k)(μ)`.
(ii). A constant `h` has `ĥ_u − ĥ_w = 0`. A constant `k` then follows by (i). ∎

**Checked in the driver** (`beta_check`, run whenever `--gain` is given): `rank β(Ψz, ·)` over `ℚ`
equals the Schur-pairing gain, asserted per instance. Also asserted: symmetry on two basis pairs,
and vanishing on the constant flex. This was added to `maincomp.py` after the first census runs.
The re-runs with it in place are byte-identical to those runs (*The census — results*).

**What (MC-6) is for.** The census (below) finds the first-order gain **equal to `def₂ − def₃` at
every instance tested**. If that is a theorem, the rank question on `X₀` becomes a statement
about **plane** frameworks only: for generic `q` and `z` in the lifting space, the symmetric form
`β(Ψz, ·)` on the `def₂`-dimensional space `L(q)/Aff(q)` has kernel of dimension exactly `def₃`
(it is `≥ def₃` always, by the target bound). This is the P3 candidate. It is **not** argued here.

---

### The census — spec, fixed before any census run

**Question.** On each population below, does `X₀`'s generic point attain `6(|V|−1) − def₃`?

**Instrument** (`maincomp.py`; its docstring states the sampler support per `HARNESS.md`
*Evidence*). Per draw: `q` uniform on integers in `[−30, 30]`, rejected until admissible; an exact
basis of `L(q)`; `z` a uniform `[−30, 30]` integer combination of it. The rank is computed mod
`2⁶¹ − 1`. Since `rank_p ≤ rank_ℚ ≤ target`, **`rank_p = target` is a certificate**: an exhibited
attaining point, a theorem for that graph. A shortfall is recomputed in exact ℚ and redrawn, up to
4 more draws. The best draw is a **lower bound** on `X₀`'s generic rank, never a measurement of it.
A `SHORT` verdict is therefore *measured, not proved*, and travels with its cap (5 draws, scale 30).
Asserted per draw: (MC-1) forward (every closed neighbourhood coplanar, adjacent points distinct);
(MC-3) exact affineness along the fibre (first draw of each instance); (MC-4)(a) and (b).
Reported: `def₂`, `def₃`, `dim L(q)`, the flat rank, `JJ` (`dim L(q) = 3 + def₂`, which also
certifies `q ∈ U`, *Step MC2*), the rank, and the verdict. Also reported: whether the best draw
satisfies all four `IsNondegPencilRealization` conjuncts (`flanks.nondeg_conjuncts`, failing
conjunct named) and, with `--gain`, the first-order gain of *Step MC6*.
**Oracles:** `def₃` by the (6,6) pebble game and `def₂` by the (3,3) pebble game on `2G`. Both are
checked against brute-force partition maxima at `n ≤ 8` in `--selftest`, and `def₃` also against
`kbare_common.exact_deficiency`.

**Populations** (`maincomp.py --pool NAME`). Every member is kept iff it is simple and 2EC.
Counts were measured by building each population, which involves no census run.
- `battery` (9): `C₄`, `C₅`, `C₇`, `K₄`, `K_{3,3}`, `θ(2,2,2)`, `θ(3,4,5)`, `θ(5,3,4)`, `W19`.
- `exh8` (7 980): **every isomorphism class** of simple 2EC graphs on 3–8 vertices
  (1 / 3 / 11 / 60 / 502 / 7 403). They are generated in-driver by vertex augmentation with a
  stdlib canonical form. The connected-graph counts match OEIS A001349 and the 2EC counts match
  A007146 through `n = 8` (both asserted in `--selftest`). **This is the only exhaustive
  population.** It contains every small member of every habitat below.
- `thetas` (109): `θ(a, b, c)`, `a ≤ b ≤ c`, `b ≥ 2`, `a + b + c ≤ 16`. This covers the tight
  habitat thetas (`Σ = 12`) and smark's `thetacores.py` shapes (`Σ = 13`), rebuilt with
  `pitch.theta_edges` rather than imported.
- `habitats` (888): the kernel-(K) class shapes. These are `lambda.habitat_specs` (`θ(3,4,5)`,
  `NT21`, `NT24`, `NT30`), `kslidecl.MEMBERS` (7), and the exhaustive `G* = K₄` stratum of
  `kslidecomb.py --k4full` (877 shapes).
- `smark` (81 built, 78 kept): `G = side + ear_m`, `m ∈ {2, 3, 4}`, over the 27 sides of smark's
  `splitoff.py --sides all`. They are imported read-only from `notes/attacks/smark/drivers/`
  (`sideprof`, `adversarial`, `earcompose.ear_edges`). The 3 dropped members are not 2EC.
- `residuals` (260): the 255 recorded residual inhabitants (`wtri.recorded_pool()`, the (RS-12)
  pool, `|V|` 19–31), plus `W19`, `R20`, `S29` (`saferes.w29()`), `T32` (`weloc.T32`) and `NT21c3`.
- `peels` (928): `bgenuine.family()`, `G = H₁ + H₂` (`K₄` R-sides glued to free sides). The
  392 forced-coincident-flag peels are marked, and the count is asserted.
- **W4 branch 2** (the P2 population) is not a separate list. It is the members of all the above
  that are certified infeasible (`nogood_subdiv.provably_infeasible`, a *sufficient* certificate
  only) and have a proper rigid subgraph (`nogood_subdiv.rigid_vertex_sets`). The summary lists its
  `def₂ > def₃` members; by the hand-off's P2 those are (α)'s whole content.
- **Not included, with the reason:** smark's Case-2 hub graphs (`case2m2.CASES`: D3, E13, E15,
  E55, T10, …) are reduced sides `Γ` with leaves and connectors, not graphs `G`. The corpus has no
  canonical completion of them to a full `G`, and their 2-cores are trees or hub cycles (smark
  S27(vi)). smark's `census.py` girth-`≥ 7` pieces are also left out: their kept set is replayable
  only through that driver's own rng.

Each member is also classified as `feas` (`provably_feasible`: `hcard` and triangle-free, the
landed-sufficient criterion), `infeas` or `middle`, and as `rigid` or `norigid` (a proper rigid
subgraph exists or not). These classes let the summary separate the hand-off's habitats.

**Decision table** (the hand-off's, made operational; **written before any census run**):

| outcome | condition | what follows (nothing without a PI call) |
|---|---|---|
| **A** | every instance of every population certified `ATTAINS` | P3 becomes "prove the rank on `X₀`", an architecture change; `kres`, the contraction kernels and smark's O7e become unnecessary in principle; the PI decides what to stop |
| **A′** | as A, but at some **feasible** graph the attaining draws all fail conjunct 3 | `X₀` supplies the distinct motive there but not the generic one; P3 must also produce a nondegenerate point on `X₀` or elsewhere |
| **B** | some `G` is `SHORT` after all draws, and a project chart attains at `G` (an attaining witness recorded in the corpus, or one produced by an existing sampler run on `G`) | witnesses live off the main component; every generic-point strategy dies at those `G`; they are the hard core, and P3 asks which component attains and why |
| **C** | some `G` is `SHORT` after all draws, and no chart the project has attains at `G` | a counterexample candidate. First strengthen the `SHORT` (more draws, larger scale, an exact symbolic rank if feasible), then check the special components: the admissible `q` where `L(q)` jumps, and the non-admissible charts (vertical planes) |

The census ends at this table.

**Disclosure — the order of work.** Before this spec was written, a prototype of the driver's
core (not retained; `maincomp.py` supersedes it) was run on seven named graphs: `C₄`, `K₄`,
`K_{3,3}`, `θ(2,2,2)`, `θ(3,4,5)`, `θ(5,3,4)`, `W19`. It showed `ATTAINS` and `JJ` at all seven. It
motivated (MC-4)(a), which was then proved. Those seven are re-run in the committed `--battery`
mode. No population above was run before this table was fixed.

---

### The census — results (2026-09-23): outcome **A′**

*Run after the spec commit `9e8aaec2`. Seed `20260923`, 1 draw and up to 4 retries, scale 30,
`--gain`. Commands and times: `notes/scripts/README.md` §3. The first runs used the spec-commit
driver. The figures below come from re-runs with three additions: (MC-6)'s check, the corrected
gain yardstick (the needed gain at the drawn `q`, not `def₂ − def₃`), and the genericity column.
The re-runs differ from the first runs only in those lines and the wall-clock `built in` line;
`exh8`'s first run was stopped before it finished, so it has no such comparison. The landed
driver differs from the one that ran the census pools only by docstrings and the `--draw0`,
`--jjprobe` and `--k23` modes. `battery`, `thetas` and `smark` were re-run on it byte-identically,
apart from the timing line.*

> **(MC-7)** `[CONSTRUCTED]` `maincomp.py --pool` **`X₀` attains at every member of every population:
> 10 252 members, 0 `SHORT`.** Some graphs recur across populations: `W19`, `θ(3,4,5)`, and the
> small members inside `exh8`. Each `ATTAINS` is an exhibited point of `B` at the target rank
> (the `JJ` column certifies `q ∈ U`, *Step MC2*), i.e. a proof for that graph that `X₀`'s generic
> point attains. At the 3 members whose attaining census draw failed `JJ` (2 peels and
> `x8_261840905`), `--jjprobe` exhibits an attaining point over a certified `q ∈ U` instead. With it comes a rank-attaining pencil configuration with adjacent points distinct.
>
> | population | members | `def₂ > def₃` | `X₀` attains | nondegenerate at the attaining draw | class (`feas`/`infeas` × `rigid`/`norigid`) |
> |---|---|---|---|---|---|
> | `battery` | 9 | 6 | 9 | 6 (fails conjunct 3: `K₄`, `K_{3,3}`, `θ(2,2,2)`) | 5 feas-norigid, 2 feas-rigid, 2 infeas-rigid |
> | `thetas` | 109 | 106 | 109 | 96 (13 fail conjunct 3) | 38 feas-norigid, 59 feas-rigid, 12 infeas-rigid |
> | `smark` | 78 | 78 | 78 | 78 | 65 feas-norigid, 13 feas-rigid |
> | `habitats` | 888 | 888 | 888 | 888 | 888 feas-norigid |
> | `residuals` | 260 | 260 | 260 | 260 | 260 feas-rigid |
> | `peels` | 928 | 928 | 928 | 0 (all fail conjunct 3; all infeasible) | 928 infeas-rigid |
> | `exh8` | 7 980 | 134 | 7 980 | 46 (7 934 fail conjunct 3, 7 858 of them certified infeasible) | 6 feas-norigid, 55 feas-rigid, 7 858 infeas-rigid, 43 infeas-`rigid?` (the rigid-subgraph enumeration's branch cap), 18 middle-rigid |
>
> The `exh8` row is **exhaustive**: every simple 2EC graph on at most 8 vertices has `X₀` attaining.
> That is a finite theorem, 7 980 exhibited certificates. Each certificate is over `ℚ`, so it
> proves its statement over every field of characteristic 0. Positive characteristic is not
> addressed (smark brief §2, O11). **Draw-level shortfalls:** 6 members fell short by 1 at their
> first draw and attained at a retry (`--draw0`: `θ(1,3,7)`, `pool210`, `pool218`, `pool228`,
> `T32`, `x7_1986081`). Only `x7_1986081`'s first `q` was a jump point
> (`dim L(q) > 3 + def₂`). The other five fell short at a `q ∈ U`: an unlucky `z` or `q` for a
> condition the dimension count does not see. Semicontinuity makes such draws expected, and they
> bound nothing. `JJ` failed at 4 first draws (2 peels, 2 in
> `exh8`). All four are unlucky `q`: one fresh `q` exhibits `dim L(q) = 3 + def₂` at each
> (`--jjprobe`). So Jackson–Jordán's equality is exhibited at every member of every population.

> **(MC-8)** `[CONSTRUCTED]` `maincomp.py --gain` **The first-order gain equals the needed gain at every
> drawn point.** At every member where the flat point misses, `rank β(Ψz, ·) = dim L(q) − 3 − def₃`
> at the census draw. The count is 2 266 outside `exh8` and 135 in `exh8`, 2 401 in all. Since
> `rank A₀ + gain ≤ rank A(q, z) ≤ target`, each equality is a certificate that **the first-order
> term alone** proves attainment at that `q`. No higher-order term was needed anywhere.

> **(MC-9)** `[PROVED]` *(checked by `maincomp.py --k23`, 20/20)* **The A′ mechanism at
> `K_{2,3} = θ(2,2,2)`.** This graph is certified feasible (`hcard`, triangle-free) and rigid, with
> a proper rigid `C₄`. On `X₀`, the hub planes `π_a` and `π_b` both contain the three non-hub points.
> At an admissible `q` those points are not collinear, so `π_a = π_b` and conjunct 3 fails at each
> non-hub. `X₀` is flat: `dim L = 3`, `def₂ = 0`. The flat point attains (MC-5)(iii), so `X₀`
> supplies the distinct motive but **not** the generic one. On the jump stratum where `q_x, q_y, q_z`
> are collinear (hubs off the line), `z` restricted to the line is affine (1 condition) and `z_a`,
> `z_b` are free, so `dim L(q) = 4`. That stratum has dimension `2|V| − 1 + 4 = 13 = dim X₀`. Every
> point of `X₀` satisfies the closed condition `π_a = π_b`, and the stratum's generic point does not.
> So the stratum lies on a **second irreducible component**, of dimension `≥ 13`. Its points are
> nondegenerate and attain. The generic motive of `K_{2,3}` lives there. This is the hand-off's "special components (the
> planar positions `q` where `L(q)` jumps)", found at the smallest feasible graph that has one.

**Reading the table against the decision table — outcome A′.** No `SHORT` anywhere, so neither
B nor C. At the certified-feasible graphs, the attaining `X₀` point is nondegenerate except at the
feasible graphs listed by the A-prime watch. Those are `θ(2,2,2)` outside `exh8`, and 28 graphs
in `exh8` (on 5–8 vertices, `θ(2,2,2)` among them). **Every one of them has a proper rigid
subgraph**, so no member of `hK`'s habitat (no proper rigid subgraph) is A′ on this library. Concretely:
- **`hK`'s conclusion** (`HasGenericPencilRealization` at feasible, no-proper-rigid `G`) holds at
  every `feas`-`norigid` member (996 outside `exh8`, 6 inside), at `X₀`'s generic point. Where
  the flat point misses, first-order gain alone reaches the target. This is the conclusion
  outright, with none of `hK`'s antecedents used.
- **(K-res)'s conclusion** holds at all 260 residuals, including `R20`, where the grid route's
  (RS-5) is refuted (§(K-res)). It holds at `X₀` and is nondegenerate.
- **(α)** (W4 branch 2, `def₂ > def₃`, the P2 population) holds at every one of the 928 peels, the
  10 `θ(1, 2, k)` and the 86 `exh8` members: `X₀` gives the distinct motive at each. The P2
  list is **not empty**, but `X₀` covers it, so on this library (α) is a consequence of the `X₀`
  rank statement rather than a kernel of its own.

**What this does and does not establish.** Every figure above is an exhibited certificate for one
graph. **Nothing** here is a class statement. The class statements that would carry an
architecture change are:

> **(MC-10)** `[CONJECTURED]` For every finite simple connected graph `G` of minimum degree `≥ 2`:
> **(a)** `X₀`'s generic point attains `6(|V| − 1) − def₃(G)`;
> **(b)** more strongly, at generic `q` and generic `z ∈ L(q)`,
> `dim ker β(Ψz, ·) = 3 + def₃(G)` on `F(q)`. That is a statement about **plane** frameworks and
> their liftings only ((MC-6));
> **(c)** if `G` is feasible and no two hubs of a common `closedHubNbhd` lie in a common
> `def₂`-rigid subgraph, `X₀`'s generic point is nondegenerate. This is the guess `K_{2,3}`
> suggests ((MC-9)); it is **not tested**, because the driver records only whether a proper rigid
> subgraph exists.

*(2026-09-24: (a) ⟺ (b) by (MC-11). (c) and its converse are (MC-14), `[INFORMAL]` modulo
Jackson–Jordán, so (c) is no longer a guess.)*

(b) ⟹ (a) by *Step MC6*. (a) would prove `HasDistinctPencilRealization K 3 G` for every simple
connected `G` of minimum degree `≥ 2`, **with no induction**. Jackson–Jordán is not needed for
that implication; the census uses it only to certify that a drawn `q` lies in `U`. With
(c), (a) also gives the generic motive wherever `X₀` is nondegenerate. At A′ graphs the generic
motive needs another component, as at `K_{2,3}`.

**What would change this:** a `SHORT` in any extension of the populations (outcome B or C). Since
(MC-11) the first-order gain *is* the rank gain, so a member where it falls below the needed gain
generically is a `SHORT`, refuting (a) and (b) alike. An A′ graph in `hK`'s habitat would break the reading that A′ is confined to graphs
with a proper rigid subgraph.

**Where the A′ exposure sits, and why it may be bounded (a sketch, not a proof).** At `K_{2,3}`
the mechanism is two hubs inside a common subgraph `H` with `def₂(H) = 0`. By (MC-4) plus
Jackson–Jordán applied to `H`, such an `H` is flat on `X₀`. **Whether each of the 28 `exh8` A′
graphs has this shape is not checked.** A `def₂`-rigid subgraph is also `def₃`-rigid
((MC-5)(i)), so in `hK`'s habitat (no proper rigid subgraph) this mechanism can occur only when
`G` itself has `def₂ = 0`. The census found **no** A′ graph without a proper rigid
subgraph. The exposure is therefore W4's generic motive at graphs that have rigid subgraphs,
i.e. branches 3a–3c. The distinct motive is not exposed at all.

**The census ends at this table** (W4-reopen P1); what follows is the PI's call. Outcome A′'s row
says P3 becomes "prove the rank on `X₀`", an architecture change. If (MC-10)(a) holds, the
distinct motive no longer needs smark's O7e programme, `hbareSplit` or (K-bare-c)/(α). On `hK`'s
habitat the same goes for `hK`, given nondegeneracy there. `kres` and (K-c) become unnecessary
wherever `X₀` is nondegenerate, which is all 260 residuals measured. P3 must also supply
nondegenerate points at A′ graphs, whose generic motive lives off `X₀` (as at `K_{2,3}`).

---

### After the census (2026-09-24): the gain is exact, and nondegeneracy on `X₀` is combinatorial

*Written 2026-09-24, continuing W4-reopen P1 at the PI's direction ("see if we can make progress
on the math without a new census first"). No census population was re-run, and no row of the
decision table moves. Two new drivers each check one identity or one equivalence per instance:
`w4/exactgain.py` checks (MC-11), `w4/nondegx0.py` checks (MC-12)/(MC-13).*

#### Step MC7 — the gain is exact

Step MC4 split the motion equations into a `W_Π`-block and a `W′`-block at `z = 0`. **The split
holds at every `z`.** The `W_Π`-coordinates of `C_e` are (MC-3)'s first summand, which does not
involve `z`. The `W′`-coordinates are `C′_e = J a_e(z)` with `a_e(z) := z_w p̂_u − z_u p̂_w`; this is
Step MC6's computation, which uses (MC-3)'s formula and not `z ∈ L(q)`. For `r : E → K³` write
`H(r) := {ω ∈ K^E : Σ_{e ∈ C} σ_C(e) ω_e r_e = 0 for every cycle C}`. This is the angular-velocity
space of the planar body-and-pin framework with pin `r_e` on edge `e`. Write `ℓ_e := p̂_u × p̂_w`, as
in Step MC6.

> **(MC-11)** `[PROVED]` *(the gain is exact)* Let `G` be connected, and let `q` have `q_u ≠ q_w` on
> every edge. Let `z ∈ K^V` be arbitrary: the framework at `p = (q, z)` is molecular (hinges
> concurrent at each `p_v`), not necessarily a pencil framework.
> **(i)** Its motion space is `{(h, m′) : h ∈ F(q), m′_u − m′_w = ω_e(h) J a_e(z) for every e = (u, w)}`.
> Hence its flexes modulo the six trivial ones are `H(ℓ) ∩ H(a(z))`, and
> `rank R(q, z) = 6(|V| − 1) − dim(H(ℓ) ∩ H(a(z)))`. The first factor depends on `q` alone (the
> flat, pin-collinear framework of Step MC4). The heights enter only through the trace pins
> `a_e(z)`, which are linear in `z`. `a_e` is the homogeneous point where the hinge line crosses
> `Π`, with last coordinate `z_w − z_u`. At a horizontal hinge it is the direction's point at
> infinity, scaled by the common height.
> **(ii)** If `q` is admissible and `z ∈ L(q)`, then **exactly**
> `rank R(q, z) = rank R(q, 0) + rank β(Ψz, ·) = 6|V| − 3 − dim ker_{F(q)} β(Ψz, ·)`, at every such
> point, with no genericity.

*Proof.* (i) The six equations `m_u − m_w − ω_e C_e = 0` of edge `e` separate into three
`W_Π`-coordinates and three `W′`-coordinates. The `W_Π`-block does not involve `z`. By Step MC4
its solutions `(m^Π, ω)` are the flat flexes `h ∈ F(q)`, with `ω = ω(h)` because `C_e|_{W_Π} ≠ 0`.
The `W′`-block, `m′_u − m′_w = ω_e J a_e`, is a coboundary equation for `m′ : V → K³`. It is
solvable iff the edge vector `(ω_e J a_e)_e` is orthogonal to `Z₁(G) ⊗ K³`, because over any field
the cut space of `K^E` is the orthogonal complement of the cycle space. Since `J` is invertible,
that is `ω ∈ H(a)`, and then `m′` is unique up to a constant. The constant `h` (3 dimensions) and
the constant `m′` (3 more) are the six trivial motions, and `F(q)/constants ≅ H(ℓ)` by
`h ↦ ω(h)`. Hence `dim ker R = 6 + dim(H(ℓ) ∩ H(a))`. (ii) Step MC6's proof identifies the pairing
of `(ω_e(h) J a_e)_e` with `λ′ ∈ Z₁ ⊗ K³` as `β(Ψz, h)(Jλ′)`, when `z ∈ L(q)` at admissible `q`.
Step MC6's `μ := −Jλ′` carries the opposite sign, which comes from `A₁ = −C′`; vanishing is
unaffected. So
the solvability condition is `β(Ψz, h) = 0` and `dim ker A(q, z) = 3 + dim ker_{F(q)} β(Ψz, ·)`. At
`z = 0` this is `3 + dim F(q)`, and (MC-3)'s `rank A = |E| + rank R` finishes. ∎

**Checked** in exact ℚ at every point drawn. (i) is checked by `exactgain.py --molecular`: 204
points on the battery, every simple 2EC graph on ≤ 5 vertices, and `θ` with sum ≤ 8. The heights
`z` are arbitrary and the pictures are only edge-injective, with scale 1 forcing degenerate
positions; the run takes about 4 s, first as the second reader's scratch check and then committed.
(ii) is checked by `exactgain.py`: 1 830 points over the battery,
every simple 2EC graph on ≤ 6 vertices, and `θ(a, b, c)` with `a + b + c ≤ 9`. The points include
131 jump points `q` (`dim L(q) > 3 + def₂`, found by `--jump 200` at scale 2) and special `z`
(each basis vector of `L(q)`, and a sum of two). The run takes about 50 s. Command:
`python3 notes/scripts/w4/exactgain.py --battery --exh 6 --thetas 9 --jump 200`.

> **(MC-11)(iii)** `[PROVED]` *(what (MC-11) does to the census)* The first-order gain of Step MC6
> *is* the gain, at every admissible point. So **(MC-8) at a draw is equivalent to (MC-7)'s
> attainment at that draw**, and carries no further information. **(MC-10)(a) ⟺ (MC-10)(b).** Two
> further forms are plane-framework statements too. The existence form of the conjecture at `G`
> (one witness, which the Lean motive needs) is: *some admissible `q` and some `z ∈ L(q)` have
> `dim ker_{F(q)} β(Ψz, ·) = 3 + def₃`.* (MC-10)(a) asks for this with `q ∈ U`.
> **(iv)** `[PROVED]` *(reciprocity)* For `z, z′ ∈ L(q)`: `Ψz′` is the vertical part of a motion of the
> framework at `(q, z)` iff `Ψz` is the vertical part of a motion at `(q, z′)`. This is (MC-11)(ii)
> with (MC-6)(i).
> **(v)** `[PROVED]` *(the gain as the image of a quadratic map)* With `P = Ψz`,
> `β(P, P)(μ) = Σ_e det(μ_e, P_w, P_u) = Σ_e μ_e · (P_w × P_u)`. So
> `Q_q : L(q)/Aff(q) → (K³)^E / (B¹ ⊗ K³) ≅ (Z₁ ⊗ K³)^∨`, `z ↦ [e ↦ P_w × P_u]`, is a quadratic map
> with differential `2β(Ψz, ·)`. In characteristic 0 the gain at generic `z ∈ L(q)` equals the
> dimension of the closure of `Q_q`'s image (generic smoothness). So (MC-10)(b) at `q` says: that
> image has dimension `dim L(q) − 3 − def₃`.
> **(vi)** `[PROVED]` *(what the pencil constraint adds to the molecular theorem)* By (i), for fixed
> `q` the heights enter only through the linear family `T_q(z) : H(ℓ(q)) → (K³)^{cycles}`,
> `ω ↦ (Σ_{e ∈ C} σ_C(e) ω_e a_e(z))_C`, with `rank R(q, z) = 6(|V| − 1) − dim ker T_q(z)`. The
> molecular theorem (Katoh–Tanigawa 2011, attaining at generic `p`) says `T_q` reaches kernel
> dimension `def₃` at generic `z ∈ K^V`, for generic `q`. It is formalized in this project over any
> infinite field (ROADMAP §33), and the hinge-concurrent case follows from the panel case by the
> Phase 25 duality; the generic form follows from the existential one by semicontinuity.
> **(MC-10)(a) says exactly that `T_q` keeps that generic rank on the linear subspace
> `L(q) ⊆ K^V`**, where `T_q(z)` is the symmetric `β(Ψz, ·)`. It is a rank question about one
> linear matrix family restricted to one linear subspace.
> **(vii)** `[PROVED]` *(the obstruction is a vector area)* `F(q)` is the space of **parallel drawings**
> of `G` in `K³` with prescribed edge directions: maps `P : V → K³` with `P_u − P_w ∈ K ℓ_e`. For a
> cycle `C` and `c ∈ K³`, `β(P, P)(1_C ⊗ c) = −2 c · A_C(P)`, where
> `A_C(P) := ½ Σ_{(a → b) along C} P_a × P_b` is the **vector area** of the closed spatial polygon
> that `P` traces around `C`. It is translation-invariant, as `β` is on constants. So the 3D
> pencil framework at `(q, z)` has, beyond the trivial ones, exactly the flat flexes `h` whose
> **mixed** vector area with `P = Ψz` vanishes around every cycle. In characteristic 0, by (v),
> (MC-10)(b) says: *for generic `q`, the map `P ↦ (A_C(P))_C` on parallel drawings has generic
> fibre dimension `3 + def₃`.* In
> the edge coordinates `ω` of a parallel drawing, this is
> `A_C = ½ Σ_{i < j along C} (σω ℓ)_i × (σω ℓ)_j`. Its coefficients `ℓ_i × ℓ_j` are the intersection
> points of pairs of edge-lines of the picture `q`, and consecutive edges at `v` meet at `q_v`
> itself.

#### Step MC8 — nondegeneracy on `X₀` is combinatorial

Planes are written in the chart as `π_w : z = α_w x + β_w y + γ_w`, with `P_w := (α_w, β_w, γ_w)`
(so `P = Ψz` on `B`). The normal of `π_w` in `K⁴` is `(α_w, β_w, −1, γ_w)`, up to scale. Linear
independence of such normals is therefore **affine** independence of the points `P_w ∈ K³`. For
`w ∈ N(v)`, `P_w − P_v = ±ω_{vw}(P) ℓ_{vw}`.

> **(MC-12)** `[PROVED]` Under (H), let `q` be in **general position**: admissible, with no three
> points of any `q(N[v])` collinear (a nonempty Zariski-open condition). General position is
> sufficient, not necessary. The proof uses it only for the triple `{q_v, q_{w₁}, q_{w₂}}` at a hub
> `v` with two hub neighbours; at such a collinear triple conjunct 3 fails for every `z`. Let `z ∈ L(q)` and
> `P = Ψz`. Then conjuncts 1, 2 and 4 of `IsNondegPencilRealization` hold at `(q, z)` (Step MC2),
> and **conjunct 3 holds iff**
> **(i)** `|closedHubNbhd v| ≤ 3` for every `v`;
> **(ii)** `P_u ≠ P_w` (that is, `π_u ≠ π_w`, that is, `ω_{uw}(P) ≠ 0`) for every edge `uw` joining two
> hubs;
> **(iii)** `P_a ≠ P_b` (that is, `(ω_{va}(P), ω_{vb}(P)) ≠ (0, 0)`) for every degree-2 vertex `v`
> whose two neighbours `a, b` are both hubs.

*Proof.* Put `S = closedHubNbhd v ⊆ N[v]`. Every plane `π_w`, `w ∈ S`, contains `p_v`, so the
normals lie in the 3-dimensional `p_v^⊥`. So `|S| ≥ 4` fails conjunct 3, which gives (i). `|S| ≤ 1`
is automatic. For `|S| ∈ {2, 3}` there are two cases. If `v` is a hub, `S = {v, w₁(, w₂)}` with
`P_{w_i} − P_v = ±ω_i ℓ_i`. The `ℓ_i` are independent by general position, so the `P`'s are
affinely independent iff every `ω_i ≠ 0`. Each `vw_i` is a hub–hub edge, and every hub–hub edge
`uw` arises this way (in `closedHubNbhd u`); this gives (ii). If `v` is not a hub, then
`deg v = 2` and `S ⊆ {a, b}`. Then `P_a − P_b = ±ω_{va} ℓ_{va} ∓ ω_{vb} ℓ_{vb}`, which is nonzero iff
the pair `(ω_{va}, ω_{vb})` is not zero; this gives (iii). ∎

A `def₂`-**rigid subgraph** is `H ⊆ G` with `|V(H)| ≥ 2` and `def₂(H) = 0`. It is connected, and
by (MC-5)(i) it is also `def₃`-rigid. In a simple graph it has at least 3 vertices. Triangles
and `K_{2,3}` are examples. For an edge `e = uw` let `G_e` be `G` plus one new vertex `x` adjacent
to exactly `u` and `w`.

> **(MC-13)(a)** `[PROVED]` For `(q, q_x)` admissible for `G_e` with `q_x` off the line `q_u q_w`,
> `F(G_e) ≅ {P ∈ F(G, q) : P_u = P_w}`, with `P_x := P_u`.
> **(MC-13)(b)** `[PROVED]` `def₂(G_e) = def₂(G)` if `u` and `w` lie in a common `def₂`-rigid
> subgraph of `G`, and `def₂(G_e) = def₂(G) − 1` otherwise. The first case holds iff some
> `def₂`-maximizing partition of `V(G)` has `u` and `w` in one part.
> **(MC-13)(c)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at `G_e` and at a rigid subgraph)*
> At generic `q`, **the planes of `u` and `w` coincide on the whole fibre `L(q)`** (`ω_e ≡ 0` on
> `F(G, q)`) **iff `u` and `w` lie in a common `def₂`-rigid subgraph of `G`.** The "only if"
> direction uses Jackson–Jordán at `G_e` only, together with the elementary (MC-4)(b) at `G`. The
> "if" direction uses it at the rigid subgraph. Only the hard direction of Jackson–Jordán's
> Thm 7.1 (TR p.21) is used: generic `dim F ≤ 3 + def₂`, for simple graphs. Their theorem is over
> `ℝ` with genericity over `ℚ`, so (c) is claimed in **characteristic 0** (over any infinite field
> modulo (MC-33)(i); in characteristics 2, 3, 101 and 10 007 wherever `G_e` has ≤ 8 vertices, by
> (MC-33)(ii)).

*Proof.* (a) A flex of `G_e` has `P_x − P_u ∥ ℓ_{xu}` and `P_x − P_w ∥ ℓ_{xw}`, and `P_u − P_w = ω_e ℓ_e`.
So `ω_e ℓ_e + ω_{wx} ℓ_{wx} + ω_{xu} ℓ_{xu} = 0`, where the three `ℓ`'s are the sides of the
non-degenerate triangle `q_u q_w q_x`. That forces every `ω` to vanish, so `P_x = P_u = P_w`.
Conversely, any `P ∈ F(G)` with `P_u = P_w` extends by `P_x := P_u`. The closed neighbourhoods
`N[x] = {x, u, w}` and `N[u] ∪ {x}` are non-collinear.
(b) Write `val(P) := 3(|P| − 1) − 2d(P)`. Take a partition of `V(G_e)` and look at where `x` goes.
If `x` is alone, the value is `val_G(P) − 1`. If `x` sits in `u`'s part (or `w`'s), the value is
`val_G(P) − 2·[u, w separated by P]`. If `x` sits in any other part, it is `val_G(P) − 4`. Hence
`def₂(G_e) = max(max_{P : u ∼ w} val_G(P), def₂(G) − 1)`, which is the dichotomy.
Parts of maximizing partitions are rigid. Refining a part `X` by a partition `Q` of `X` changes
`val` by `3(|Q| − 1) − 2d_{G[X]}(Q) ≤ 0`, so `def₂(G[X]) = 0`. Conversely, let `H ∋ u, w` be
rigid and `P` maximizing. Merge the `t` parts that meet `V(H)`. This changes `val` by
`−3(t − 1) + 2·(edges of G between the merged parts)`, which is `≥ −3(t − 1) + 2d_H(P|_H) ≥ 0`. So
the merged partition is still maximizing, and `u ∼ w` in it.
(c) *Only if.* Suppose no rigid subgraph contains `u, w`. By (a), (b), Jackson–Jordán at `G_e`
(generic `(q, q_x)`, so generic `q` for `G`) and (MC-4)(b) at `G`:
`dim{P ∈ F(G, q) : P_u = P_w} = dim F(G_e) = 3 + def₂(G_e) = 2 + def₂(G) < 3 + def₂(G) ≤ dim F(G, q)`.
*If.* Suppose `u, w ∈ V(H)` with `H` rigid. Every `P ∈ F(G, q)` restricts to a flex of `H` at `q|_H`
(generic for `H`). By Jackson–Jordán at `H`, `dim F(H) = 3 + def₂(H) = 3`, so the restriction is
constant and `P_u = P_w`. ∎

> **(MC-14)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at the `G_e` and at rigid subgraphs)*
> *(settles (MC-10)(c) and adds its converse; characteristic 0)* Under (H), at generic `q`, **`X₀`'s generic point
> satisfies `IsNondegPencilRealization` iff every `|closedHubNbhd v| ≤ 3` and no `def₂`-rigid
> subgraph of `G` contains two members of a common `closedHubNbhd`.** The "if" direction uses
> Jackson–Jordán only at the graphs `G_e`, for `e` a hub–hub edge or an edge at a degree-2 vertex
> with two hub neighbours. On the A′ graphs this is exactly the `K_{2,3}` mechanism of (MC-9).

*Proof.* **If.** Fix a hub–hub edge `e`. It lies in no rigid subgraph, so `ω_e ≢ 0` on `F(q)` by
(MC-13)(c). Now take a degree-2 vertex `v` with hub neighbours `a, b`. Suppose both `ω_{va} ≡ 0` and
`ω_{vb} ≡ 0`. By (MC-13)(c) there are rigid `H₁ ∋ v, a` and `H₂ ∋ v, b`. Their union is rigid.
*Proof of the union lemma* (the second reader's):
- Let `P` partition `V₁ ∪ V₂` into `k` parts. Let `P₁ = P|_{V₁}`, with `t₁` parts.
- Let `P₂′` be `P|_{V₂}` with every part that meets `V₁` merged into one; it has `k − t₁ + 1`
  parts.
- An `H₂`-edge crossing `P₂′` has an endpoint outside `V₁`, so it is not an `H₁`-edge. Hence
  `d(P) ≥ d_{H₁}(P₁) + d_{H₂}(P₂′)`.
- So `val(P) ≤ val_{H₁}(P₁) + val_{H₂}(P₂′) ≤ 0`. One shared vertex suffices.
So the union contains `a` and `b`, which is excluded.
(The edge form checked by the driver is equivalent to the pair form stated. Use the union lemma,
and note that adding a degree-2 vertex to a rigid graph keeps it rigid.) Hence at least one of `ω_{va}`, `ω_{vb}` is not
identically zero. Only finitely many nonzero linear functionals on `F(q)` are involved, so
generic `z` avoids all their kernels, and (MC-12) gives conjunct 3.
**Only if.** If some `|closedHubNbhd v| ≥ 4`, (MC-12)(i) fails everywhere. Suppose instead that
`w₁, w₂ ∈ closedHubNbhd v` lie in a rigid `H`. Then `P_{w₁} = P_{w₂}` on all of `F(q)`, as in the
"if" half of (MC-13)(c). So their normals coincide, and conjunct 3 fails on all of `B`. (Linear dependence is a closed
condition holding on a dense subset of `B`.) ∎

**Checked** by `nondegx0.py` over every simple 2EC graph on ≤ 8 vertices (7 980 graphs, 121 208
edge checks), the battery and `θ(a, b, c)` with `a + b + c ≤ 10`. It uses one scale-30 admissible
`q` per graph. The (MC-13) equivalence is asserted edge by edge wherever that `q` and a drawn
`q_x` exhibit Jackson–Jordán's equality at `G` and at `G_e`; 12 edge checks at 1 graph were skipped
for that reason. The (MC-12)/(MC-14) prediction is asserted against `flanks.nondeg_conjuncts`, with
up to 4 drawn `z` per graph. On `exh8` the prediction and the observation agree at all 7 980
graphs: **7 934 predicted = 7 934 observed conjunct-3-degenerate on `X₀`**, which is the census's
own count in (MC-7)'s `exh8` row. Of these, 7 701 fail `hcard` and 233 pass `hcard` but have a rigid
hub pair (the census's 28 feasible A′ graphs are among the 233). Runs: `exh8` about 170 s;
`python3 notes/scripts/w4/nondegx0.py --battery --thetas 10 --exh 6 --list` about 1 s.

#### Step MC9 — kernel (K)'s habitat has no `def₂`-rigid subgraph

> **(MC-15)(i)** `[PROVED]` Let `G` be simple and 2-edge-connected, with `|V| ≥ 4`, a vertex of
> degree 2, and **no proper rigid subgraph**: no `H ≤ G` with `2 ≤ |V(H)|`, `V(H) ⊊ V(G)` and
> `deficiency H 3 = 0` (Lean `IsProperRigidSubgraph`, `n = 3`). Then **no subgraph of `G` on at least
> two vertices is `def₂`-rigid, `G` itself included.**
> **(ii)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at the `G_e`)* Hence, on `hK`'s habitat
> (`Escape.lean`'s `hK` assumes `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid
> subgraph, and a degree-2 vertex), wherever every `|closedHubNbhd v| ≤ 3`, `X₀`'s generic point
> is **nondegenerate** (MC-14). On that habitat **(MC-10)(a) alone would give `hK`'s conclusion
> `HasGenericPencilRealization K 3 G` outright, without its split-off antecedent or its induction
> hypothesis**, over the fields where (MC-10)(a) and Jackson–Jordán hold.

*Proof of (i).* A `def₂`-rigid subgraph `H` with `V(H) ⊊ V(G)` is connected and `def₃`-rigid by
(MC-5)(i), so it is excluded. A subgraph spanning all of `V(G)` is **not** excluded by
`IsProperRigidSubgraph`, but it has `def₂(H) ≥ def₂(G)`, having fewer edges. So it suffices to
show `def₂(G) > 0`. Suppose `def₂(G) = 0`. For `X ⊊ V` let `c(X)` be
the number of edges leaving `X`.
- *Step 1.* `def₂(G[X]) ≤ 2c(X) − 3`. Add the single part `V ∖ X` to a partition of `X`.
- *Step 2.* If `def₂(H) ≤ 1`, then `H` is connected, and `def₃(H) = 0` iff `H` is bridgeless. From
  `2d(P) ≥ 3|P| − 4`: `6(|P| − 1) − 5d(P) ≤ (8 − 3|P|)/2 < 0` for `|P| ≥ 3`, and `|P| = 2` needs
  `d ≥ 2`.
- *Step 3.* Let `c(X) = 2` and `|X| ≥ 2`. Then `G[X]` has a bridge, else it would be a proper rigid
  subgraph. The bridge splits `X` into `X₁`, `X₂`. Since `G` is 2EC and
  `c(X₁) + c(X₂) = 2 + c(X) = 4`, both have `c(X_i) = 2`.
- *Step 4.* By induction on `|X|`, every vertex of such an `X` has degree 2 in `G`.
- *Step 5.* Apply this to `X = V ∖ {v}`, `v` of degree 2: `c(X) = 2`. So `G` is a cycle, and
  `def₂(C_n) = n − 3 = 0` forces `n = 3`, against `|V| ≥ 4`. ∎

(ii) is (i) with (MC-14): no rigid subgraph exists at all.

**Where this leaves the A′ exposure.** Under Jackson–Jordán it is now exactly the graphs with a
`def₂`-rigid subgraph containing two hubs of a common `closedHubNbhd` (MC-14). By (MC-15) that
set is disjoint from `hK`'s habitat; the census's "no A′ graph in `hK`'s habitat" is now a theorem
(mod Jackson–Jordán). **Residuals** (packaging (b)'s (K-res) habitat) have proper rigid subgraphs,
so (MC-15) does not reach them. For each residual, (MC-14) turns "nondegenerate on `X₀`" into a
finite check of `def₂`-rigid subgraphs; the census found all 260 nondegenerate.

#### Step MC10 — the ear step on `X₀` (P3 Track 1)

*Worked by a forked agent (2026-09-24) and checked by the coordinator; driver `w4/earstep.py`
(new). The question: does the `X₀` motive, "`X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)`",
propagate along an ear addition `G = G′ + ear_k`? Here `G′` satisfies (H). The ear has `k ≥ 1` new
vertices on a path `a − x₁ − ⋯ − x_k − b`. It is **open** if `a ≠ b`; **closed** if `a = b`, and then
`k ≥ 2`.*

**Notation.**
- `M_H`: the motion space of `H`'s body-hinge framework at the configuration in hand.
- `f := def₃(G′)` and `g := def₃(G′/ab)`, the maximum over partitions with `a, b` in one part.
- `δ := f − g ∈ [0, 6]`: smark's `δ_i`, smark brief §1.
- `ρ := {X_b − X_a : X ∈ M_{G′}}`, with `r := dim ρ`.
- `Λ`: the span of the ear's `k + 1` hinge lines, with `λ := dim Λ`.
- `U := {P_a − P_b : P ∈ F(G′, q′)}`: the 2D relative motion of `a, b` in the vertical block.
- The flag pair `(p_a, π_a; p_b, π_b)` with `p_a ≠ p_b` lies in one of four projective orbits:
  **(i)** `p_a ∉ π_b` and `p_b ∉ π_a`; **(ii)** exactly one of these incidences holds;
  **(iii)** both hold and `π_a ≠ π_b`, so `π_a ∩ π_b = p_a p_b`; **(iv)** `π_a = π_b`.

> **(MC-16)** `[PROVED]` *(the dimension formula, at every configuration)* For an open ear,
> `dim M_G = dim M_{G′} − r + dim(ρ ∩ Λ) + (k + 1) − λ`. For a closed ear,
> `dim M_G = dim M_{G′} + (k + 1) − λ`. Moreover `r ≤ δ` wherever `G′` attains.

*Proof.* Solving along the chain gives `X_{x_{i+1}} = X_{x_i} − ω_i C_i`, so the ear closes iff
`X_b − X_a ∈ Λ`. Given that, the ear's `ω` form an affine space of dimension `(k + 1) − λ`, and they
determine the ear bodies. The admissible `X` are the preimage of `ρ ∩ Λ` under the surjection
`M_{G′} → ρ`. For a closed ear, `X_b − X_a = 0`. For the bound, `r = dim M_{G′} − dim M_{G′,weld}`,
where `M_{G′,weld} = {X ∈ M_{G′} : X_a = X_b}` is the motion space of the framework on `G′/ab` with
the same hinge lines. Its dimension is at least `6 + g` by the partition bound. ∎

> **(MC-17)** `[PROVED]` *(the target)* `def₃(G) = f + k − 5` for an open ear with `k ≥ 5`;
> `f − min(δ, 5 − k)` for an open ear with `k ≤ 4`; and `f + max(0, k − 5)` for a closed ear.

*Proof.* Restrict a partition of `V(G)` to `V(G′)`. Suppose the ear path has `c` crossing edges.
Its middle segments are best made new parts, so the ear contributes `6(c − 1) − 5c = c − 6`.
- If `a, b` are separated, then `c ≥ 1`, and the best is `c = k + 1`, contributing `k − 5`.
- If `a, b` share a part, then `c = 0` or `c ≥ 2`, and the best is `max(0, k − 5)`.
So `def₃(G) = max(f_sep + k − 5, g + max(0, k − 5))`, where `f_sep` is the maximum over separating
partitions and `f = max(f_sep, g)`. Then split into cases:
- For `k ≥ 5` this is `f + k − 5`.
- For `k ≤ 4` with `f_sep ≥ g`, it is `f − min(δ, 5 − k)`.
- For `k ≤ 4` with `f_sep < g`, `δ = 0` and it is `f`.
- For a closed ear only the "same part" case occurs. ∎

In Tay's generic model, `λ = min(k + 1, 6)`, `r = δ` and `dim ρ ∩ Λ = max(0, r + λ − 6)`. With
these, (MC-16) reproduces (MC-17).

> **(MC-18)** `[PROVED]` *(dominance, corrected at `k = 1`)* **(a)** For `k ≥ 2`, and for closed ears,
> `L_G(q) ≅ L_{G′}(q′) × K^{k−2}` by `z_{x₁} = h_a(q_{x₁})`, `z_{x_k} = h_b(q_{x_k})`, with the middle
> heights free. So restriction `X₀(G) → X₀(G′)` is dominant, and the fibre is exactly the set of
> **placements**: `p_{x₁} ∈ π_a`, `p_{x_k} ∈ π_b`, middle points free. **(b)** For `k = 1`,
> `L_G(q) ≅ {z′ ∈ L_{G′}(q′) : (h_a − h_b)(q_x) = 0}`, and restriction is dominant **iff
> `dim U ≠ 1`** at generic `q′`.

*Proof of (b).* The incidence `{(z′, q_x) : (h_a − h_b)(q_x) = 0}` is the zero set of a form that is
linear in `z′` and affine in `q_x`. Its rank as a bilinear form is `dim U`.
- `U = 0`: the condition is vacuous.
- `dim U ≥ 2`: the form does not factor. Its zero set is then irreducible, has generic `q_x`, and
  dominates `L_{G′}`.
- `dim U = 1`, say `U = K·φ₀`: the zero set has two components of equal dimension,
  `K² × {P_a = P_b}` and `{φ₀ = 0} × L_{G′}`. `X₀(G)`, which has generic `q_x`, is the first, and
  lies over the proper locus `{P_a = P_b}`. ∎

Two instances of `dim U = 1`:
- `φ₀ ∝ ℓ_{ab}`: an edge or implied edge `ab`, the triangle case.
- `C₄ = a c b d` with `a, b` opposite: `P_a − P_b ∈ N_c^⊥ ∩ N_d^⊥ = K ℓ_{cd}`, and `G = K_{2,3}`.
  This is (MC-9)'s mechanism.

`[MEASURED earstep.py --rdelta 7]` `dim U = 1` occurs at 241 of the 11 573 vertex pairs of simple
2EC graphs on `≤ 7` vertices: 114 adjacent, 127 not. Each is at one draw, a lower bound on `dim U`.

> **(MC-19)** `[PROVED]` *(chain spans; `earstep.py --chains`, 16/16 certificates)* **(a)** A generic
> closed polygon with `n` edges has hinge span `min(n, 6)`. **(b)** For any flag pair with
> `p_a ≠ p_b`, a generic open-ear placement with `k ≥ 2` has `λ = min(k + 1, 6)`. At `k = 1`,
> `λ = 2` in orbits (i), (ii), (iv), and `λ = 1` in (iii), where `p_x ∈ p_a p_b`. **(c)** For any
> flag, a generic closed-ear placement with `k ≥ 2` has `λ = min(k + 1, 6)`.

*Proof.* The placement space is irreducible (a product of planes and copies of `P³`), and rank is
lower semicontinuous on it. So one exhibited placement per projective orbit proves the generic
value.
- (b) with `π_a ≠ π_b`: choose `x₁ ∈ π_a` and `x_k ∈ π_b` with `p_a, x₁, x_k, p_b` not coplanar, and
  send them to `e₂, e₀, e₁, e₃`. The span then depends only on the free middle points, and one
  random choice has full rank.
- (b) with `π_a = π_b`: `p_a, x₁, x_k, p_b` are four general points of the common plane.
- (c): `p_a, x₁, x_k` are three general points of `π_a`.
- `n ≥ 7` and `k ≥ 6`: put the extra points on an existing hinge line of a spanning `n = 6` or
  `k = 5` configuration. The line set, and so the span, is unchanged, at a point of the closure. ∎

> **(MC-20)** `[PROVED]` *(the unconditional ear steps)* If `X₀(G′)` attains, then `X₀(G)` attains
> when the ear is **closed**, or **open with `k ≥ 5`**.

*Proof.* By (MC-18)(a), `X₀(G)`'s generic point lies over `X₀(G′)`'s, with a generic placement.
- Closed: by (MC-16) and (MC-19)(c), `dim M_G = 6 + f + (k + 1) − min(k + 1, 6)`, which is the
  target (MC-17).
- Open with `k ≥ 5`: `Λ = K⁶` by (MC-19)(b), so `ρ ∩ Λ = ρ` and `dim M_G = 6 + f + k − 5`.
Neither case uses `r`, `δ` or a placement condition. ∎

> **(MC-21)** `[PROVED]` *(class theorems; the first infinite families attaining on `X₀`)* **(a)**
> Every graph obtained from a cycle by successively adding closed ears and open ears with at least 5
> interior vertices attains on `X₀`. **(b)** **Every simple θ-graph `θ(p₁, p₂, p₃)` attains on
> `X₀`.**

*Proof.* `X₀(C_n)` has no hubs, so `L = K^V`, and by (MC-19)(a)
`dim M = 6 + n − min(n, 6) = 6 + def₃(C_n)`. Then (a) follows by induction with (MC-20). For (b):
if `p₃ ≥ 6`, the θ-graph is `C_{p₁+p₂}` plus an open ear with `p₃ − 1 ≥ 5` interior vertices. If
`p₃ ≤ 5`, it is one of 30 graphs, each with an exhibited attaining `X₀` point
(`earstep.py --thetas 5`, mod-`2⁶¹ − 1` rank equal to the target). ∎

This extends (MC-7)'s finite `a + b + c ≤ 16` to every θ-graph. It is **characteristic-free
wherever (MC-19)'s certificates are**: they are exact over ℚ, so every prime not dividing their
minors is covered, and the remaining primes are not checked. Nondegeneracy is not claimed:
`θ(2,2,2) = K_{2,3}` stays A′ (MC-9), (MC-14).

> **(MC-22)** `[PROVED]` *(the reduction for open ears with `k ≤ 4`)* Let `X₀(G′)` attain *(added by
> the 2026-09-24 second reading: the proof uses it)*. Assume dominance (MC-18) and
> `λ = k + 1`; the latter excludes orbit (iii) at `k = 1`. Then `G` attains at `X₀(G)`'s generic
> point **iff** both of the following hold at `X₀(G′)`'s generic point:
> **(R_k)** `r ≥ min(δ, 5 − k)`;
> **(P_k)** the generic placement has `dim(ρ ∩ Λ) = max(0, r + k − 5)`.

*Proof.* By (MC-16) and (MC-17) we need `r − dim(ρ ∩ Λ) = min(δ, 5 − k)`. The left side is at most
`min(r, 5 − k)` and `r ≤ δ`, so equality forces (R_k). Given (R_k), equality holds iff
`dim(ρ ∩ Λ)` takes its least possible value, which is (P_k). ∎

*Second reading (2026-09-24).* "We need" uses `dim M_{G′} = 6 + f`, that is, `X₀(G′)` attains; hence
the added hypothesis. The `(R_k)` half of "⟹" holds without it: with `dim M_{G′} = 6 + f + e`,
`e ≥ 0`, attainment of `G` reads `r − dim(ρ ∩ Λ) = e + min(δ, 5 − k) ≤ min(r, 5 − k)`, so still
`r ≥ min(δ, 5 − k)`. That half is all (MC-24) extracts, and every other use is inside an ear step
where `X₀(G′)` attains, so nothing downstream moves. No step of the proof uses `a ≁ b`.

**`r = δ` is a separate statement from "`G′` attains".** By (MC-16), `r = δ` iff the welded
framework on `G′/ab` attains at the pencil point. That framework's merged body carries two points
and two planes, so it is not a pencil framework.

> **(MC-23)** `[CONJECTURED]` *(the relative-dof conjecture (R); `earstep.py --rdelta 7` finds it at
> every one of 11 573 pairs)* At `X₀(G′)`'s generic point, `r = δ` for every `G′` satisfying (H) and
> every pair `a, b`. This is (K-c)'s genericity question in `X₀` form. On `≤ 7` vertices, at a draw
> where `G′` attains, `r_draw ≤ r_generic ≤ δ`, so each observed equality **certifies** the generic
> value; that is a finite theorem on `≤ 7` vertices, 9 min 32 s. *(2026-09-24: under (MC-10)(a)
> at `G′` and at `G′ + ab`, (MC-44) proves it for `a ≁ b` and `δ ≤ 5`.)*

> **(MC-24)** `[PROVED]` *(the gadgets: (R₃), (R₄), and conditionally (R₂), come from a strong
> induction on `|V|`)* Suppose `X₀(G′ + E′)` attains, where `E′` is an open `a–b` ear with `k′`
> interior vertices and restriction is dominant. Then (MC-22) at `G′ + E′` gives
> `r ≥ min(δ, 5 − k′)` at `X₀(G′)`'s generic point.
> - `k′ = 2` is always dominant. It gives `r ≥ min(δ, 3)`, hence **(R₃) and (R₄)**, and `G′ + E′` has
>   fewer vertices than `G` whenever `k ≥ 3`.
> - `k′ = 1` gives **(R₂)**, but only where `dim U ≠ 1`.
> - **(R₁) is not reachable this way**: the only smaller gadget is a chord, and a chord is not
>   dominant.
>
> *(2026-09-24: the last two bullets are superseded for `a ≁ b` by (MC-44): the chord `G′ + ab`
> gives `(R₀)`, hence every `(R_k)`, by upper semicontinuity of the welded motion space, not by
> dominance; so `(R₁)` is reachable and `(R₂)` does not need `dim U ≠ 1`.)*

> **(MC-25)** `[PROVED]` *(`k = 4`: (P₄) holds for every `ρ`; `earstep.py --lamcap`)* The intersection
> of `Λ` over all placements is `0` in all four orbits at `k = 4`. Hence, **under strong induction on
> `|V|`, the `k = 4` open-ear step holds**: (P₄) from this, (R₄) from (MC-24).

*Proof.* Here `λ = 5`. For `r ≥ 1`, (P₄) says that `ρ ⊄ Λ` for some placement, and that fails only
if `ρ ⊆ ⋂ Λ`. The exhibited intersection over 12 placements per orbit frame is already `0`, and
intersecting over more placements only shrinks it. ∎

> **(MC-26)** `[PROVED]` *(degeneration links)* For a given `ρ`: (P₁) ⟹ (P₂) at `r ≥ 4`, and
> (P₂) ⟹ (P₃) at `r ≥ 3`. (P_k) holds at `r = 1` for every `k ≤ 4`, except in the two cells where
> `⋂Λ ≠ 0`: orbit (iii) at `k = 1`, and orbit (iv) at `k = 2`.

*Proof.* For the first implication, degenerate the 2-ear to `x₁ ∈ π_a ∩ π_b` with `x₂` on the line
`x₁ p_b ⊆ π_b`. Its line set is then a 1-ear's, so the limit of `Λ₂` contains `Λ₁` plus one
dimension. Upper semicontinuity gives `dim ρ ∩ Λ₂ ≤ max(0, r − 4) + 1`, which is the (P₂) value
iff `r ≥ 4`. The second implication is the same, with `x₂` on the line `p_a x₁`. At `r = 1`,
(P_k) means `ρ ⊄ ⋂Λ` (`--lamcap`). ∎

Orbit (iv) is harmless on `X₀`. It is `P_a = P_b` at the generic point, i.e. `U = 0`. By the
argument of (MC-13), applied to `G′ + ab + x` with `x` adjacent to `a` and `b`, and assuming
Jackson–Jordán, `a` and `b` then lie in a common `def₂`-rigid subgraph. That subgraph is also
`def₃`-rigid, so `δ = 0` and `r = 0`.

> **(MC-27)** `[OPEN]` *(the open ear steps, `k = 1, 2, 3`)* At `X₀(G′)`'s generic point, `ρ` avoids
> the placement bad set `B_k(r) = {ρ : dim(ρ ∩ Λ) > max(0, r + k − 5) at every placement}`.
> **The universal form is false.** `Λ` always contains the line `p_a x₁`, which lies in the pencil
> `Pen(p_a, π_a)`. So every `ρ ⊇ Pen(p_a, π_a)` is bad when `r ≤ 5 − k`, and likewise for
> `Pen(p_b, π_b)`. Whether such `ρ` occur on `X₀` is open. They do not occur on `≤ 8` vertices:
> `exh8` attains everywhere (MC-7), which by (MC-22) forces (R_k) and (P_k).
> *`k = 1` in orbit (i), an exact criterion* `[PROVED]`. Put `m := π_a ∩ π_b` and `n := p_a p_b`,
> which are skew. Then `Λ(x) = x ⊗ n̂` inside `W₄ := m̂ ⊗ n̂`, the lines meeting both `m` and `n`. Put
> `ρ₄ := ρ ∩ W₄`. The 2-planes of `m̂ ⊗ n̂` meeting every `x ⊗ n̂` are exactly the `m̂ ⊗ y₀`. So (P₁)
> fails iff either `r ≤ 4` and (`dim ρ₄ ≥ 3`, or `ρ ⊇ m̂ ⊗ y₀` for some `y₀ ∈ n`), or `r = 5` and
> `ρ ⊇ W₄`.
> **Stop rule fired** (W4-reopen): the remaining cells split by `k` × orbit × `r`.
> *(2026-09-24: answered in part by Step MC13, (MC-43)–(MC-50); the cells that remain are
> (MC-51).)*

**What an ear-only induction on `X₀` still lacks** *(as updated by Step MC13)*.
- The open-ear cells of (MC-51)(a)–(c) at `δ ≥ 1` (at `δ = 0` all three close, (MC-54)): `k = 2`
  with `dim U = 1`; `k = 2` in orbit (iv), modulo Jackson–Jordán; `k = 1` with `1 ≤ δ ≤ 4`. Step
  MC14 counts what the steps reach on tested graphs — every one — but there is no coverage
  theorem (MC-61).
- Graphs of minimum degree `≥ 3` have no removable ear with an interior vertex, so they need a
  chord or contraction step, which the ear step does not supply. The contraction step is Step MC12, conditional on (MC-39)'s
  (i) and (ii).

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`, exact ℚ except the `--thetas` rank mod
`2⁶¹ − 1`, which is still a certificate; sampler support is in the docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/earstep.py --chains` | 16/16 | 0.2 s |
| `python3 notes/scripts/w4/earstep.py --thetas 5` | 30/30 | 0.6 s |
| `python3 notes/scripts/w4/earstep.py --lamcap` | span and intersection per orbit and `k` | < 1 s |
| `python3 notes/scripts/w4/earstep.py --rdelta 6` | 1 031 pairs | 31 s |
| `python3 notes/scripts/w4/earstep.py --rdelta 7` | 11 573 pairs | 9 min 32 s |

#### Step MC11 — the split-off step on `X₀` (Jackson–Jordán's Claim 6.5 Case 1, transferred)

*From the 2026-09-24 feasibility recon of W4-reopen's second unranked direction (transferring
Jackson–Jordán's proof technique). A second agent re-derived every `PROVED` step here and extended
the membership claim to both `def₂` cases. Driver `w4/splitext.py` (new). The question:
Jackson–Jordán's Case 1 (TR p.16) splits off a degree-2 vertex, realizes the smaller graph by
induction, and puts the new pin at a 1-extension position. Does that step transfer to `X₀`?*

**Notation.** `G` satisfies (H), and `x` is a vertex of degree 2 whose neighbours `a`, `b` are **not**
adjacent.
- `G′ := G − x`. This is Step MC10's `G′` for the open ear `a − x − b` with `k = 1`.
- `G″ := G′ + ab = G.splitOff x a b` (`kbare_common.split_off`). It satisfies (H) and has `|V| − 1`
  vertices.
- `δ := def₃(G′) − def₃(G′/ab)` is Step MC10's `δ`, and `δ₂ := def₂(G′) − def₂(G′/ab)`.
- For `q′ : V ∖ {x} → K²`, `U := {P_a − P_b : P ∈ F(G′, q′)}` is Step MC10's `U`.
- `ℓ_ab := p̂_a × p̂_b`, and `c := dim(U + Kℓ_ab) − 1`.
- The **special point** over `(q′, z″) ∈ B(G″)` and `s ∈ K ∖ {0, 1}` sets
  `p_x := (1 − s) p_a + s p_b`, that is, `q_x0 := (1 − s) q_a + s q_b` and
  `z_x := (1 − s) z_a + s z_b`. The hinges `xa`, `xb` and the deleted `ab` are then one line.

> **(MC-28)** `[PROVED]` *(rank exactly `+5`; field-free)* Let `(q′, z″)` be any configuration of
> `G″` with all hinges nonzero, and let `s ∉ {0, 1}`. The special configuration is a pencil
> configuration of `G`. It is not admissible, since `q(N[x])` is collinear. And
> `rank R_G(special) = rank R_{G″}(q′, z″) + 5`.

*Proof.*
- *Pencil.* `N[x] = {x, a, b}` is collinear, hence coplanar. `N_G[a] = N_{G″}[a] − b + x` lies in
  `π_a`, because `p_x ∈ p_a p_b ⊆ π_a`. The same holds at `b`. No other closed neighbourhood changes.
- *Hinges.* `p_x ≠ p_a, p_b`, because `s ∉ {0, 1}` and `p_a ≠ p_b`. So `C_{xa}` and `C_{xb}` are
  nonzero multiples of `C_{ab}`.
- *Motions.* A motion `X` of `G` has `X_x − X_a, X_x − X_b ∈ K C_{ab}`, together with `G′`'s
  conditions. So `X|_{V∖x}` is a motion of `G″`, and `X_x = X_a + t C_{ab}` with `t` free. Hence
  `dim M_G = dim M_{G″} + 1`, and `rank R_G = 6|V| − dim M_G = rank R_{G″} + 5`.

No step divides or uses an order. ∎

In Step MC10's terms (when `G′` satisfies (H)): at a point of `X₀(G″)` the flag pair of `a`, `b` is
in orbit (iii), or in orbit (iv) when `U = 0`. The special point is the `k = 1` placement on
`p_a p_b`. There `λ = 1` and `Λ = K C_{ab}` ((MC-19)(b)), and (MC-22)'s hypothesis `λ = k + 1`
excludes this placement. The split-off step uses exactly this placement.

> **(MC-29)** `[PROVED]` *(the counts)* **(a)** `def₃(G) − def₃(G″) = [δ ≥ 5]`, and
> `def₂(G) − def₂(G″) = [δ₂ ≥ 2]`. Both lie in `{0, 1}`. **(b)** Hence
> `target(G) − (target(G″) + 5) = 1 − [δ ≥ 5]`.

*Proof.* This is (MC-17)'s count. Restrict a partition to `V(G′)`. Let `f = def₃(G′)` and
`g = def₃(G′/ab)`, and let `f_sep` be the maximum over partitions separating `a` from `b`.
- The chord `ab` contributes `−5` when `a`, `b` are separated, and `0` otherwise.
- The path `a − x − b` contributes `−4` when `a`, `b` are separated (`x` alone: `6 − 2·5`). Otherwise
  it contributes `0` (`x` joins the part of `a` and `b`).

So `def₃(G″) = max(f_sep − 5, g)` and `def₃(G) = max(f_sep − 4, g)`.
- If `δ > 0`, then `f_sep = f`, and these are `f − min(δ, 5)` and `f − min(δ, 4)`.
- If `δ = 0`, both equal `f`.

For `def₂`, replace `6` and `5` by `3` and `2`. The chord then contributes `−2` and the path `−1`,
giving `f₂ − min(δ₂, 2)` and `f₂ − min(δ₂, 1)`. For (b):
`target(G) − target(G″) = 6 − def₃(G) + def₃(G″)`. ∎

So `def₃` rises by one exactly when `δ ≥ 5`. `def₂` rises exactly when `δ₂ ≥ 2`.

> **(MC-30)** `[PROVED]` *(the special point lies on `X₀(G)`)* Let `q′` be admissible for `G″` with
> `dim L_{G″}(q′) = 3 + def₂(G″)`.
> **(i)** `U ≠ Kℓ_ab`.
> **(ii)** Suppose some admissible `(q′, q_x1)` has `dim L_G(q′, q_x1) = 3 + def₂(G)`, and that
> `U = 0` or `U ⊄ p̂_{x0}^⊥`. Then for every `z″ ∈ L_{G″}(q′)` the special point over `(q′, z″, s)`
> lies on `X₀(G)`.
> **(iii)** If `def₂` rises, then `c = 2`. If `def₂` does not rise and (ii)'s `q_x1` exists, then
> `c = [U ≠ 0]`. So at a certified point, `c = 2` iff `def₂` rises. In flex form this is the
> flag-genericity condition `dim F(G′) − dim F(G″) = 2`.
> **(iv)** Suppose `ℓ₀(G″) = 3 + def₂(G″)`. Then at the generic point of `X₀(G″)`, and for every
> `s ∉ {0, 1}` except at most one, the special point lies on `X₀(G)`. No hypothesis at `G` is
> needed.

*Proof.* Two formulas come first. They hold for `q′` edge-injective on `G″` and `q_x` off the line
`q_a q_b`. Both follow from (MC-13)(a)'s computation, since `Kℓ_{xa} = p̂_x^⊥ ∩ p̂_a^⊥`.
1. `F(G, (q′, q_x)) ≅ ker φ_{q_x} ⊆ F(G′, q′)`, where `φ_{q_x}(P) := (P_a − P_b) · p̂_x`.
   `P_x` is the affine function with values `P_a·p̂_a`, `P_b·p̂_b`, `P_a·p̂_x` at `q_a`, `q_b`, `q_x`.
2. `F(G″, q′) = {P ∈ F(G′, q′) : P_a − P_b ∈ Kℓ_ab}`, so `dim F(G′) − dim F(G″) = c`.

Together they give

  `dim F(G, (q′, q_x)) = dim F(G″, q′) + c − [U ⊄ p̂_x^⊥]`.    (★)

*(i).* Suppose `U = Kℓ_ab`. Then `c = 0` and `U ≠ 0`. At an admissible `q_x` off the line
`q_a q_b`, (★) gives `dim F(G) = 2 + def₂(G″) < 3 + def₂(G)`, using (MC-29)(a). That contradicts
(MC-4)(b) at `G`.

*(ii).*
- *The curve.* Take `η ∈ K²` not parallel to `q_b − q_a`, and set `q_x(t) := q_x0 + tη`. Write
  `φ₀ := φ_{q_x0}` and `ψ(P) := (P_a − P_b) · (η, 0)`, so that `φ_{q_x(t)} = φ₀ + tψ`. For all but
  finitely many `t`, `(q′, q_x(t))` is admissible. `N_G[a] = N_{G″}[a] − b + x` can be collinear only
  when `N_{G″}[a] − b` lies on a line through `q_a` other than `q_a q_b`, and the curve meets that
  line at most once. The same holds at `b`. At such `t`, `[U ⊄ p̂_{x(t)}^⊥] = [U ≠ 0]`, because
  `φ₀ ≠ 0` when `U ≠ 0`.
- *It lies in `U(G)`.* By (★), `dim L_G(q′, q_x(t)) ≤ dim L_G(q′, q_x1) = 3 + def₂(G)`. (MC-4)(b)
  gives equality, so `(q′, q_x(t)) ∈ U(G)`.
- *The flexes.* Let `P₀ := Ψz″ ∈ F(G″, q′) ⊆ ker φ₀`. If `U = 0`, put `P(t) := P₀`. Otherwise pick
  `W₀` with `φ₀(W₀) ≠ 0`, and put `P(t) := P₀ − [tψ(P₀)/(φ₀(W₀) + tψ(W₀))] W₀`. Then
  `φ_{q_x(t)}(P(t)) = 0` and `P(t) → P₀`.
- *The limit.* `z(t) := Φ(P(t)) ∈ L_G(q′, q_x(t))`, by formula 1 and Step MC4. At `t = 0`,
  `z_w = P₀_w · p̂_w = z″_w` on `V ∖ x`. And `z_x = P₀_a · p̂_{x0} = (1 − s) z″_a + s z″_b`, because
  `P₀_a − P₀_b ∈ Kℓ_ab ⊥ p̂_b`. So the special point is a limit of points of `B(G)`.

*(iii).* If `def₂` rises, apply (MC-4)(b) at `G` and (★) at a generic `q_x`:
`1 ≤ c − [U ≠ 0]`. This forces `U ≠ 0` and `c = 2`, since `U + Kℓ_ab ⊆ K³`. If `def₂` does not
rise, (★) at `q_x1` gives `c = [U ⊄ p̂_{x1}^⊥] ≤ [U ≠ 0]`. Conversely, `c ≥ [U ≠ 0]` by (i).

*(iv).* At the generic point, `q′` is generic in `K^{2(|V|−1)}`, so
`dim L_{G″}(q′) = ℓ₀(G″) = 3 + def₂(G″)` and (i) applies. Because `U(G)` is dense and open, some
`q_x1` has `(q′, q_x1) ∈ U(G)`, with `dim L_G = ℓ₀(G)`. The proof of (ii) used only that
`dim L_G(q′, q_x1)` is the minimum `ℓ₀(G)`, so it applies unchanged. If `U ≠ 0`, then `U ⊄ Kℓ_ab`
by (i). So some `u ∈ U` does not vanish on the whole line `q_a q_b`, and `u(q_{x0})` is zero for at
most one `s`. ∎

> **(MC-31)** `[PROVED]` *(the step, within one)* If `X₀(G″)` attains and
> `ℓ₀(G″) = 3 + def₂(G″)`, then the generic rank on `X₀(G)` is at least
> `target(G) − 1 + [δ ≥ 5]`. In particular, **`X₀(G)` attains whenever `δ ≥ 5`**, with no condition
> on the flag orbit, on dominance, or on `r`.

*Proof.* Take the generic point of `X₀(G″)` and a generic `s`. By (MC-28) the special point has rank
`target(G″) + 5`, and by (MC-30)(iv) it lies on `X₀(G)`. Rank is lower semicontinuous on the
irreducible `X₀(G)` (MC-2). Then use (MC-29)(b). ∎

Where the hypothesis `ℓ₀(G″) = 3 + def₂(G″)` is available:
- in characteristic 0, by Jackson–Jordán;
- at every `G″` on at most 8 vertices in characteristic 0, by the census's `JJ` column with
  `--jjprobe` (*The census — results*);
- at the same graphs in characteristics 2, 3, 101 and 10 007, by (MC-33)(ii);
- over any infinite field, modulo (MC-33)(i).

It is used only to exclude `U = Kℓ_ab`.

> **(MC-32)** `[MEASURED]` *(`splitext.py`; the missing `+1` appears at first order)* Moving `x` off the
> line gives first-order gain `≥ 1` at every instance where one is needed. The curve is the exact
> curve of (MC-30)(ii)'s proof: `q′` fixed, `q_x(t) = q_{x0} + tη`, `P(t)` in `ker φ_{q_x(t)}`,
> `z(t) = Φ(P(t))`.
> - On `exh8` (every simple 2EC graph on ≤ 8 vertices, every eligible `x`): 4 736 of 4 736 needed
>   instances.
> - On θ-graphs: 62 of 62 (`a + b + c ≤ 10`), and 69 of 69 (`11 ≤ a + b + c ≤ 13`). Both θ
>   populations are capped at 3 eligible `x` per graph.
>
> The gain is the mod-`p` rank of `S₀ᵀA₁K₀` along the curve's 1-jet. At a certified instance,
> `rank_p A₀ = rank_ℚ A₀`, so the gain is a lower bound for the ℚ-rank along the curve. Each instance
> is therefore a certificate that `X₀(G)` attains at that `G`. The census certifies this on ≤ 8
> vertices anyway; what is new is the mechanism.
> *Control:* the curve that moves `x` along the line keeps every point special. Its gain is asserted
> to be `0`, and it is `0` at all 63 instances of `--control --exh 6`.
> **This is not a class statement.** No argument is known that the gain is positive in general.

**Measured cells** (`splitext.py --exh 8` histogram of `(dim U, c, δ)`, 4 751 certified
instances):
- `dim U = 0`: 3 247 instances, all with `δ = 0`. This is the orbit-(iv) remark after (MC-26).
- `dim U = 1`: 1 017 instances, `c = 1`, `δ ≤ 1`. Here the ear restriction is **not** dominant
  (MC-18)(b).
- `dim U = 2`: 374 instances, and `dim U = 3`: 113 instances, all with `c = 2`.

So `def₂` rises exactly at the 487 instances with `dim U ≥ 2`, as (MC-30)(iii) requires. `δ ≥ 5`
occurs at exactly 15 instances, the pairs `(C₇, x)` and `(C₈, x)`. On the θ populations it occurs at
33 instances.

**How this relates to Step MC10.**
- *(MC-18)(b), `k = 1`.* The ear route takes its induction hypothesis at `G′ = G − x`. It needs
  dominance (`dim U ≠ 1`), `λ = 2` (not orbit (iii)), (R₁) and (P₁). The split-off route takes its
  hypothesis at `G″ = G′ + ab` instead. That graph has the same number of vertices, and it is the
  chord gadget that (MC-24) sets aside for (R₁) because a chord is not dominant.
  - It needs no dominance. It sits exactly at the placement on `p_a p_b` that (MC-22) excludes (orbit
    (iii), or orbit (iv) when `U = 0`).
  - It covers the 1 017 non-dominant instances above, up to the one missing `+1`.
- *(MC-27)'s `k = 1` cell.* That cell stays open as stated, because (MC-27) is the ear route's
  placement lemma. The split-off step closes the `k = 1` step by another route when `δ ≥ 5` (MC-31).
  On ≤ 8 vertices, and on the θ populations, the `δ ≥ 5` instances are cycles and θ-graphs, which
  already attain by (MC-21). So (MC-31) proves nothing new on the tested graphs. Its content is the
  general statement.
- *The same statement, found independently.* The 2026-09-24 recon of W4-reopen's third unranked
  direction (the `X₀` hybrid) reached (MC-28) + (MC-31) as a "subdivision" step, without the
  `X₀`-membership half, which (MC-30) supplies. It found that the step fires ahead of the cycle base
  case at no graph on ≤ 8 vertices. That is consistent: the only `δ ≥ 5` instances there are `C₇` and
  `C₈`.
- *What is still missing.* For `δ ≤ 4`, the `+1` must come from leaving the special position. That
  is a first-order statement about moving `x` off `p_a p_b` together with the heights, on `X₀(G)`.
  The direction-2 recon judged that making it uniform meets `notes/pencil/strategy.md` §2.4's Schubert/`V_bc` wall,
  which gives per-shape answers only. That judgment was not re-checked here. (MC-32) finds the `+1` at
  every instance tested.

**What would change this:**
- an instance where `splitext.py` fails the `+5` assert (then (MC-28)'s motion count is wrong);
- a certified `q′` with `U = Kℓ_ab` (then (MC-4)(b) is wrong);
- a certified instance where `def₂` rises with `c ≠ 2`;
- a needed instance whose first-order gain stays `0` under many jets. That would not refute
  anything, but it would locate a shape where the `+1` is not first order.

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`; exact ℚ for the flex spaces, `U`, `φ₀` and
the curve; ranks mod `2⁶¹ − 1` only as certificates or lower bounds; sampler support is in the
docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/splitext.py --exh 7` | 417 instances (331 / 79 / 7 by `(Δdef₃, Δdef₂) = (0,0) / (0,1) / (1,1)`, printed `ddef3`/`ddef2`); all certified; gain `≥` needed 417/417 | 15 s |
| `python3 notes/scripts/w4/splitext.py --exh 8` | 4 751 (4 264 / 472 / 15); all certified; gain `≥` needed 4 751/4 751 | 220–265 s |
| `python3 notes/scripts/w4/splitext.py --thetas 10` | 65 (cap 3 per graph; 5 / 57 / 3); all certified | 2.7 s |
| `python3 notes/scripts/w4/splitext.py --thetas 13 --smin 11` | 99 (cap 3; 0 / 69 / 30); all certified | 8.3 s |
| `python3 notes/scripts/w4/splitext.py --thetas 13 --smin 11 --perg 1` | 33 (25 / 8): the recon's population | 2.6 s |
| `python3 notes/scripts/w4/splitext.py --control --exh 6` | 63; along-line control gain 0 at 63 | 2.3 s |

The recon's scratch-probe figures reproduce class for class: 417 (331 / 79 / 7), 65 (5 / 57 / 3)
and 33 (25 / 8), so 515 instances, 18 of which close outright. Its θ figures carried caps it did not
state, 3 and 1 eligible `x` per graph; `splitext.py` prints its caps.

#### Jackson–Jordán beyond ℝ — a second reading (2026-09-24)

*The question (`notes/Phase39-design.md`, field-hypothesis recon, row S5: "unverified beyond ℝ").*
Jackson–Jordán's pin-collinear theorem is used here only in (MC-4)(b)'s equality form. Does it hold
over every infinite field? Through Step MC4, `F(q)` is their rod-and-pin null space. The dictionary:
- JJ's pin-line `L_v : p₁x + p₂y = 1` is dual to `q_v`, with `p(v) = −q_v`;
- the pin `L_u ∩ L_v` is `ℓ_uv`, as a homogeneous point;
- the motion vectors change by `diag(1, −1, 1)`, because JJ's `P(e) = (x_e, −y_e, 1)` (TR p.10).

The dictionary is valid wherever no edge line passes through the origin, which holds generically. So
the (MC-4) form is exactly their Thm 7.1 (TR p.21). The TR was read twice: by the 2026-09-24
recon of W4-reopen's second unranked direction, and then by a second reader who re-derived each row
of the table below. Page numbers are as
printed.

> **(MC-33)** *(Jackson–Jordán's rank formula over an infinite field)*
> **(i)** `[INFORMAL]` *(gaps: a written field-general proof; the non-degeneracy of each constructed
> realization, bypass R2, was checked at sketch level only)* Thm 6.1 and Thm 7.1 (TR pp.14, 21)
> hold over every infinite field `K`, of any characteristic. "Generic" means "in a nonempty
> Zariski-open subset of `K^{2V}`" rather than "algebraically independent over ℚ". The proof needs
> two repairs (R0, R1) and one bypass (R2), listed below. Characteristics 2 and 3 are not special.
> **(ii)** `[MEASURED]` *(`jjchar.py`)* At every simple 2EC graph on ≤ 8 vertices (7 980 graphs), some
> admissible `q` over each of GF(2¹⁶), GF(3¹⁰), GF(101) and GF(10 007) has `dim L(q) = 3 + def₂`.
> Each such line is a finite theorem: for that graph, `ℓ₀ = 3 + def₂` over every infinite field of
> characteristic 2, 3, 101 or 10 007.

*Why each line of (ii) is a theorem.*
- The lower bound `dim L(q) ≥ 3 + def₂` holds over every field (MC-4)(b).
- The matrix `M(q)` of Step MC2 has entries that are polynomials over the prime field. So a nonzero
  minor at one point over `GF(pᵏ)` is a nonzero polynomial over `GF(p)`. It does not vanish at
  generic points of any infinite field of characteristic `p`, and neither does the admissibility
  polynomial.
- Step MC4's bijection `F(q) = L(q)` is field-free. It is asserted in rank form at every draw.

*The reading, step by step* (TR-2006-06; "Zariski" means: the Euclidean `ε`-move is replaced by "all
but finitely many values of a parameter on an irreducible line, pencil or plane containing the
original position", and each extra condition in the move was checked to exclude only finitely many
values):

| TR step (page) | what it uses | verdict |
|---|---|---|
| bar-joint rigidity matrix, Lemma 2.1 `r ≤ 2n − 3` (p.3) | the dot product; three trivial motions (two translations and `m_v = Jq_v`, `J` antisymmetric, so `d·Jd = 0` in every characteristic) | field-free |
| Lemma 2.2(a) (p.4) | specialization of the generic rank | field-free |
| Lemma 2.2(b) (p.4) | an `ε`-ball | Zariski form: `{q′ : r(G, q′) ≥ r(G, q)}` is open and contains `q` |
| Lemmas 2.3 (0-extension), 2.4 (1-extension, cited from Whiteley), 2.5 (vertex split) (pp.4–5) | linear algebra; 2.4 needs `Q ≠ q(v₁), q(v₂)`, and `s(s − 1) ≠ 0` works in every characteristic | field-free (2.4 re-derived) |
| Lemma 2.6 (p.5; stated, "proved similarly") | trivial motions of the two rigid parts must agree on `X` | field-free (proof supplied through Lemma 2.9) |
| Lemmas 2.7, 2.8, 2.9 (pp.5–6) | completing to `K_n` on a spanning point set, which is rigid by 0-extensions; `f_S` with `M_S` antisymmetric | field-free |
| §3, Lemma 4.1 (pp.6–9) | combinatorics; Lemma 2.1 on each part | field-free |
| degree-1 pin-line convention (p.9) | "the line through `q(p)` orthogonal to `q(v)q(p)`" | **R0 (cosmetic).** At an isotropic direction (`(1,1)` in characteristic 2; any field containing `√−1`) this line contains `q(v)`. Make the pin-line of a degree-1 body a free datum through its pin. `r(G*, q)` does not depend on it |
| Lemma 4.2 (p.9) | `ε`-moves of pins along their pin-lines; "a small rotation of `L(u)` about `q(uv)`" | **doubtful as written, over ℝ as well:** if `u` has two edges `uv`, `uv₁` with `L(u) = L(v) = L(v₁)` (a triangle with one common pin-line), the pin `uv₁` is forced onto `L′ ∩ L(u) = q(uv)`. **R2 (bypass):** carry "non-degenerate" in the induction. Every construction below has generic free choices (R1 supplies them at the gluing), so each constructed realization can be taken non-degenerate. Lemma 4.2 is then never needed |
| Lemma 5.1 (p.11) | Lemma 2.9 on each rigid body `B_v` | field-free |
| Lemma 5.2 (p.13) | generic rod-and-pin rank `≥` rank at a non-degenerate realization | Zariski form (semicontinuity on `K^{2V}`, which is irreducible); needed only for non-degenerate realizations under R2 |
| "pin-line-generic" realizations (p.13): no two pin-lines parallel, each pin on exactly two lines, restriction to a subgraph generic | finitely many nonzero polynomials | Zariski: finitely many nonempty open conditions, intersected |
| Claims 6.2–6.4 (pp.14–15) | disjoint union; 0-extensions; `Q = L(u₁) ∩ L(u₂)`; Lemma 2.7 with `t = 1` | field-free |
| Claim 6.5, same brick and Case 3 (pp.15–18) | 0-extensions only | field-free |
| Claim 6.5 Case 1 (p.16) | `r(G₂*) ≥ r(G₁*) + 3` gives three bars at `p₀` (needs `q(u₁), q(u₂), p₀` non-collinear; body points are free); `ε`-move of `p₀` along `L(u₁)`; 1-extension with `Q₂ = L′ ∩ L(u₂)`, `L′` the line `Q₁ q(u₂)` | Zariski on `L(u₁) ≅ K`: the rank condition is cofinite, and each of `Q₁ ∉ L(u₂)`, `L′ ∦ L(u₂)`, `Q₂ ≠` each pin of `u₂` excludes one point (central projection from `q(u₂)` is a bijection `L(u₁) → L(u₂)`) |
| **Claim 6.5 Case 2** (pp.16–17): the step the first reading flagged | two 1-extensions on `L(z)`; vertex split (Lemma 2.5); "small rotation of `L(z)` about `q₅(p₃)`" with `p_i = L′ ∩ L_i` (`4 ≤ i ≤ j`); `ε`-move of `q₅(u₂)`; a final 1-extension and a 0-extension | **field-free in Zariski form.** Parametrize `L′` by its slope in the pencil at `Q₃` (a `P¹`): `p_i := L′ ∩ L_i`, and `p₁` is any point of `L′` depending rationally on the slope (the TR's "`L_1`" is undefined, a slip: `p₁` needs only to lie on `L′`). The rank condition is cofinite, and pin distinctness, `L′ ≠ L(z)` and `q(u₁) ∉ L′` each exclude finitely many slopes. The move of `u₂` is Zariski on `K²`. The subframework `F` is rigid by a determinant (`z ∉ L(z)`), not a metric. No ordered-field use |
| Claims 6.6–6.9 (pp.18–19) | 0-extensions; in 6.8, the rotation of one side about the cut pin `p₂` is blocked by the bar `p₁v` iff `det(q(p₁) − q(v), q(v) − q(p₂)) ≠ 0`; a Zariski move of `q₁(v)` | field-free |
| Claim 6.10 (a), (b) (p.19) | combinatorics | field-free |
| **final gluing** (pp.19–20) | "translation, rotation, and dilation" matching `q₁(p₃) = q₂(p₆)`, `q₁(p₅) = q₂(p₇)` | **R1 (repair; the first reading's).** Use an invertible affine map. Bar-joint rank is invariant under it over any field, since `R(G, Aq + b) = R(G, q)·diag(Aᵀ)`. Two point conditions leave a 2-parameter family, which also makes the glued realization non-degenerate for R2. (Similarities cannot map an isotropic segment to a non-isotropic one over a field containing `√−1`, nor in characteristic 2.) Lemma 2.7 with `t = 2` and the rank counts via Lemma 2.3 are field-free |
| Thm 7.1 (p.21) | Thm 6.1 plus Lemmas 5.1, 5.2 | field-free; genericity in Zariski form |

What was re-derived and what was taken on trust:
- **Re-derived:** every row above, including the two lemmas the TR does not prove (2.4, cited from
  Whiteley; 2.6, "proved similarly"), and the Step MC4 dictionary.
- **Taken on trust:** the brick and superbrick lemmas (3.2, 3.3, from Jackson–Jordán's molecular
  paper [5]) and the claims' deficiency inequalities. These are combinatorial and field-free, but
  they were not re-proved.
- **Checked at sketch level only:** that each construction can be made non-degenerate (R2).

No step divides by an integer or uses an order.

**What would change this:**
- a step of the TR that needs a metric property beyond the bilinear dot product;
- a construction whose free choices cannot avoid a degenerate pair (R2);
- a graph and a characteristic where `jjchar.py` never exhibits the equality (an upper bound per
  draw, so this would prompt a search, not a refutation).

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/jjchar.py --selftest` | 5 non-fields rejected, 6 fields accepted; OK | 0.4 s |
| `python3 notes/scripts/w4/jjchar.py --exh 7` | 577/577 in each of the four fields | 2.7 s |
| `python3 notes/scripts/w4/jjchar.py --exh 8` | 7 980/7 980 in each of GF(2¹⁶), GF(3¹⁰), GF(101), GF(10 007) | 35–43 s |
| `python3 notes/scripts/w4/jjchar.py --battery --thetas 12` | 9/9 and 43/43 in each field | 0.5 s |

Arithmetic is exact in each named field. There these ranks are the object, not a proxy for ℚ, so
the harness's "GF(p) only as a bound for ℚ" rule does not apply. The GF(2¹⁶) and GF(3¹⁰)
constructors assert that `X` has order `q − 1`, which makes the polynomial primitive and so the
quotient a field. They also check the table arithmetic against slow polynomial arithmetic.

#### Step MC12 — the contraction step on `X₀` (W4-reopen P1, option 2)

*Worked 2026-09-24 by a forked agent, porting the device and scratch probes of the feasibility recon
of W4-reopen's first unranked direction (the multi-scale construction; its claims were
unreviewed). Every claim marked `PROVED` below was re-derived by that agent and checked by the
coordinator at sketch level. **A second reader (2026-09-24) re-derived (MC-34)–(MC-39) and (MC-59)**
against the driver's row structure and KT 2011 §6.2: nothing wrong, no gap left open; its fills and
sharpenings are recorded at the claims they touch. The driver is `w4/coreshrink.py` (new).
The question is Step MC10's last "still lacks" bullet, W4-reopen P1 (2026-09-24) option 2: does
`X₀(G)` relate to `X₀(G/H)` at all? **Yes, for a proper rigid `H` whose contraction `G/H` is
simple.** Katoh–Tanigawa's contraction case (KT 2011 §6.2, Lemma 6.3) has an `X₀` form. The
contraction step reduces to two linear-algebra conditions, (i) and (ii), which are checked per
graph at one exact picture.*

**Notation.**
- **Proper rigid set.** `W ⊊ V` with `|W| ≥ 2` and `def₃(G[W]) = 0`. Put `H := G[W]`, the
  induced subgraph. A rigid `H` has minimum degree `≥ 2`: the partition `{{v}, W ∖ v}` has value
  `6 − 5 deg_H v`. So `|W| ≥ 3`, and `H` satisfies (H).
- **Outside, contraction.** `O := V ∖ W` is the outside. `G/H` contracts `W` to one vertex `v*`
  and keeps parallel edges. It is **simple** iff no outside vertex has two neighbours in `W`.
- **Attachments.** When `G/H` is simple, each **attachment** `u` (an outside vertex adjacent to
  `W`) has exactly one core neighbour `c(u)`. `A_c` is the set of attachments of `c`, and `c` is
  **pinned** if `|A_c| ≥ 2`.
- **Ranks.** For a multigraph `Γ` with a nonzero line `L_e` on every edge,
  `M_Γ(L) := {X : V(Γ) → K⁶ : X_u − X_w ∈ K L_e}` and `rank R_Γ(L) = 6|V(Γ)| − dim M_Γ(L)`.
  `L_p` is the line set `p_u ∧ p_w` of a configuration `p`.
- **Targets.** `tgt(Γ) := 6(|V(Γ)| − 1) − def₃(Γ)`. It bounds `rank R_Γ(L)` for every `L`.
- **The collapse point.** `P` is a point, put at the origin of the chart; `Q = (0, 0)` is its
  picture. `q' := (q|_O, Q)` is a picture of `G/H` with `v*` at `Q`.
  `L⁰_{G/H}(q') := {z ∈ L_{G/H}(q') : z_{v*} = 0}`.
- **Two-scale family.** A curve `p(t)` of pencil configurations of `G` with `p_c(t) → P` for
  every `c ∈ W` and `p_u(t) → p_u(0)` for every `u ∈ O`: the core "at scale `t` around `P`".

> **(MC-34)** `[PROVED]` *(the block identity: the kernel form of KT 2011 eq. (6.3), p. 673)* Let
> `p` be any configuration of `G` with adjacent points distinct. If `(H, p|_W)` is infinitesimally
> rigid, then **exactly**
> `rank R_G(L_p) = 6(|W| − 1) + rank R_{G/H}(L_p)`.
> Here `G/H` carries the **actual** lines of `p`: a boundary edge `uc` keeps `p_u ∧ p_c`. No
> genericity is assumed, and the identity holds over any field.

*Proof.* Restrict a motion `X` of `G` to `W`. It is a motion of `H`, and `H` is infinitesimally
rigid, so it is constant: `X|_W ≡ X*`. Put `X_{v*} := X*`. This is a motion of `G/H` with the same
lines, because the conditions at edges of `H` hold trivially and the others are unchanged.
Conversely, a motion of `G/H` extends by `X|_W :≡ X_{v*}`. So `dim M_G = dim M_{G/H}`, and
`6|V| − dim M_G = 6(|W| − 1) + (6(|V| − |W| + 1) − dim M_{G/H})`. ∎

KT's (6.3) is the block-triangular shape of `R(G, p)`: the rows of `E′` are supported on `V′`.
With their Lemma 5.1 (p. 667) it gives `≥`; the kernel view gives equality. The driver asserts
(MC-34) at every sampled point where the core is rigid.

> **(MC-35)** `[PROVED]` *(the targets add; KT 2011 Lemma 3.5, p. 658, is the minimal-k-dof form)*
> If `H` is rigid, then `def₃(G) = def₃(G/H)`, so `tgt(G) = 6(|W| − 1) + tgt(G/H)`.

*Proof.* Write `val(𝒫) := 6(|𝒫| − 1) − 5 d(𝒫)`. Take a maximizing partition `𝒫` of `V` and
merge the `t` parts that meet `W`. The value changes by
`−6(t − 1) + 5·(edges between the merged parts)`. This is
`≥ −6(t − 1) + 5 d_H(𝒫|_W) = −val_H(𝒫|_W) ≥ −def₃(H) = 0`. So some maximizing partition has `W`
inside one part. Such partitions of `V` are exactly the partitions of `V(G/H)`, with the same
crossing edges. Finally, `|V(G/H)| = |V| − |W| + 1`. ∎

> **(MC-36)** `[PROVED]` *(the limit)* Let `p(t)` be a two-scale family, regular in `t` at `0`, with
> `p_u(0) ≠ P` at every attachment and `p_u(0) ≠ p_w(0)` on outside edges.
> - The lines `L(t)` of `G/H` converge to `L(0)`, with `L(0)(uc) = p_u(0) ∧ P`: in the limit every
>   hinge at `v*` passes through `P`.
> - For all but finitely many `t`, `rank R_{G/H}(L(t)) ≥ rank R_{G/H}(L(0))`.
> - `L(0)` is the line set of the configuration of `G/H` with `v*` at `P` and `u` at `p_u(0)`.
>   If `G/H` is simple, this configuration is pencil at every `u ≠ v*`. At `v*` it need not be:
>   `v*` is realized "as a d-dimensional body" (KT p. 675).

*Proof.* The augmented matrix of (MC-3) is polynomial in the points, so its entries are regular at
`t = 0`. A minor that is nonzero at `t = 0` is nonzero at all but finitely many `t`. By (MC-3),
`rank A = |E| + rank R` whenever every line is nonzero, and the distinctness hypotheses give that
at `t = 0`. For the pencil claim: coplanarity of `N_{G/H}[u]` is a closed condition. It holds at
every `t ≠ 0`, because `N_G[u]` is coplanar and, when `G/H` is simple, it meets `W` at most in
`c(u)`, whose point tends to `P`. ∎

Simplicity is what makes the limit usable. An outside `u` with two core neighbours would give two
boundary hinges converging to the same line `p_u(0) ∧ P`. This is the (α)/parallel-class
obstruction, and KT Lemma 6.3's hypothesis "`G/E′` simple".

**The construction** (`coreshrink.py --pool`). It is a linear system, not a hand construction.
1. Fix `q_u` for `u ∈ O` and `δ_c` for `c ∈ W`, and put `q_c(t) := t δ_c`.
2. Write the core heights as `z_c = t ζ_c`. For every `v ∈ N[W]`, write the constant term of `π_v`
   as `γ_v = t γ̃_v`.
3. For `t ≠ 0`, the pencil conditions `z_w = α_v x_w + β_v y_w + γ_v` (`w ∈ N[v]`) become a
   homogeneous system `M(t) = M₀ + t M₁` in `(z_O, ζ, α, β, γ̃)`, and `ker M(t) ≅ L(q(t))`. The
   only `t` in it is the `γ̃_v` of the rows `(v ∈ N[W], w ∈ O)`.
4. Let `W₀ := lim_{t→0} ker M(t)`. It is a subspace of `ker M₀` of dimension `dim L(q(t))`, and
   the driver computes it exactly, from jets. **No jump** means `ker M₀ = W₀`.
5. A family is the unique `x(t) ∈ ker M(t)` with `R x = b`, for fixed generic `R` and `b`. It is
   regular at `0`, with `x(0) ∈ W₀`. Then `p(t) := ((q_u, z_u(t))_{u ∈ O}, (tδ_c, tζ_c(t))_{c ∈ W})`
   is a two-scale family.

At `t = 0` the rows say three things:
- the outside planes are those of a configuration of `G/H` with `v*` at `P`, pencil except at `v*`;
- `π_c(0)` passes through `P` and contains `A_c`;
- the rescaled core `d_c := (δ_c, ζ_c(0))` has, at each `c`, a plane through `N_H[c]` with the
  slope of `π_c(0)`.

> **(MC-37)** `[PROVED]` *(the `X₀` form of KT's Claim 6.4, p. 675)* Let `G/H` be simple, and assume
> **(ii)** *no jump:* `dim ker M₀ = dim L(q(t))` at one picture where `q(t) ∈ U` is certified.
> Then, at `X₀(G)`'s generic point `p`, `rank R_{G/H}(L_p)` is at least the generic rank of
> `X₀(G/H)`. That rank is `tgt(G/H)` if `X₀(G/H)` attains.

*Proof.*
1. *(ii) is generic.* `dim ker M₀` is upper semicontinuous in the picture, and it is never below
   `dim W₀ = ℓ₀(G)`. So equality at one certified picture gives equality at a generic one.
2. *Containment: `L⁰_{G/H}(q') ⊆ proj_z ker M₀`.* Take `z⁰ ∈ L⁰_{G/H}(q')`. Its plane at `v*` is
   `π* : z = a*·(x, y)`, through `P` since `z⁰_{v*} = 0`. Extend `z⁰` by a flat core:
   - `ζ := a*·δ`;
   - every core plane of slope `a*`, with `γ̃_c = 0`;
   - `γ̃_u := ζ_{c(u)} − a_u·δ_{c(u)}` at each attachment `u`.

   Every row of `M₀` then holds. The two kinds that could fail do not: "`π_c(0)` contains `A_c`"
   holds because `A_c ⊆ π*`, and "an attachment's plane passes through `P`" holds because
   `v* ∈ N_{G/H}[u]`.
3. *The limit is good.* By (ii), `W₀ = ker M₀`. So for generic `(R, b)` the limit `x(0)` is a
   generic point of `ker M₀`, and its heights are a generic point of the linear space
   `proj_z ker M₀`. That space contains `L⁰_{G/H}(q')`, by 2.
   - The rank at `(q', z)` is lower semicontinuous on that linear space. So the rank at the limit
     is at least its generic value on `L⁰_{G/H}(q')`.
   - By (MC-3) (shifts by `Aff(q')`), that value is the generic value on `L_{G/H}(q')`.
   - `q'` is generic up to translation, so this is the generic rank of `X₀(G/H)`.
4. *From the limit to the generic point.* Apply (MC-36) to the family. The map
   `(q_O, δ, R, b, t) ↦ p(t)` is dominant onto `B`: `(q_O, tδ)` is a generic picture, and for
   fixed `t ≠ 0` the pinned point sweeps a dense subset of `ker M(t) ≅ L(q(t))`. So the rank
   inequality holds on a nonempty open set of parameters, hence on a dense subset of `B`, hence
   at `X₀(G)`'s generic point. ∎

*Second reading (2026-09-24): steps 3 and 4 filled in.*
- *Implicit hypothesis.* `G/H` satisfies (H), in particular `|δ(W)| ≥ 2`. Otherwise
  `N_{G/H}[v*]` has two points, no `q′` is admissible, and `X₀(G/H)` is undefined. (MC-39) supplies
  it through 2EC, which it uses for nothing else.
- *The row types of `M₀`* (read off `coreshrink.py`'s `recipe`, not the prose). There are five:
  1. core rows `ζ_w = a_c·δ_w + γ̃_c`, `w ∈ N_H[c]`;
  2. `z_w = a_c·q_w`, `w ∈ A_c`;
  3. `ζ_{c(u)} = a_u·δ_{c(u)} + γ̃_u` at each attachment `u`;
  4. `z_w = a_u·q_w`, `w ∈ N_O[u]`;
  5. the unchanged far rows.

  `γ̃_u` occurs in `M₀` only in type 3, once per `u` when `G/H` is simple. So type 3 only fixes `γ̃_u`,
  and this is the one place step 2 uses simplicity. The flat core of step 2 is KT's specialization in
  their proof of Claim 6.4 (p. 675): every core panel is set to the `v*` panel.
- *Step 3, joint genericity.* On the open set of parameters `(q_O, δ, R, b)` where (ii) holds and
  `R|_{ker M₀}` is invertible, `ker M₀` is a vector bundle over the pictures. The map to `x(0)` is
  onto its total space, so the limit heights are a generic point of `proj_z ker M₀`.
- *Step 3, `q′` is generic enough.* Translations of the plane preserve admissibility, `L` and the
  rank, so the maximal-rank locus `B°(G/H)` is translation-invariant. The slice
  `B(G/H) ∩ {q_{v*} = Q}` is a vector bundle over a nonempty open set, hence irreducible, and `B°`
  meets it (translate any point of `B°`). So for `q_O` in a nonempty open set the generic rank on
  `L_{G/H}(q′)` is the generic rank of `X₀(G/H)`.
- *Step 4.* For each fixed `t ≠ 0` the parametrization is onto `B(G)`, not just dominant. And one
  parameter in the good open set suffices: by (MC-36) it gives cofinitely many `t` with `p(t) ∈ B(G)`
  and the rank inequality. That inequality is lower semicontinuous on the irreducible `B(G)`, so it
  holds on a dense open subset.

What the recon called "the Claim-6.4 inequality comes free from linearity
(`L(G/H) ⊆ L_relaxed`)" is step 3. But containment in the relaxed space alone is not enough: the
limit must be *generic* in a space containing `L⁰_{G/H}(q')`. That is step 2 together with (ii).

> **(MC-38)** `[PROVED]` *(the core half is a statement about `X₀(G)` alone)* For `t ≠ 0`, the
> points `p(t)` of the families are generic points of `B` ((MC-37), step 4). So the hypothesis of
> (MC-34) needed here is: **`H` is infinitesimally rigid at `X₀(G)`'s generic point, restricted to
> `W`.** It holds if `X₀(H)` attains and
> **(i)** *core-free:* `proj_W L_G(q) = L_H(q|_W)` at one `q` with `q ∈ U(G)` and `q|_W ∈ U(H)`
> certified.

*Proof.*
- `proj_W L_G(q) ⊆ L_H(q|_W)` always, since `N_H[c] ⊆ N_G[c]`.
- The dimension of the left side is lower semicontinuous on `U(G)`. The right side has the
  constant dimension `ℓ₀(H)` on `U(H)`. So equality at one certified `q` gives equality at a
  generic `q`.
- Hence restriction `B_G → B_H` is dominant. `H` is rigid at `X₀(H)`'s generic point, which is
  therefore the image of a generic point of `B_G`. Rigidity is an open condition. ∎

*Second reading:* the claim's first sentence holds only for generic parameters, and nothing uses
it. (MC-39) needs only that the two dense open subsets of `B(G)` given by (MC-37) and by this claim
meet.

The two-scale limit is **not** where the core's rigidity comes from. In the `pencil` variant
below, W19's rescaled limit core is flat, with rank `17 = 18 − def₂(C₄)`, while at every `t ≠ 0`
the core has rank 18. The same happens at 4 of the 20 sampled residuals.

> **(MC-39)** `[PROVED]` *(the contraction step on `X₀`)* Let `G` satisfy (H) and be
> 2-edge-connected. Let `W` be a proper rigid set with `G/H` simple that satisfies (i) and (ii).
> Then **if `X₀(H)` and `X₀(G/H)` attain, `X₀(G)` attains.** Both `H` and `G/H` satisfy (H),
> `G/H` is 2EC, and both have fewer vertices than `G`. Without (i), the hypotheses "(i) and
> `X₀(H)` attains" can be replaced by "`H` is infinitesimally rigid at `X₀(G)`'s generic point".

*Proof.* At a generic point `p` of `B`, the core is rigid (MC-38). So
`rank R_G(L_p) = 6(|W| − 1) + rank R_{G/H}(L_p)` by (MC-34), and this is
`≥ 6(|W| − 1) + tgt(G/H)` by (MC-37), which is `tgt(G)` by (MC-35). The reverse inequality always
holds. One point of `B` at the target suffices (MC-2). For the side conditions: `v*` has degree
`|δ(W)| ≥ 2` because `G` is 2EC, and outside degrees are unchanged. ∎

This is KT 2011 §6.2's case "`G` has a proper rigid subgraph `G′` with `G/E′` simple" (Lemma 6.3,
p. 674), with two changes:
- KT's fresh hinges `Π_{G/E′,p₂}(u) ∩ Π_{G′,p₁}(v)` (6.6) are not available. A pencil hinge must
  pass through both points and lie in both planes, and the scale `t` supplies such hinges.
- KT prove Claim 6.4 by specialization plus algebraic independence. Here it becomes the
  containment (MC-37) step 2, plus linearity.

(MC-39) consumes, from the induction, **`X₀` attainment at `H` and at `G/H`**. That is the
generic-point motive, not bare existence, and it is `X₀`'s own motive, so the step composes.

> **(MC-40)** `[CONSTRUCTED]` *(`coreshrink.py --family`; the recon's certificates, re-run with the
> checks its probe lacked)* On W19 and R20, core `C₄` / `C₅` (their unique maximal rigid set;
> `G/H` has 16 vertices, target 90), the recon's recipe gives **64/64 rows at the target**:
> 2 graphs × 2 variants × 4 draws × `t ∈ {1/10, 1/100, 1/10⁴, 1/10⁸}`, ranks 108/108 and 114/114.
> The recipe keeps the outside fixed and every star exact at every `t`. At every row:
> - `q(t) ∈ U` is certified (`dim L = 13 = 3 + def₂` at W19, `14` at R20);
> - the core is rigid (18/18, 24/24);
> - `G/H` with the actual lines reaches 90/90;
> - (MC-34) is asserted.
>
> The limit `G/H` reaches 90/90 at all 16 draws, including the 8 `pencil` draws, where the limit is
> a pencil configuration of `G/H` (the induction hypothesis applies verbatim).
> *Measured, `coreshrink.py --pool` (the general construction).* The results, by pool, in the
> `relaxed` variant, over (member, maximal `W` with `G/H` simple) runs:
> - `named` 2/2; `smark` 20/20 runs (13 members); `thetas` 80/80 (69 members);
> - `exh7` 99/99 on the 85 members with such a `W`;
> - `peels` every 8th member: 196/196 (116 members);
> - `residuals` every 13th member: 20/20 (20 members).
>
> Every run with (i) and (ii) certified attains:
> - exh7 185/185, including the fallback runs below;
> - smark 20/20; thetas 80/80; peels 196/196; residuals 20/20.
>
> The `pencil` variant is OK at every run. Its points are not generic in `B`, so these runs are
> certificates for `G`, not evidence for (MC-37).

**Coverage** (the `--pool` summary lines). The figures are counts of labelled
members over the named populations and caps.
- Every sampled `residuals`, `peels` and `smark` member has a maximal rigid `W` with `G/H`
  simple. So does every `thetas` member with a proper rigid set, except 2, and those 2 are flat.
- `exh7`: of the 572 members with a proper rigid set, 85 have such a maximal `W`, and **68 of those
  85 have `def₂(G) = 0`**. Of the rest, 89 have one only among smaller rigid sets and 398 have
  none, and every one of these 487 has `def₂(G) = 0`.
- `exh8` is not classified. `--pool exh8 --classify` ran about 12 min before stopping at a member
  beyond `rigid_vertex_sets`'s 22-branch cap. The driver now skips and counts such members, but
  no `exh8` figure is recorded.
- A flat `X₀` (`def₂(G) = 0`) attains outright by (MC-5)(iii). So on `≤ 7` vertices the
  contraction step has content only at the 17 members with `def₂(G) > 0`. The larger pools are
  the informative ones.

> **(MC-41)** `[OPEN]` *(the residue (X₀-∂))* (MC-39) is conditional on (i) and (ii), and it needs
> a `W` with `G/H` simple.
> - **(∂1)** When does (i) hold?
> - **(∂2)** When does (ii) hold, or at least the containment `L⁰_{G/H}(q') ⊆ proj_z W₀` that (ii)
>   gives?
> - **(∂3)** What happens at the graphs with a proper rigid set but no rigid `W` with `G/H` simple?
>   This is KT Lemma 6.5's case, p. 676, which KT close with a degree-2 vertex (Claim 6.6).
>
> Measured:
> - (i) fails at exactly 11 exh7 runs. All are `C₄` cores (`def₂ = 1`) at non-maximal `W`, in the
>   fallback, and all have `def₂(G) = 0`: `X₀(G)` is flat, so `proj_W L_G = Aff` is 3-dimensional
>   while `dim L_H(C₄) = 4`. The core is flexible there (17/18), but `G` attains anyway, by
>   (MC-5)(iii).
> - (ii) fails at 1 relaxed run, `x7_1716440` (also flat). In the smark `pencil` sub-family it
>   fails at 3 runs, where `L0in` still holds.
> - In no relaxed run with `def₂(G) > 0`, in any of these pools, does (i) or (ii) fail.

*The recon's three predicted failure points, re-examined.*
1. **"A core with `def₂ > def₃` forced flat (N3's `C₄ + x, y`: core 17/18)."** As cited, this is
   wrong on two counts:
   - N3's instance is `K_{2,4}` with core `C₄ = 1234`. There `x` and `y` each have two core
     neighbours, 1 and 3, so `G/H` is **not simple**: the instance is failure point 2, not 1.
   - 17/18 is gate **N1**'s figure (the all-coplanar `C₄`). Gate **N3** reports **18/18** on KT's
     constrained family (`notes/Phase39-design.md`, numerics index).

   Genuine forced-flat cores with `G/H` simple do exist: the 11 exh7 runs above, all at flat
   `X₀(G)`. For a *maximal* `W` a flat core is harmless: if `H` lies in a `def₂`-rigid `K` with
   `V(K) ⊋ W`, then `K` is `def₃`-rigid (by (MC-5)(i) and connectivity), so maximality forces
   `V(K) = V`, and then `def₂(G) ≤ def₂(K) = 0`. `[PROVED]`
2. **"`G/H` with a parallel class."** This is excluded by the hypothesis of (MC-36)–(MC-39) and
   counted, not attacked: in exh7, 2 667 maximal sets have `G/H` not simple. The 487 exh7
   members with **no** maximal `W` whose `G/H` is simple are all flat (*Coverage*).
3. **"Two adjacent pinned core vertices, forcing a third scale."** This is an artifact of the
   recon's recipe, which **fixes** the outside. In the linear-system family the outside moves at
   order `t`. Adjacent pinned pairs occur at 10 exh7 runs, all OK; none occur in the other pools.

The recon's stop rule was "> 3 structurally distinct failing patterns, or a member where `X₀`
attains with no working `H`". It fires only vacuously. The failing patterns are 3 (`s = 1100`,
`1110`, `2100`: `C₄` cores with 2 or 3 attachment vertices). The members with no working `H` are
`x7_520384`, `x7_1460568` and `x7_1841496`, and every one of them has `def₂(G) = 0`.

> **(MC-42)** *(durable negatives)*
> **(a)** `[PROVED]` *(and measured, `coreshrink.py --collapse`)* *Collapsing a flexible side of a 2-cut to
> a point is lossy at leading order.* Take `θ(3,4,5)` (target 60) and collapse its 5-edge path's
> interior to `Q ∈ π_A ∩ π_B` (`POINT`). The family has rank 60 at certified points of `B`. But
> all five limit lines of the path pass through `Q`, so they span at most `dim Λ_Q = 3`, and the
> leading-order bound is `≤ 58`. It is measured 58 at 3/3 draws; the corpus's slide-in
> (§(K-pitch) Step 6) is lossless, at 60.
> The refined limit, the Grassmannian limit of the path's span, recovers 60. But it is `X^⊥`
> (Klein form) for a line `X` through `Q` with `X ≠ π_A ∩ π_B` (3/3). This is a special linear
> complex fixed by the side's internal data, so it does not decouple into a statement about the
> two sides.
> The contrast with (MC-34) is the point: a rigid core never needs a refined limit, because its
> internal motion is trivial and its internal hinges never enter `G/H`.
> **(b)** `[INFORMAL]` *(the recon's analysis; no driver, second reader owed)* At a 2-cut,
> the leading-term analysis under a one-parameter subgroup of the flag stabilizer `S(φ)` is
> smark S2's block-sum condition (B) with its exceptions (X1)–(X4)
> (`notes/pencil/workbook/attack-smark.md`, S2). Gauge families cannot change a side's rank or
> welded rank (projective invariance), so no configuration obtained this way both attains and
> welded-attains.
> **(c)** *(pointer)* The tree-packing / WW87 specialization of the contraction is §(K-slide-cl)'s
> tetrahedral collapse, refuted in §(K-slide-comb) and §(K-pure) (PC-OBS).

**What would change this.**
- A run with (i) and (ii) certified whose `G` falls short would contradict (MC-39): a proof error.
  `coreshrink.py` would still pass its (MC-34) asserts.
- A member with `def₂(G) > 0` and a maximal `W` where (i) fails, or where (ii) and the containment
  `L0in` both fail, would be the first genuine (∂1) or (∂2) witness.
- A member with `def₂(G) > 0`, a proper rigid set and no rigid `W` with `G/H` simple would be the
  first (∂3) witness.
- A second reader finding a gap in (MC-37) steps 2–4, the only non-routine step.

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`; exact ℚ for the family's linear algebra,
ranks mod `2⁶¹ − 1` with every shortfall recomputed in ℚ; sampler support is in the docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/coreshrink.py --family` | 64/64 rows at the target, `q(t) ∈ U` certified, core rigid; limit 16/16 at 90/90; 2 degenerate draws redrawn | 5.7 s |
| `python3 notes/scripts/w4/coreshrink.py --collapse` | POINT 60 / 58 / 60, SLIDE 60 / 60 / 60, at 3/3 draws; `in(R₃) = X^⊥`, `X ∋ Q`, `X ≠ M` | 0.6 s |
| `python3 notes/scripts/w4/coreshrink.py --pool named,smark,thetas` | relaxed OK 2/2, 20/20, 80/80; (i) and (ii) at every run | 89 s |
| `python3 notes/scripts/w4/coreshrink.py --pool exh7` | 99/99 maximal-`W` runs OK; fallback 86/89 members; 11 `C₄` core-flexible runs, all `def₂(G) = 0` | 47 s |
| `python3 notes/scripts/w4/coreshrink.py --pool peels --stride 8` | 196/196 relaxed runs OK (116 members); (i) and (ii) at every run | 132 s |
| `python3 notes/scripts/w4/coreshrink.py --pool residuals --stride 13` | 20/20 (20 members); (i) and (ii) at every run; 4 `pencil` runs with a flat limit core, rigid at `t ≠ 0` | 105 s |

#### Step MC13 — the short ear step with the antecedent (a second reading of (MC-27))

*A second reader of Step MC10's (MC-27), 2026-09-24, working from the sketch ("Theorem E") of the
feasibility recon of W4-reopen's third unranked direction (the `X₀` hybrid).
Every `[PROVED]` below was re-derived by the second reader; what was taken on trust is named at
each claim. Drivers `w4/earante.py` and `m2/earbad.m2` (new).*

The ear step at `k` may use the **antecedent**: `X₀(G′ + ear_{k−1})` attains. `G′ + ear_{k−1}` has
fewer vertices than `G = G′ + ear_k`, so under the strong induction of (MC-24) the antecedent is
free. Where (MC-22) applies at `G′ + ear_{k−1}` (dominance, and `λ = k` for the `(k−1)`-ear), it gives
**both** `(R_{k−1})` and `(P_{k−1})` at `X₀(G′)`'s generic point. (MC-24) used only the first.

**Notation** (added to Step MC10's). `Pen_a := Pen(p_a, π_a)` and `Pen_b := Pen(p_b, π_b)`, the
lines through a terminal point in its plane (2-dimensional). `N := Pen_a + Pen_b`: 4-dimensional in
orbits (i), (ii), 3-dimensional in orbits (iii), (iv) (the two pencils share `n` there). `star(p)`
is the 3-dimensional space of lines through `p`; `Λ²π` that of lines in `π`. `⊥` is
Klein-orthogonality; a line is Klein-orthogonal to exactly the lines it meets. The **strong
induction hypothesis** is: `X₀(H)` attains for every `H` satisfying (H) with `|V(H)| < |V(G)|`.

> **(MC-43)** `[PROVED]` *(the bad sets are monotone where it matters)* Let `1 ≤ j ≤ k ≤ 4`, with
> `λ = j + 1` for the `j`-ear (so not orbit (iii) at `j = 1`). If `r ≤ 5 − k`, then every `ρ ⊇ Pen_a`,
> and every `ρ ⊇ Pen_b`, lies in `B_k(r) ∩ B_j(r)`. So (MC-27)'s obstruction is excluded by the
> antecedent wherever (MC-22) applies to `G′ + ear_{k−1}`. More: `B_k(r) ∖ B_{k−1}(r)` is
> - **empty** at `k = 3`, in every orbit and at every `r` (MC-45);
> - **empty** at `k = 2` in orbits (i) and (ii), at every `r` (MC-46);
> - **nonempty** at `k = 2` in orbit (iv), for `r = 1, 2, 3` (MC-47);
> - not the relevant set at `k = 2` in orbit (iii), where the 1-ear has `λ = 1` and (MC-22) does
>   not apply to the antecedent; `B₂(r)` itself is given in (MC-47).

*Proof.* Every `j`-ear placement has `x₁ ∈ π_a` (for `j = 1`, `x₁ ∈ m ⊂ π_a`). So `Λ_j` contains
`p_a ∧ x₁`, a nonzero vector of `Pen_a`, and likewise `x_j ∧ p_b ∈ Pen_b`. The (P_j) value
`max(0, r + j − 5)` is `0` because `r ≤ 5 − k ≤ 5 − j`. The four bullets are (MC-45), (MC-46), (MC-47). ∎

> **(MC-44)** `[PROVED]` *(the chord gadget gives `(R₀)`, hence every `(R_k)`)* Let `a ≁ b` in `G′`.
> If `X₀(G′)` and `X₀(G′ + ab)` both attain, then at `X₀(G′)`'s generic point
> **`r ≥ min(δ, 5)`**. So `(R_k)` holds for every `k ≥ 0`, and **`r = δ` whenever `δ ≤ 5`**. In the
> ear step at `G = G′ + ear_k` (`k ≥ 1`), `G′ + ab` is simple, satisfies (H) and has fewer vertices
> than `G`, so under the strong induction both hypotheses hold. This supersedes the last two
> bullets of (MC-24) whenever `a ≁ b`: `(R₁)` **is** reachable, and `(R₂)` does not need `dim U ≠ 1`.

*Proof.* `U(G′)` and `U(G′ + ab)` are dense open in `K^{2V}`, so there is `q` in both. Over it, pick
`z₀ ∈ L_{G′+ab}(q)` at which `G′ + ab` attains (a dense open set of such points exists). Adding a
vertex's neighbour only adds lifting conditions, so `L_{G′+ab}(q) ⊆ L_{G′}(q)` and `z₀ ∈ B(G′)`.
Let `M_weld(p) := {X ∈ M_{G′}(p) : X_a = X_b}`. It is contained in `M_{G′+ab}(p)`, because the new
hinge only asks `X_b − X_a ∈ ⟨n⟩`. Attainment at `z₀` and (MC-17)'s count with `k = 0`
(`def₃(G′ + ab) = f − min(δ, 5)`) give `dim M_weld(z₀) ≤ 6 + f − min(δ, 5)`. `dim M_weld` is the
kernel dimension of a matrix polynomial in the point, so it is upper semicontinuous on the
irreducible `B(G′)`. At the generic point `dim M_weld ≤ 6 + f − min(δ, 5)`, and `dim M_{G′} = 6 + f`.
Since `r = dim M_{G′} − dim M_weld`, `r ≥ min(δ, 5)`. With `r ≤ δ` ((MC-16)) this is `r = δ` for `δ ≤ 5`. ∎

So (MC-23) holds at every `(G′, a, b)` with `a ≁ b` and `δ ≤ 5` for which (MC-10)(a) holds at `G′`
and at `G′ + ab`. That is a reduction, not a proof of (MC-23).

> **(MC-45)** `[PROVED]` *(`k = 3`, every orbit)* For every `ρ` and every flag pair with
> `p_a ≠ p_b`: `(P₂) ⟹ (P₃)`. Hence, **under the strong induction, the open-ear step with `k = 3`
> holds in every orbit**: if `X₀(G′)` attains, so does `X₀(G′ + ear₃)`. Nothing in this uses
> Jackson–Jordán.

*Proof of the implication.* At `r = 0` there is nothing to prove. At `r = 1`, `(P₃)` holds for every
`ρ`, since `⋂Λ₃ = 0` in all four orbits (MC-26). At `r ≥ 3` it is (MC-26). The new case is `r = 2`,
where `(P₃)` asks `ρ + Λ₃ = K⁶`.

*The splitting degeneration* (the hybrid recon's device, checked here). Let `y = (y₁, y₂)` be a generic
2-ear placement. By `(P₂)`, `ρ ∩ Λ₂(y) = 0`, so `W(y) := ρ + Λ₂(y)` is a hyperplane. For `u ∈ K⁴` and
`t ≠ 0` the 3-ear `(x₁, x₂, x₃) = (y₁, y₁ + tu, y₂)` is a placement. Its lines are `p_a y₁`,
`t · y₁ ∧ u`, `(y₁ + tu) ∧ y₂` and `y₂ p_b`. Divide the second by `t`. The four rows are then
polynomial in `t`, and at `t = 0` they span `Λ₂(y) + ⟨y₁ ∧ u⟩`. Rank is lower semicontinuous, in `t`
and on the irreducible placement space. So the generic `dim(ρ + Λ₃)` is at least
`dim(W(y) + ⟨y₁ ∧ u⟩)`. It is `6` unless `y₁ ∧ u ∈ W(y)` for every `u`, that is,
**`star(y₁) ⊆ W(y)`**. Colliding `x₂` with `x₃` instead gives the second condition `star(y₂) ⊆ W(y)`.
`(P₃)` can fail only if both hold at generic `y`.

*The `x₁` end, orbits (i)–(iii).* Put `V(y) := star(y₁) + Λ₂(y) = star(y₁) + ⟨y₂ ∧ p_b⟩`, which is
4-dimensional. As `Λ₂(y) ⊆ V(y)`, the modular law gives `star(y₁) ⊆ W(y)` iff `ρ ∩ V(y) ≠ 0`. For a
2-form `c` let `φ_c(x) := c ∧ y₁ ∧ x`. This is a linear form on `K⁴/⟨y₁⟩`, and `φ_c = 0` iff
`c ∈ star(y₁)`. So `c ∈ V(y)` iff `φ_c` is a multiple of `φ_{y₂∧p_b}`, whose kernel is the plane
`⟨y₁, y₂, p_b⟩`. Fix a generic `y₁ ∈ π_a`. Then `y₁ ∉ π_b`, and as `y₂` runs over `π_b` that plane runs
over all planes through the line `y₁ p_b`. So `ρ ∩ V(y) ≠ 0` for generic `y₂` iff one of these holds:
- **(α)** `ρ ∩ star(y₁) ≠ 0`;
- **(β)** every `φ_c` with `c ∈ ρ` vanishes at `p_b`, that is, `y₁ ∧ p_b ⊥ ρ`.

Both are closed in `y₁`. So one of them holds for every `y₁ ∈ π_a`.
- (α) for every `y₁`: `ρ` contains a line through every point of `π_a`. A 2-plane of 2-forms holds
  at most two lines unless it is a pencil `Pen(p, σ)`, whose lines cover exactly `σ`. So
  `ρ = Pen(p, π_a)`, and `ρ ⊆ Λ²π_a`.
- (β) for every `y₁`: `ρ ⊆ S_b^⊥`, with `S_b := span{y₁ ∧ p_b : y₁ ∈ π_a}`. If `p_b ∉ π_a`, then
  `S_b = star(p_b)` and `S_b^⊥ = star(p_b)`. If `p_b ∈ π_a`, then `S_b = Pen(p_b, π_a)` and
  `S_b^⊥ = star(p_b) + Λ²π_a`, which contains `Λ²π_a`.

The `x₃` end is the same with `a ↔ b`: `ρ ⊆ Λ²π_b` or `ρ ⊆ S_a^⊥`.

*The four combinations*, for a 2-dimensional `ρ`:
- **Orbit (i).** `Λ²π_a ∩ Λ²π_b = ⟨m⟩` and `star(p_a) ∩ star(p_b) = ⟨n⟩` are too small.
  `Λ²π_a ∩ star(p_a) = Pen_a` and `star(p_b) ∩ Λ²π_b = Pen_b`. So `ρ ∈ {Pen_a, Pen_b}`. This is
  the hybrid recon's four-end classification, which is correct.
- **Orbit (ii)**, say `p_b ∈ π_a` and `p_a ∉ π_b`. The `x₁` end gives `ρ ⊆ star(p_b) + Λ²π_a`, the
  lines meeting every line of `Pen(p_b, π_a)`. The `x₃` end gives `ρ ⊆ Λ²π_b` or `ρ ⊆ star(p_a)`.
  A line of `π_b` meets every line of `Pen(p_b, π_a)` iff it passes through `p_b`. A line through
  `p_a` does iff it lies in `π_a`. So again `ρ ∈ {Pen_a, Pen_b}`.
- **Orbit (iii).** Both ends: `ρ ⊆ (Pen(p_b, π_a) + Pen(p_a, π_b))^⊥`, which is the 3-dimensional
  `N = Pen_a + Pen_b`. Every such `ρ` meets `Λ₂(y) ∩ N ⊇ ⟨p_a y₁, y₂ p_b⟩`, a 2-plane of the same
  3-space, so it violates `(P₂)`.
- **Orbit (iv)**, `π_a = π_b = π`. Here `Λ₂(y) = Λ²π` for every placement (MC-47), so
  `W = ρ ⊕ Λ²π`. The `x₁` end alone would need `y₁ ∧ u ∈ W` for all `y₁ ∈ π` and `u ∈ K⁴`. These
  span `π ∧ K⁴ = Λ²K⁴ ≠ W`, so the `x₁` end already gives `(P₃)`.

In orbits (i) and (ii) the survivors `Pen_a`, `Pen_b` violate `(P₂)` by (MC-43). ∎

*Proof of the ear step.* `X₀(G′ + ear₂)` attains by the induction hypothesis. The restriction is
dominant (MC-18)(a), and `λ = 3` in every orbit (MC-19)(b). So (MC-22) gives `(R₂)` and `(P₂)`.
`(R₂)` gives `(R₃)`, the implication gives `(P₃)`, and (MC-22) at `G` concludes. ∎

> **(MC-46)** `[PROVED]` *(`k = 2`, orbits (i) and (ii))* Let the flag pair be in orbit (i) or (ii),
> and let `r ≤ 3`. Then **`ρ ∈ B₂(r)` iff `ρ ⊇ Pen_a`, or `ρ ⊇ Pen_b`, or (`r = 3` and `ρ ⊆ N`)**.
> Each of the three families lies in `B₁(r)`. So, in these orbits, `(P₁) ⟹ (P₂)` for every `ρ`
> (`r ≥ 4` is (MC-26), and `B₂(1) = ∅`). Hence **under the strong induction the `k = 2` open-ear
> step holds whenever `X₀(G′)`'s generic flag pair is in orbit (i) or (ii) and `dim U ≠ 1`.** The
> orbit-dimension table the proof uses is checked by `earante.py --orbits`, with exact symbolic
> minors. The classification itself is re-checked, independently, by `earbad.m2` (B2).

*Proof.* Let `S` be the stabiliser of the flag pair in `PGL₄`: `dim S = 5` in orbit (i) and `6` in
orbit (ii). `S` maps placements to placements. It acts on 2-ear placements with an open orbit, and
`--orbits` asserts that orbit is 4-dimensional. Fix `x⁰` in it and put `B := Λ₂(x⁰)`. By
semicontinuity, `(P₂)` holds iff `ρ ∩ gB = 0` for one `g ∈ S`. Let
`I := {(g, [c]) : c ∈ B, g·c ∈ ρ}`. Then `ρ ∈ B₂(r)` forces `I → S` onto, so `dim I ≥ dim S`.
We show `dim I < dim S` outside the three families.

Stratify `P(B)` by `S`-orbit type. Write `B = span(L₀, L₁, L₂)` for `L₀ = p_a x₁`, `L₁ = x₁x₂`,
`L₂ = x₂ p_b`, and `y = [l₀L₀ + l₁L₁ + l₂L₂]`. The fibre of `I` over `y` has dimension
`dim(P(ρ) ∩ S·y) + dim S − d_y`, where `d_y := dim S·y`. `--orbits` certifies the `d_y`:
- orbit (i): `d_y = 4` where `l₁ ≠ 0`; `3` on the line `l₁ = 0`; `1` at `L₀` and at `L₂`;
- orbit (ii): `d_y = 5` where `l₀l₁l₂ ≠ 0`; `4` where `l₀l₂ = 0 ≠ l₁`; `3` on `l₁ = 0`; `1` at `L₀`
  and at `L₂`.

`S` preserves `Pen_a`, `Pen_b` and `N`. The line `l₁ = 0` is `span(L₀, L₂) ⊆ N`, and its orbit is
open in `P(N)`. `S·L₀ ⊆ P(Pen_a)` and `S·L₂ ⊆ P(Pen_b)`. The counts, with `dim P(ρ) = r − 1 ≤ 2`:
- *Orbit (ii), `l₀l₁l₂ ≠ 0`:* `2 + (r − 1) + 1 ≤ 5`.
- *Orbit (ii), `l₀l₂ = 0 ≠ l₁`:* `1 + (r − 1) + 2 ≤ 5`.
- *Orbit (i), `l₁ ≠ 0`.* Here the plain count gives only `5`, so use the two quadrics of the
  attack's S1(i): `Q₁ = x_M x_L` and `Q₂ = det[x_u | x_v]`. They are semi-invariants of one character
  (`--orbits` re-checks this at 5 group elements). So `S·y` lies on the member
  `Q_{I(y)} := {Q₂(y)Q₁ = Q₁(y)Q₂}` of their pencil. On `P(B)`, `I(y) = [l₁²αβ − l₀l₂ : l₁²αβ]` is not
  constant, so its level sets are curves. If `P(ρ)` lies on two members, it lies in `{Q₁ = 0}`,
  which `S·y` misses (`Q₁(y) ≠ 0` when `l₁ ≠ 0`). Otherwise at most one level set has
  `dim(P(ρ) ∩ S·y) = r − 1`, and elsewhere it is `≤ r − 2`. The bound is
  `max(2 + (r − 2) + 1, 1 + (r − 1) + 1) = r + 1 ≤ 4`. (This is the attack's S2 generic-stratum step,
  with the fix of its review note S10(i).)
- *Both orbits, `l₁ = 0`:* `1 + (c_ρ(N) − 1) + (dim S − 3) < dim S` iff `c_ρ(N) := dim(ρ ∩ N) ≤ 2`.
  This fails only for `r = 3` and `ρ ⊆ N`.
- *Both orbits, `L₀`:* `0 + (dim(ρ ∩ Pen_a) − 1) + (dim S − 1) < dim S` iff `ρ ⊉ Pen_a`. Likewise at
  `L₂` with `Pen_b`.

So outside the three families `dim I < dim S`, and `(P₂)` holds.

Conversely, each family is bad. `Pen_a ∋ p_a ∧ x₁`, and `Pen_b` likewise. For `r = 3` and `ρ ⊆ N`,
the space `Λ₂ ∩ N ⊇ ⟨p_a x₁, x₂ p_b⟩` is a 2-plane in the 4-dimensional `N`, which `ρ` meets. Each
family lies in `B₁(r)`, since `Λ₁(y) = span(p_a y, y p_b) ⊆ N`, with `p_a ∧ y ∈ Pen_a` and
`y ∧ p_b ∈ Pen_b`.

*The ear step.* `dim U ≠ 1` gives dominance of `G′ + ear₁` (MC-18)(b). Not orbit (iii) gives
`λ = 2` (MC-19)(b). With the induction hypothesis at `G′ + ear₁`, (MC-22) gives `(R₁)` and `(P₁)`,
hence `(R₂)` and `(P₂)`. ∎

This is the attack's S14(iii), `m = 2`, `δ′ ≤ 3` case, specialised to the one partner `B = Λ₂`. For
that partner `P(B)` meets only five orbit strata, so none of S2's exceptions (X1)–(X4) can arise.
The specialisation adds orbit (ii), which S14 does not treat.

> **(MC-47)** *(`k = 2` in orbits (iii) and (iv): what the antecedent cannot kill)*
> **(i)** `[PROVED]` In orbit (iv), `Λ₂ = Λ²π` at **every** 2-ear placement. So
> `B₂(r) = {ρ : ρ ∩ Λ²π ≠ 0}` for `r ≤ 3`, and it is **not** contained in `B₁(r)`: `ρ = ⟨ℓ⟩ + (generic)`,
> with `ℓ` a generic line of `π`, has `(P₁)` but not `(P₂)`. On `X₀` orbit (iv) is `U = 0`. So
> `r = 0` modulo Jackson–Jordán (Step MC10's remark after (MC-26)), and the step is closed only
> modulo that.
> **(ii)** `[CONSTRUCTED]` *(`M2 --script notes/scripts/m2/earbad.m2`, check (B3))* In orbit (iii), `B₂(1) = ∅`,
> `B₂(2) = {ρ ⊆ N}` and `B₂(3) = {dim(ρ ∩ N) ≥ 2}`, with `N` 3-dimensional; also `B₃(2) = {ρ ⊆ N}`.
> The inclusions `⊇` are `[PROVED]`: `Λ₂ ∩ N ⊇ ⟨p_a x₁, x₂ p_b⟩`. Orbit (iii) has `dim U ≤ 1`, so
> the 1-ear antecedent is not dominant, and `λ = 1` besides. **No antecedent is available**, and the
> cell stays open.

*Proof of (i).* All four points `p_a, x₁, x₂, p_b` lie in `π`, generically in general position, and
the three chain lines are then independent in the 3-dimensional `Λ²π`. For the non-containment,
`Λ₁(y) = Pen(y, π)`, and `ℓ ∈ Pen(y, π)` iff `y ∈ ℓ`. ∎

> **(MC-48)** *(flag genericity on the habitat)* Let `G′` satisfy (H) with `a ≁ b`, and suppose
> **(c)** `5|E(K)| ≤ 6(|V(K)| − 1)` for every subgraph `K ⊆ G′` on at least 2 vertices.
> **(i)** `[PROVED]` The all-singletons partition is `def₂`-optimal for `G′`, and
> `δ₂ := def₂(G′) − def₂(G′/ab) ≥ 2`.
> **(ii)** `[PROVED-MOD]` *((MC-33): Jackson–Jordán at `G′ + ab`)* At generic `q`, the two incidence functionals
> `φ₁(z) = z_b − h_a(q_b)` and `φ₂(z) = z_a − h_b(q_a)` are independent on `L_{G′}(q)`. Hence
> **`X₀(G′)`'s generic flag pair is in orbit (i), and `dim U ≥ 2`**.
> **(iii)** `[PROVED]` The hypotheses hold when `G = G′ + ear_k`, with `k ≤ 4`, is in `hK`'s habitat.
> **(iv)** Consequently, on `hK`'s habitat, and under the strong induction:
> - the `k = 3` step holds (MC-45);
> - the `k = 2` step holds modulo Jackson–Jordán, (MC-46) with (ii);
> - only `k = 1` remains (MC-51).

*Proof.* **(i)** Refining a part `X` of a partition into singletons changes
`val(P) = 3(|P| − 1) − 2d(P)` by `3(|X| − 1) − 2e(X)`. By (c) this is at least `0.6(|X| − 1) ≥ 0`, so
the singletons are optimal. For `δ₂`, take `P` with `a, b` in one part `X₀`. Then
`val(singletons) − val(P) ≥ 3(|X₀| − 1) − 2e(X₀)`. Using (c) and `a ≁ b`, this is at least:
- `3` when `|X₀| = 2` (`e = 0`);
- `2` when `|X₀| = 3` (`e ≤ 2`);
- `3` when `|X₀| = 4` (`e ≤ 3`);
- `≥ 0.6(|X₀| − 1) > 2` when `|X₀| ≥ 5`.

**(ii)** Adding the edge `ab` asks `π_a ∋ p_b` and `π_b ∋ p_a`. So
`L_{G′+ab}(q) = L_{G′}(q) ∩ ker φ₁ ∩ ker φ₂`. The partition count of (MC-13)(b) gives
`def₂(G′ + ab) = max(f₂^sep − 2, g₂)`, where `f₂^sep` maximises over partitions separating `a, b`
and `g₂ = def₂(G′/ab)`. By (i) this is `def₂(G′) − 2`. The hard direction of Jackson–Jordán at the
simple graph `G′ + ab` gives, at generic `q`, `dim L_{G′+ab} = 1 + def₂(G′)`. (MC-4)(b) at `G′` gives
`dim L_{G′} ≥ 3 + def₂(G′)`. So the codimension is `2`, and `φ₁, φ₂` are independent. Both factor
through `z ↦ P_a − P_b ∈ U`, since `φ₁ = −(P_a − P_b)(q_b)` and `φ₂ = (P_a − P_b)(q_a)`. So
`dim U ≥ 2`. At generic `z` both are nonzero, so `p_b ∉ π_a` and `p_a ∉ π_b`; and `π_a ≠ π_b`.
This is the pattern of (MC-13)(c)'s "only if": Jackson–Jordán at an augmented graph, (MC-4)(b) at
the base.

**(iii)** Every `K ⊆ G′` has `V(K) ⊊ V(G)`. If `5|E(K)| > 6(|V(K)| − 1)`, the 5-fold edge set of `K`
is dependent in the union of six cycle matroids. A circuit `C` of that union has
`|C| = 6(|V(C)| − 1) + 1` and is connected. So `C − e` is six edge-disjoint spanning trees of
`V(C)`, and `G[V(C)]` is a proper rigid subgraph. This is the attack's S16(ii), re-derived here.
If `a ∼ b` in `G′`, the cycle `a x₁ … x_k b` has `k + 2 ≤ 6` vertices. It is then rigid and proper,
since `|V(G′)| ≥ 3`. ∎

`[MEASURED earante.py --thetas 14, --habitats]` At every tested instance satisfying (c) —
45/45 θ-instances; 342/342 in the stride-8 habitat sample; 2 811/2 811 in the full pool — the drawn
point shows flag genericity, orbit (i) and `dim U ≥ 2`, as (ii) predicts.

So the hypothesis is on `G′`, not on `G`: `G′` need not be in the habitat (it may have a bridge, or
no degree-2 vertex). It needs only (c) and `a ≁ b`. (c) is weaker than "no `def₃`-rigid subgraph":
`C₆` satisfies (c) with equality and is rigid.
- (MC-15)(i) is the corresponding statement for `G` itself: no `def₂`-rigid subgraph.
- (MC-18)(b)'s dominance condition `dim U ≠ 1` is implied by (ii).

> **(MC-49)** `[PROVED]` *(`k = 1`, large `δ`: the degenerate chord point)* Let `a ≁ b`, let
> `dim U ≥ 2` at generic `q`, and let `X₀(G′ + ab)` attain. If `δ ≥ 5`, then `X₀(G′ + ear₁)` attains.
> `X₀(G′)` attaining is not used.

*Proof.* Take `z₀` as in (MC-44), and a point `y₀ ≠ p_a, p_b` on `n`. By (MC-18)(b)'s proof, the part of
`X₀(G)` over `q` contains the whole zero set `{(z′, q_y) : (h_a − h_b)(q_y) = 0}`. That set is
irreducible since `dim U ≥ 2`, and its generic points lie in `B(G)`. At `z₀`, `h_a − h_b` vanishes on the line `q_a q_b`, so `(z₀, y₀)` is a point of
`X₀(G)`. There both ear hinges are the line `n`. So `M_G = {(X, X_y) : X ∈ M_{G′+ab}(z₀),
X_y − X_a ∈ ⟨n⟩}`, and `dim M_G = 6 + f − min(δ, 5) + 1`. For `δ ≥ 5` this is `6 + f − 4 = 6 + def₃(G)`
by (MC-17). Upper semicontinuity concludes. ∎ This is the hybrid recon's argument, re-derived; the recon
did not state `dim U ≥ 2`, which is what puts `(z₀, y₀)` on `X₀(G)` here. Step MC11 reaches the
same conclusion at the same point without `dim U ≥ 2` ((MC-30), (MC-31): `p_x ∈ p_a p_b` is the
chord point `y₀ ∈ n`), using Jackson–Jordán's equality at `G″ = G′ + ab` instead, to exclude
`U = Kℓ_ab`.

> **(MC-50)** `[INFORMAL]` *(gap: the first-order limit plane is a sketch; second reader owed)*
> *(`k = 1`, `δ ≤ 4`: reduction to the chord point)* Assume the hypotheses of (MC-49), flag
> genericity (MC-48)(ii) at `q`, and `π_a ≠ π_b` at `z₀`. The last fails when `a, b` have a common
> neighbour, since then `π_a = π_b` at every point of `L_{G′+ab}`. If
> `dim((ρ(z₀) ∩ n^⊥) + ⟨n⟩) ≤ 4`, then `X₀(G′ + ear₁)` attains. At `δ ≤ 5`, `n ∉ ρ(z₀)` and
> `r(z₀) = δ + a′(z₀)`, where `a′(z₀) := dim M_{G′}(z₀) − 6 − f` `[PROVED]`: (MC-16) at `k = 0` with
> attainment gives `r(z₀) − dim(ρ(z₀) ∩ ⟨n⟩) = min(δ, 5) + a′(z₀)`, and the partition bound
> `dim M_weld ≥ 6 + g` gives `r(z₀) ≤ δ + a′(z₀)`. Both are asserted by `earante.py --chord`.
> So the condition holds when `δ + a′(z₀) ≤ 3`. It fails only if `ρ(z₀) ∩ n^⊥` is 4-dimensional:
> at `r(z₀) = 4`, only if the bar along `ab` is already implied in `G′` at `z₀`.

*Sketch.* Move along `z(s) = z₀ + s z₁`, with `z₁ ∈ L_{G′}(q)` and `q_y(s)` on the line
`(h_a − h_b)(s) = 0` through `q_{y₀}`. For generic `s` this is a curve in `B(G)`. The ear's span
`Λ(s)` tends to a pencil `Pen(y₀, σ̄)` with `σ̄ ⊃ n`. To first order, `σ̄` is determined by
`(φ₁(z₁), φ₂(z₁))`, so under flag genericity every plane through `n` occurs. Semicontinuity gives
`dim M_G ≤ dim M_{G′}(z₀) − r(z₀) + dim(ρ(z₀) ∩ Pen(y₀, σ̄))`, and this is the target once
`ρ(z₀) ∩ Pen(y₀, σ̄) = 0`. The pencils `Pen(y₀, σ̄)/⟨n⟩` are the isotropic lines of the quadratic
space `n^⊥/⟨n⟩`, a smooth quadric surface's worth. So a good pencil exists unless
`(ρ(z₀) ∩ n^⊥) + ⟨n⟩ = n^⊥`. **Gap:** the first-order computation of `σ̄`. `earante.py --chord`
asserts at every tested instance that the computed limit is a pencil through `y₀` containing `n`,
and records whether two draws of `z₁` give distinct planes. At an instance where the recorded
bound equals the target, the constructed curve **certifies** that instance.

`[MEASURED earante.py --chord-habitats --stride 4]` Every `k = 1` instance of the 222-member
sample of `hK`'s class shapes (269 instances) has `δ = 4`, `a′(z₀) = 0`, `r(z₀) = 4` and
`dim(ρ(z₀) ∩ n^⊥) = 3`, and its constructed curve reaches the target: 269/269.
`[MEASURED earante.py --chord-thetas 14]` Of the 32 θ-instances with `δ ≤ 4`, 13 have a
computable limit (the other 19 have a common neighbour of `a, b`), and 13/13 reach it.
`[MEASURED earante.py --chord-habitats]` On the full pool of 888 class shapes (1 075 `k = 1`
instances), the same holds at 1 075/1 075. Step MC11's (MC-32) measures the same cell at the same
point from the other side: moving `x` off `p_a p_b` gives first-order gain `≥ 1` at every needed
instance on ≤ 8 vertices.

> **(MC-51)** `[OPEN]` *(restates (MC-27): the open-ear cells that remain)* Under the strong
> induction, and with `a ≁ b` (so that (MC-44) supplies every `(R_k)`), the open-ear step is proved:
> - for `k ≥ 5` (MC-20);
> - for `k = 4` (MC-25);
> - for `k = 3` in every orbit (MC-45);
> - for `k = 2` when the generic flag pair is in orbit (i) or (ii) and `dim U ≠ 1` (MC-46);
> - for `k = 1` when `δ ≥ 5` and `dim U ≥ 2` (MC-49), or when `δ ≥ 5` alone, modulo Jackson–Jordán
>   at `G′ + ab` (MC-31).
>
> **Open:**
> - **(a)** `k = 2` with `dim U = 1`, in orbits (i)–(iii). The 1-ear antecedent is not dominant, and
>   in orbit (iii) `λ = 1` besides. The bad sets are (MC-46) in (i)–(ii) and (MC-47)(ii) in (iii).
>   *(Closed wherever `δ = 0`: (MC-54), Step MC14.)*
> - **(b)** `k = 2` in orbit (iv) (`U = 0`): closed only modulo Jackson–Jordán (MC-47)(i).
>   *(Closed wherever `δ = 0` without Jackson–Jordán: (MC-54), Step MC14.)*
> - **(c)** `k = 1` with `dim U ≥ 2` and `δ ≤ 4`: `(P₁)`. *(At `δ = 0` it holds: (MC-54), Step MC14;
>   the open cell is `1 ≤ δ ≤ 4`.)* (MC-50) reduces it to one condition at
>   the chord point. `k = 1` with `dim U = 1` (dominance fails, and in orbit (iii) `λ = 1`) is open
>   outright. `k = 1` with `U = 0` is closed modulo Jackson–Jordán, as in (b).
>
> With `a ∼ b` (then orbit (iii)), (MC-44) is not available. `k ≥ 3` is as above; `k ≤ 2` is open.
> On `hK`'s habitat, by (MC-48), only (c) with `δ ≤ 4` remains, modulo Jackson–Jordán.
> `earante.py --chord-habitats` closes it at every tested class-shape instance.
> The (MC-27) text (the Pen obstruction, the exact `k = 1` criterion in orbit (i)) stands. Its
> `k = 2, 3` part is answered by (MC-43)–(MC-47); its `k = 1` part by (MC-44), (MC-49), (MC-50).

**What was re-derived, and what was taken on trust.**
- *Re-derived by the second reader:* (MC-43)–(MC-46), (MC-47)(i), (MC-48)(i) and (iii) (including the
  attack's S16(ii) circuit argument), (MC-48)(ii)'s reduction to Jackson–Jordán, (MC-49).
- *Re-read, not re-derived:* the proofs of (MC-16), (MC-17), (MC-22) and (MC-26).
- *Taken on trust:*
  - Jackson–Jordán's hard direction, in (MC-48)(ii) and (MC-47)(i);
  - the `⋂Λ = 0` certificates of `earstep.py --lamcap`;
  - the orbit-dimension table (a computation, `--orbits`);
  - `m2/earbad.m2` for (MC-47)(ii).
- *Not re-derived:* the attack's S1 table beyond the five strata used, and S2 in general.

**The hybrid recon's errors and omissions.**
- The four-end classification uses `star(p_b)`, which is right in orbit (i) only. In orbits (ii)
  and (iii) it must be `star(p_b) + Λ²π_a` when `p_b ∈ π_a`. The conclusion survives there, and in
  orbit (iv) (MC-45).
- "`k = 2` needs S2 with (X1)–(X4)": for the partner `Λ₂` the exceptions are vacuous (MC-46).
- The `k = 1` chord argument omits `dim U ≥ 2` (MC-49).
- It misses that the chord gives `(R₀)` (MC-44).
- "FG ⟺ `δ₂ ≥ 2` under Jackson–Jordán at `H′ + wv`": only `⟸` holds with that one citation, and
  only `⟸` is used.
- "FG PROVED on the habitat": only the combinatorial half is proved; the rest is modulo
  Jackson–Jordán (MC-48).

**What would change this:**
- an `earante.py` assert firing: (MC-16), (MC-22), (MC-45), (MC-46) or (MC-48)(i);
- `--orbits` failing to certify a stratum of the table;
- an `m2/earbad.m2` check failing;
- an instance where `(P₂)` holds and `(P₃)` fails;
- or one in orbit (i)/(ii) where `(P₁)` holds and `(P₂)` fails.

**Drivers** (Python at `PYTHONHASHSEED=0`, seed `20260924`, exact ℚ except the mod-`2⁶¹ − 1`
attainment screen of `G′`, which is a certificate and is re-derived exactly; `M2` 1.26.06,
`randomness: none`; sampler support is in `earante.py`'s docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/earante.py --orbits` | orbit-dimension table certified, orbits (i), (ii); transitivity; semi-invariance | 0.4 s |
| `python3 notes/scripts/w4/earante.py --frames` | the (MC-43)/(MC-46)/(MC-47) families bad and a random `ρ` good, every orbit, `k ≤ 3`, `r ≤ 3` | 0.5 s |
| `M2 --script notes/scripts/m2/earbad.m2` | (B0)–(B4) OK: `B₃(2) ⊆ B₂(2)` in all orbits; `B₂` classified in all four | 2.9 s |
| `python3 notes/scripts/w4/earante.py --exh 6` | 354 non-adjacent pairs, all `r = 0` (only `C₇`'s 14 pairs have `δ > 0` on ≤ 7 vertices, so `--exh 7` adds nothing), 0 failures | 45 s |
| `python3 notes/scripts/w4/earante.py --thetas 14` | 50 instances, all orbit (i), `r = 0..5`; 0 `(P_{k−1})`-but-not-`(P_k)`; FG at 45/45 count-instances | 12 s |
| `python3 notes/scripts/w4/earante.py --habitats --stride 8` | 342 instances (211 at `k = 2`, `r = 3`; 131 at `k = 3`, `r = 2` — exactly (MC-27)'s cells), all orbit (i), all FG, all certified `r = δ`; `(P_k)` at 342/342 | 201 s |
| `python3 notes/scripts/w4/earante.py --habitats` | the full pool: 2 811 instances (1 724 at `k = 2`, `r = 3`; 1 087 at `k = 3`, `r = 2`), the same profile; 0 failures | 1 374–1 499 s (over the ceiling, run backgrounded; `--stride 8` is the foreground form) |
| `python3 notes/scripts/w4/earante.py --chord 6` | 354 pairs, all `δ = 0`; identities asserted | 25 s |
| `python3 notes/scripts/w4/earante.py --chord-thetas 14` | 35 pairs; 13/13 computable `δ ≤ 4` limits reach the target | 8 s |
| `python3 notes/scripts/w4/earante.py --chord-habitats --stride 4` | 269 pairs, all `δ = 4`, `a′ = 0`, `dim(ρ(z₀) ∩ n^⊥) = 3`; 269/269 reach the target | 183 s |
| `python3 notes/scripts/w4/earante.py --chord-habitats` | 1 075 pairs, the same profile; 1 075/1 075 | 732 s (over the ceiling; `--stride 4` is the foreground form) |

#### Step MC14 — which graphs the `X₀` induction reaches (W4-reopen P1, step 4)

*Worked 2026-09-24 by a forked agent, as step 4 of W4-reopen P1's later 2026-09-24 plan. Driver
`w4/x0arms.py` (new). It replaces four scratch probes of the feasibility recon of W4-reopen's
third unranked direction (the `X₀` hybrid): a first-arm classifier, a recursion, a necklace check
and a gluing check. The question: take an induction on `|V|` whose motive is (MC-10)(a),
"`X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)`". Which graphs does it reach, using the
landed steps and the lemmas proved here? Every `PROVED` claim below was derived by that agent end
to end. None has had a second reader. **Coverage is measured here, not proved:** there is no theorem
that every graph is covered ((MC-61)).*

**Covered.** A graph `G` satisfying (H) is **covered** if some step below applies at `G` and every
graph the step consumes is covered.
- Every step consumes graphs with fewer vertices (MC-55)(i). So "covered" is well defined by strong
  induction on `|V|`, and it does not depend on the order in which steps are tried.
- The driver reports the *first* covering step in the order of the table.
- Two switches: `--ear23 antecedent` turns on Step MC13's cells; `--delta0 off` drops (MC-54).
  The default is `--ear23 none --delta0 on`.

| step | claim | consumes | applicability |
|---|---|---|---|
| BASE | (MC-21)(a): `G` a cycle | — | structural |
| THETA | (MC-21)(b): `G` a θ-graph | — | structural |
| CUT | (MC-52): a cut vertex | the two pieces | structural |
| BRIDGE | (MC-53): a chain of bridges | the two pieces | structural |
| EAR, closed or open `k ≥ 5` | (MC-20) | `G′` | structural |
| EAR, open `k = 4` | (MC-24), (MC-25) | `G′`, `G′ + ear₂` | structural |
| EAR, open `k = 3` (`--ear23`) | (MC-45), every orbit | `G′`, `G′ + ear₂` | structural |
| EAR, open `k = 2` (`--ear23`) | (MC-46): orbit (i) or (ii), `dim U ≠ 1` | `G′`, `G′ + ear₁` | `dim U ≥ 2` certified at `q ∈ U(G′)` |
| SPLITOFF | (MC-31): `δ ≥ 5` | `G″ = G′ + ab` | structural, plus JJ at `G″` |
| FLAT | (MC-5)(ii): `def₂ = def₃` | — | structural, plus JJ at `G` |
| EAR, open `k = 2, 3` at `δ = 0` | (MC-54) | `G′` | structural |
| EAR, open `k = 1` at `δ = 0` | (MC-54) | `G′` | `dim U ≥ 2` certified at `q ∈ U(G′)` |
| EAR, open `k = 2`, orbit (iv) (`--ear23`) | (MC-47)(i), modulo JJ | `G′` | `δ₂ = 0` (combinatorial) |
| CONTRACT | (MC-39) | `H = G[W]`, `G/H` | structural (`W`, `G/H` simple), plus (i) and (ii) certified at one exact picture |

- **JJ at `G`** is the equality `ℓ₀(G) = 3 + def₂(G)`. It is Jackson–Jordán's theorem in
  characteristic 0, and (MC-33) beyond. The driver does not cite it: it **exhibits** one admissible
  `q` with `dim L(q) = 3 + def₂` at every graph where a step needs it. Such a `q` lies in `U`, so on
  the tested graphs no step uses the citation. A class statement built from these steps does.
- **The flag orbit and `dim U`** are read in exact ℚ over the whole fibre `L(q)`, at up to three
  pictures `q` certified in `U(G′)`. "`p_b ∉ π_a`", "`p_a ∉ π_b`" and "`dim U ≥ d`" are open
  conditions on the irreducible `B(G′)`. So what one certified `q` shows holds at `X₀(G′)`'s generic
  point, and conditions shown at different `q` combine. `dim U ≥ 2` also excludes orbits (iii) and
  (iv). This is the coordinator's "read at an attaining draw", in fibre form: attainment of `G′` is
  not needed for it; the induction supplies that separately.
- **Orbit (iv)** is recognised by `δ₂ := def₂(G′) − def₂(G′/ab) = 0`, that is, `a` and `b` lie in a
  common `def₂`-rigid subgraph ((MC-13)(b)'s argument, which does not use `a ∼ b`). That gives
  `U = 0` modulo JJ.
- **(MC-44)** is not a step. Where `a ≁ b`, it supplies `(R_k)` from the chord gadget and so
  removes (MC-24)'s dominance requirement for `(R₁)`, `(R₂)`. (MC-46) and (MC-49) use it; the table
  records their conditions as landed.

> **(MC-52)** `[PROVED]` *(a cut vertex; the hybrid recon's "Aff-gauge fibre product", re-derived)*
> Let `G = G₁ ∪ G₂` with `V(G₁) ∩ V(G₂) = {v}` and disjoint edge sets, where `G₁` and `G₂` satisfy
> (H). Then:
> **(i)** `def₂` and `def₃` add: `def(G) = def(G₁) + def(G₂)`. Hence `tgt(G) = tgt(G₁) + tgt(G₂)`.
> **(ii)** At every configuration with adjacent points distinct, over any field,
> `rank R_G = rank R_{G₁} + rank R_{G₂}`.
> **(iii)** At every `q` admissible for `G₁` and `G₂`, `L_G(q)` is the set of pairs
> `(z¹, z²) ∈ L_{G₁} × L_{G₂}` whose planes at `v` coincide. So
> `dim L_G(q) = dim L_{G₁} + dim L_{G₂} − 3`, and both restriction maps `L_G(q) → L_{Gᵢ}` are onto.
> **(iv)** `X₀(G)` attains **iff** `X₀(G₁)` and `X₀(G₂)` attain.

*Proof.* Write `val(𝒫) = D(|𝒫| − 1) − (D − 1)d(𝒫)`, with `D = 3` for `def₂` and `D = 6` for `def₃`.
- (i) Restrict a partition `𝒫` of `V` to `𝒫ᵢ` on `V(Gᵢ)`. Every edge lies in one `Gᵢ`, and it
  crosses `𝒫` iff it crosses `𝒫ᵢ`, so `d(𝒫) = d(𝒫₁) + d(𝒫₂)`. A part meeting both sides is counted
  twice, and `v`'s part does, so `|𝒫| − 1 ≤ (|𝒫₁| − 1) + (|𝒫₂| − 1)`. Hence
  `val(𝒫) ≤ val(𝒫₁) + val(𝒫₂)`. Conversely, two partitions glued along `v`'s parts give equality.
- (ii) A motion of `G` is a pair of motions of `G₁` and `G₂` that agree at `v`. Evaluation at `v`
  maps each motion space onto `K⁶` (constant motions), so `dim M_G = dim M_{G₁} + dim M_{G₂} − 6`.
  Then use `rank R = 6|V| − dim M` and `|V| = |V₁| + |V₂| − 1`. Nothing divides.
- (iii) Only `v`'s condition changes. `N_G[v] = N₁[v] ∪ N₂[v]`, and each `Nᵢ[v]` has at least 3
  non-collinear points. So `z|N_G[v]` is affine iff the two interpolants `h¹_v`, `h²_v` coincide.
  Given any `z¹ ∈ L_{G₁}` and `z² ∈ L_{G₂}`, put `g := h¹_v − h²_v ∈ Aff`. Then `(z¹, z² + g)` lies in
  `L_G(q)`, since `z²_v + g(q_v) = z¹_v`, and `g` is the only such correction. This gives the
  dimension and ontoness onto `L_{G₁}`, and onto `L_{G₂}` by symmetry.
- (iv) By (iii), the minimum `ℓ₀(G)` is attained where both restrictions of `q` lie in `U(Gᵢ)`.
  There the restriction `B(G) → B(Gᵢ)` is dominant: the planar picture restricts onto an open set,
  and the fibres map onto by (iii). `B(G)` is irreducible, so a nonempty open set of its points maps
  into both of the open sets where `G₁` and `G₂` have their generic ranks. There (ii) and (i) give
  `rank R_G = tgt(G)` iff both pieces attain, since each rank is at most its target. ∎

> **(MC-53)** `[PROVED]` *(a chain of bridges)* Let `G` be `G₁ ⊔ G₂` plus a path
> `a − x₁ − ⋯ − x_k − b` (`k ≥ 0` new vertices), with `a ∈ V(G₁)`, `b ∈ V(G₂)`, where `G₁` and `G₂`
> satisfy (H). Then:
> **(i)** `def(G) = def(G₁) + def(G₂) + (k + 1)`, for `def₂` and for `def₃`. So
> `tgt(G) = tgt(G₁) + tgt(G₂) + 5(k + 1)`.
> **(ii)** At every configuration with adjacent points distinct, over any field,
> `rank R_G = rank R_{G₁} + rank R_{G₂} + 5(k + 1)`.
> **(iii)** At every `q` admissible for `G`, `G₁` and `G₂`,
> `dim L_G(q) = dim L_{G₁} + dim L_{G₂} + c_k`, with `c₀ = −2`, `c₁ = −1`, and `c_k = k − 2` for
> `k ≥ 2`. Both restriction maps are onto.
> **(iv)** `X₀(G)` attains **iff** `X₀(G₁)` and `X₀(G₂)` attain.

*Proof.*
- (i) Take one bridge first, with sides `A` and `B`. For a partition `𝒫`, let `s` be the number of
  parts that meet both sides.
  - If `s ≥ 1`, then `val(𝒫) ≤ val(𝒫_A) + val(𝒫_B) − D(s − 1)`.
  - If `s = 0`, the bridge crosses, and `val(𝒫) = val(𝒫_A) + val(𝒫_B) + D − (D − 1)`.

  So one bridge adds exactly 1. Apply this along the path; each `xᵢ` is a one-vertex side with
  `def = 0`.
- (ii) Choose a motion of `G₁`. Then `X_{x_{i+1}} = X_{x_i} + tᵢ C_i` with `k + 1` free scalars, and
  the last step reaches `b`. The motions of `G₂` with `X_b` prescribed form an affine space of
  dimension `dim M_{G₂} − 6`. So `dim M_G = dim M_{G₁} + dim M_{G₂} + (k + 1) − 6`.
- (iii) The path's vertices have degree 2, so they impose nothing. `a` adds
  `z_{x₁} = h_a(q_{x₁})`, and `b` adds `z_{x_k} = h_b(q_{x_k})`; for `k = 0`, read `x₁ = b` and
  `x_k = a`. Shifting `z²` by `g ∈ Aff` shifts `h_b` by `g`.
  - `k ≥ 2`: the two conditions fix `z_{x₁}` and `z_{x_k}`, and the `k − 2` middle heights are free.
  - `k = 1`: `h_a(q_x) = h_b(q_x)`. This is one condition, met by `g` with `g(q_x)` prescribed.
  - `k = 0`: `z_b = h_a(q_b)` and `z_a = h_b(q_a)`. These are two conditions, met by `g` with
    `g(q_a)` and `g(q_b)` prescribed. That is possible because `q_a ≠ q_b`.

  In each case a suitable `g` exists for every pair `(z¹, z²)`, so both restrictions are onto.
- (iv) As in (MC-52)(iv). ∎

> **(MC-54)** `[PROVED]` *(the short open ear at `δ = 0`: no antecedent, no orbit condition, no
> Jackson–Jordán)* Let `G = G′ + ear_k` be an open ear with `1 ≤ k ≤ 4`, `G′` satisfying (H), and
> `δ = def₃(G′) − def₃(G′/ab) = 0`. For `k = 1` suppose also that `dim U ≥ 2` at `X₀(G′)`'s generic
> point. If `X₀(G′)` attains, then `X₀(G)` attains.

*Proof.* Where `G′` attains, `r ≤ δ = 0` (MC-16). So `ρ = 0`, and (MC-22)'s `(R_k)` and `(P_k)`
hold with nothing to check. (MC-22) needs two more things:
- dominance: (MC-18)(a) for `k ≥ 2`; for `k = 1`, (MC-18)(b) with `dim U ≥ 2`;
- `λ = k + 1`: (MC-19)(b) for `k ≥ 2`, in every orbit. For `k = 1`, `dim U ≥ 2` excludes orbit
  (iii), where `U ⊆ p̂_a^⊥ ∩ p̂_b^⊥ = Kℓ_ab`.

Directly, (MC-16) gives `dim M_G = dim M_{G′} = 6 + def₃(G′)`, and `def₃(G) = def₃(G′)` by
(MC-17). ∎

What this does to (MC-51)'s open cells:
- (a) (`k = 2`, `dim U = 1`, orbits (i)–(iii), including `a ∼ b`) is closed wherever `δ = 0`.
- (b) (`k = 2`, orbit (iv)) is closed wherever `δ = 0`, **without** Jackson–Jordán.
  - (MC-47)(i) needs JJ only to get from `U = 0` to `r = 0`. The step itself needs only `r = 0`,
    and `δ = 0` gives that.
  - `δ = 0` is combinatorial. It holds whenever `δ₂ = 0`, since a common `def₂`-rigid subgraph is
    `def₃`-rigid, and merging it into a maximizing partition gives `def₃(G′/ab) = def₃(G′)`. The
    driver asserts this at every `δ₂ = 0` pair it meets.
- (c) (`k = 1`, `δ ≤ 4`) is closed at `δ = 0` when `dim U ≥ 2`.

(MC-45)'s proof already notes that "at `r = 0` there is nothing to prove". (MC-54) makes that
remark a step, keyed to the combinatorial `δ`. `earante.py --exh 6` finds `r = 0` at all 354 of its
non-adjacent pairs, so on small graphs this is the typical case.

> **(MC-55)** `[PROVED]` *(the induction stays inside (H))*
> **(i)** Every graph a step consumes satisfies (H) and has fewer vertices. In particular, the
> induction never meets a leaf or a disconnected graph.
> **(ii)** Let `G` satisfy (H) and be neither a cycle nor 2-connected. Then CUT or BRIDGE applies,
> with pieces satisfying (H).
> **(iii)** A 3-edge-connected `G` has `def₂(G) = def₃(G) = 0`, so FLAT applies modulo JJ at `G`.
> Hence `def₂ > def₃` forces a 2-edge-cut. So does being 2-connected and uncovered, modulo JJ.
> **(iv)** *(the leaf lemma; not used)* Let `v` be a leaf of `G` whose neighbour `u` has degree
> `≥ 3`, and drop `v`'s own non-collinearity condition from admissibility (`N[v]` has two points).
> Then `L_G(q) ≅ L_{G−v}(q)` by `z_v = h_u(q_v)`, `rank R_G = rank R_{G−v} + 5`, and
> `def(G) = def(G − v) + 1`. So `X₀(G)` attains iff `X₀(G − v)` does.

*Proof.*
- (i) For CUT and BRIDGE, the pieces are as in (ii).
  - EAR requires `G′` to satisfy (H). A closed ear at a hub of degree 3 is therefore excluded; the
    hub's third edge is then a bridge, and BRIDGE applies instead. An open ear's ends are hubs, so
    they keep degree `≥ 2`. The gadgets add a path to `G′`.
  - SPLITOFF: `a ≁ b`, and `a`, `b` keep their degrees.
  - CONTRACT: a rigid `H` has minimum degree `≥ 2` and is connected (Step MC12, notation). `G/H`
    is simple by hypothesis, and `v*` has degree `|δ(W)| ≥ 2` because `G` is 2EC.
  - Sizes: `G′ + ear_{k−1}` and `G″` have `|V| − 1` vertices, and `G/H` has
    `|V| − |W| + 1 ≤ |V| − 2`.
- (ii) `G` has a hub. Suppose it has a bridge. The bridge lies on a maximal chain `P` between hubs
  `h₁ ≠ h₂` (a closed chain lies on a cycle). Removing one edge of `P` disconnects `G` iff `h₁` and
  `h₂` are disconnected in `G − int(P)`, so every edge of `P` is a bridge. `G − int(P)` has two
  components, and each `hᵢ` loses one edge and keeps degree `≥ 2`. If `G` has no bridge but a cut
  vertex `v`, then every component `C` of `G − v` sends `≥ 2` edges to `v`. So `G[C ∪ v]` and
  `G − C` satisfy (H).
- (iii) Take a partition with `p ≥ 2` parts. Each part has `≥ 3` crossing edges, so `2d ≥ 3p` and
  `3(p − 1) − 2d ≤ −3`. Hence `def₂ = 0`, and `def₃ ≤ def₂` (MC-5)(i). *Repair (second reading):*
  this covers "`def₂ > def₃` forces a 2-edge-cut" only for 2EC `G`. If `G` has a bridge, the
  one-bridge lemma of (MC-53)(i), valid for any graph and both `D`, makes `def₂` and `def₃` each the
  sum over the 2-edge-connected components plus the number of bridges. So some component has
  `def₂ > def₃`, is not 3EC, and has a minimal 2-edge-cut, which is one of `G`.
- (iv) `u`'s plane is fixed by `N_{G−v}[u]`, which has `≥ 3` non-collinear points, and it fixes
  `z_v`. Rank and counts are (MC-53)'s one-bridge computations, with `{v}` as one side. ∎

**How the induction treats graphs that fail (H): they never arise**, by (i). For every step it
takes, the driver asserts that each consumed graph is smaller and satisfies (H). The recon's leaf
lemma is (iv), recorded but unused.

> **(MC-56)** `[PROVED]` *(covered graphs attain)* If `G` is covered, then `X₀(G)` attains.

*Proof.* Strong induction on `|V|`. Each step is a proved implication from its consumed graphs. Each
certificate a step uses is exact:
- JJ at a graph: `dim L(q) = 3 + def₂` in exact ℚ, which puts `q` in `U`;
- the flag orbit and `dim U`: exact ℚ at such a `q`;
- (MC-39)'s (i) and (ii): as `coreshrink.py` certifies them, exact ℚ at certified pictures. ∎

A covered graph is therefore proved to attain to exactly the standard of the steps it uses. The
exception is the orbit-(iv) cell (MC-47)(i), which is modulo JJ; it is reported apart and is never
needed below. The 2026-09-24 second reading confirmed (MC-37)–(MC-39), (MC-52)–(MC-55) and the
`a ≁ b` reading of (MC-19)(b), (MC-22), (MC-24), (MC-25); Step MC10's `k ≥ 4` claims have not had
an independent re-derivation beyond that reading. On `≤ 8` vertices, and in every census population, attainment is already certified graph by
graph (MC-7). What the coverage adds there is the **reach of a proof strategy**.

> **(MC-57)** `[MEASURED]` *(`x0arms.py --exh 8`; exhaustive: every simple 2EC graph on ≤ 8
> vertices, 7 980)* **The default steps cover all 7 980, and so do the default steps plus Step MC13's cells.**
> By first covering step:
>
> | | BASE | THETA | CUT | EAR `k = 4` | EAR `k = 3` (MC-45) | FLAT | EAR `δ = 0`, `k = 2, 3` | EAR `δ = 0`, `k = 1` | CONTRACT | uncovered |
> |---|---|---|---|---|---|---|---|---|---|---|
> | `--ear23 none` | 6 | 16 | 319 | 4 | — | 7 568 | 58 | 7 | 2 | 0 |
> | `--ear23 antecedent` | 6 | 16 | 319 | 4 | 40 | 7 568 | 18 | 7 | 2 | 0 |
>
> - The 134 graphs with `def₂ > def₃` are the non-FLAT entries: BASE 5, THETA 13, CUT 45, and every
>   entry to the right of CUT except FLAT.
> - (MC-46) (`k = 2`) never fires here. All 31 of its orbit-(i)–(iii) cells have `dim U = 1` at the
>   certified pictures (14 in (i), 5 in (ii), 12 in (iii)). The remaining 419 show `U = 0`.
>   (MC-47)(i) is never the first covering step.
> - JJ is exhibited at all 7 568 FLAT graphs. Both CONTRACT runs have a `def₂`-rigid core. No graph
>   is without an applicable step.
>
> **Without (MC-54)** (`--delta0 off`, i.e. only landed ear steps):
> - `--ear23 none`: CONTRACT takes 66, and 1 graph is uncovered.
> - `--ear23 antecedent`: EAR `k = 3` takes 40, CONTRACT 26, and the same 1 graph is uncovered.
>
> That graph is `x8_60101824`: the 8-cycle `4 0 5 2 7 3 6 1` with the two antipodal chords `4–7` and
> `5–6`, i.e. `K₄` with the four edges of a 4-cycle subdivided once.
> - It has `def₂ = 1`, `def₃ = 0` and four 2-edge-cuts.
> - **Stuck cell:** all four of its ears are `k = 1`, in (MC-51)(c), at `δ = 0`, orbit (i),
>   `dim U = 2`. (MC-54) closes each, consuming `G′ = θ(2, 3, 3)`.
> - CONTRACT cannot reach it. Every `W` with `G/H` simple is a 5-cycle, with `def₂ = 2 > 1`, so (i)
>   fails (MC-59)(a). (MC-39)'s last sentence (the core rigid at a point of `B(G)`, in place of (i))
>   does cover it (`--contract cert-core`), but with a rank certificate.
> - Of the 76 CONTRACT runs in the `--delta0 off` table, the 10 that failed all have
>   `def₂(H) > def₂(G)`.
>
> **Without CONTRACT** (`--contract off`), uncovered:
>
> | | `--delta0 on` | `--delta0 off` |
> |---|---|---|
> | `--ear23 none` | 2 | 67 |
> | `--ear23 antecedent` | 2 | 27 |
>
> The 27 with only the landed ear cells are stuck in (MC-51)(a) and (c). (MC-54) closes 25 of them at
> `δ = 0`. The 2 that need CONTRACT in any case are:
> - `x8_93131968`: `k = 1` at `δ = 2`, orbit (i), `dim U = 2`, which is (MC-51)(c); and `k = 1` with
>   `a ∼ b`;
> - `x8_218769729`: `k = 2` at `δ = 1`, orbit (i), `dim U = 1`, which is (MC-51)(a); and `k = 1` with
>   `a ∼ b`.

**The hybrid recon's count, re-done.** Its classifier left 48 graphs on `≤ 8` vertices with no
applicable arm (its "REST"). Its step set had no contraction and no θ-class, and its own ear rule
excluded chains with adjacent ends at `k ≤ 4`. Under the steps above (`x0arms.py --round1`):

| | THETA | EAR `k = 4` | EAR `k = 3` | EAR `δ = 0` | CONTRACT | uncovered |
|---|---|---|---|---|---|---|
| default | 6 | 3 | — | 37 | 2 | 0 |
| `--ear23 antecedent` | 6 | 3 | 26 | 11 | 2 | 0 |
| `--delta0 off` | 6 | 3 | — | — | 38 | 1 |
| `--delta0 off --contract off` | 6 | 3 | — | — | — | 39 |

- **The 3 EAR `k = 4` covers are all at chains with adjacent ends.** As landed, (MC-19)(b) holds for
  any flag pair, (MC-22), (MC-24) and (MC-25) carry no `a ≁ b` hypothesis, and (MC-25) is stated in
  all four orbits. (MC-51)'s closing paragraph says the same for `k ≥ 3` with `a ∼ b`. The recon's
  exclusion came from its own ear theorem, which went through `pencilLoss_vertexTwoCut`.
  *Confirmed by the 2026-09-24 second reading:* `a ∼ b` puts the generic flags in orbit (iii) or
  (iv), and each of the four claims covers all four orbits. `w4/earspan.py`, which shares no code
  with `earstep.py`, re-certifies `λ = 3, 4, 5` at `k = 2, 3, 4` and `⋂Λ₄ = 0` in every orbit.
- **The recon's "REST is reached from 887/888 habitat members"** counted a recursion that followed
  **only the first applicable arm** at each graph. So "reached" there did not mean "uncovered". The
  landed figure is (MC-58).
- **The recon's "REST is infinite"** (the `K₄` necklaces) was true of its own step set. CONTRACT
  supersedes it (MC-60).
- **The recon's predicted first failure**, `K₄` with every edge subdivided once, is covered. (MC-54)
  closes it with `k = 1` at `δ = 0`, consuming `θ(2, 4, 4)` (`--tree x10_3584739737600`).

> **(MC-58)** `[MEASURED]` *(`x0arms.py --pool`; the census populations; counts of labelled members)*
>
> | population | members | `--ear23 none` | `--ear23 antecedent` |
> |---|---|---|---|
> | `battery` | 9 | 9 (BASE 3, THETA 3, EAR `k = 4` 1, FLAT 2) | 9 |
> | `thetas` | 109 | 109 (THETA) | 109 |
> | `smark` | 78 | 63 (BASE 15, THETA 18, EAR `k ≥ 5` 3, `k = 4` 22, SPLITOFF 3, `δ = 0` 1, CONTRACT 1) | 78 (… EAR `k = 4` 19, `k = 3` 14, `k = 2` 9) |
> | `habitats` | 888 | 511 (THETA 1, EAR `k = 4` 510) | 888 (THETA 1, EAR `k = 4` 480, `k = 3` 353, `k = 2` 54) |
> | `peels` | 928 | 928 (EAR `k ≥ 5` 320, `k = 4` 304, `δ = 0` 304) | 928 (… EAR `k = 3` 268, `k = 2` 36) |
> | `residuals` | 260 | 208 (EAR `k ≥ 5` 144, `k = 4` 63, CONTRACT 1) | 260 (… EAR `k = 3` 1, `k = 2` 52) |
>
> - With `--delta0 off` the `antecedent` column is unchanged (888, 78, 928, 260).
> - A **terminal** graph is one where no step applies, or where every applicable step fails only a
>   certificate. It is reached from an uncovered member through consumed graphs that are themselves
>   uncovered.
> - Under `--ear23 none`, the uncovered members reach 25 terminal graphs (habitats), 63 (smark) and 1
>   (residuals). Every one has the same profile (the driver's `by structure` line): no applicable
>   step, no proper rigid set, every maximal chain with `k ≤ 3`, `def₃ = 0 < def₂`, and `δ ≤ 4` at
>   every degree-2 vertex.
> - **Stuck cells**, read at the listed terminal graphs: every `k = 2` chain is (MC-46)'s cell
>   (orbit (i), `dim U = 3`); every `k = 3` chain is (MC-45)'s; every `k = 1` chain is (MC-51)(c) at
>   `δ = 2` or `4`. So they are stuck exactly at Step MC13's cells, and `--ear23 antecedent` covers
>   every member.

**So, on everything tested, Step MC13's landed cells together with (MC-54) leave nothing
uncovered** — a measurement on finite populations, not a coverage theorem ((MC-61)). Without (MC-54), exactly one graph is left, and it sits in (MC-51)(c) at `δ = 0`.

> **(MC-59)** *(what hypothesis (i) of (MC-39) can and cannot do, and the flat core)* Let `W` be a
> proper rigid set with `G/H` simple, and let `q ∈ U(G)` with `q|_W ∈ U(H)`.
> **(a)** `[PROVED]` If (i) holds at `q`, then `ℓ₀(H) ≤ ℓ₀(G)`. At certified pictures this reads
> `def₂(H) ≤ def₂(G)`.
> **(b)** `[PROVED]` If `def₂(H) = 0` and `dim L_H(q|_W) = 3`, then (i) holds at `q`.
> **(c)** *(the flat core, `def₂(H) = 0`; three parts since the 2026-09-24 second reading)*
> **(c1)** `[PROVED]` *(no citation)* If `def₂(H) = 0`, then `def₂(G/H) = def₂(G)`.
> **(c2)** `[PROVED]` *(no citation)* At any picture of `coreshrink.py`'s construction with `δ`
> admissible for `H`, `q′` admissible for `G/H` and `dim L_H(δ) = 3`:
> `ker M₀ ≅ L⁰_{G/H}(q′) ⊕ K`, so `dim ker M₀ = dim L_{G/H}(q′)`.
> **(c3)** `[PROVED-MOD]` *((MC-33): Jackson–Jordán at `H` and at `G/H` only; sharpened by the
> 2026-09-24 second reading, which dropped `G`)* If `def₂(H) = 0`, then (ii) holds at a generic
> picture, **and `ℓ₀(G) = 3 + def₂(G)` follows**: Jackson–Jordán at `G` is a consequence, not a
> hypothesis.
> **(d)** `[PROVED-MOD]` *((MC-33): Jackson–Jordán at `H` and `G/H`)* Consequently, **at a
> `def₂`-rigid core, (MC-39) needs no per-graph certificate**. If `X₀(G/H)` attains, then `X₀(G)` attains, because `X₀(H)` attains by
> FLAT.

*Proof.*
- (a) `proj_W L_G(q) ⊆ L_H(q|_W)` always ((MC-38)'s proof), and its dimension is at most
  `dim L_G(q) = ℓ₀(G)`.
- (b) `Aff(q) ⊆ L_G(q)` projects onto `Aff(q|_W)`. That space is 3-dimensional because `q|_W` is
  not collinear, and it equals `L_H(q|_W)`, which has dimension 3.
- (c1) Merge the parts meeting `W` in a `def₂`-maximizing partition. This is (MC-35)'s proof with
  `(3, 2)` for `(6, 5)`.
- (c2) Read off the five row types of `M₀` (listed after (MC-37)'s proof).
  - The core rows say that `ζ` lies in `L_H(δ)`, with the core plane slopes `a_c`. When
    `dim L_H(δ) = 3`, that space is `Aff(δ)`: `ζ = a*·δ + γ`, every `a_c = a*`, and every
    `γ̃_c = γ`.
  - The rows "`π_c(0)` contains `A_c`" then say that every attachment lies on the plane
    `z = a*·(x, y)` through `P`. That is exactly `G/H`'s condition at `v*`, with `v*` at height 0.
  - The attachment rows say that each `π_u` passes through `P`. That is `G/H`'s condition at `u`,
    since `v* ∈ N_{G/H}[u]`. Each attachment's `γ̃_u` appears in one row only (`G/H` is simple), and
    that row fixes it.
  - The far rows are unchanged.

  So the outside data range over `L⁰_{G/H}(q′)`, the slope `a*` is fixed by them (`N_{G/H}[v*]` is
  not collinear), and `γ` is free. Given `(z_O, γ)`, every other unknown is determined.
  `dim L⁰ = dim L_{G/H}(q′) − 1`, since the constants have `z_{v*} ≠ 0`.
- (c3) Take a generic picture: `dim L_H(δ) = ℓ₀(H) = 3` (JJ at `H`), `q′ ∈ U(G/H)` (the translation
  argument after (MC-37)'s proof), and `q(t) ∈ U(G)` for cofinitely many `t`. Then
  `ℓ₀(G) = dim W₀ ≤ dim ker M₀ = ℓ₀(G/H)`, by `W₀ ⊆ ker M₀` and (c2), with no citation. And
  `ℓ₀(G/H) = 3 + def₂(G/H) = 3 + def₂(G) ≤ ℓ₀(G)`, by JJ at `G/H`, (c1) and the elementary
  (MC-4)(b) at `G`. So every inequality is an equality: `dim ker M₀ = ℓ₀(G)`, which is (ii), and
  `ℓ₀(G) = 3 + def₂(G)`. JJ at `G` alone would not do: it bounds `ℓ₀(G/H)` from the same side as
  the degeneration does. The hard direction is needed at `G/H`.
- (d) (b) gives (i), and (c3) gives (ii). FLAT at `H` (`def₂ = def₃ = 0`) gives `X₀(H)`. JJ at `H`
  is used three times: for (b) at a generic picture, for (c2) at a generic `δ`, and for FLAT at `H`. ∎

`[MEASURED x0arms.py --flatcore 8]` The kernel identity of (c2) is asserted exactly at 2 080
pictures. That is one per graph: the largest `def₂`-rigid `W` with `G/H` simple. The graphs are
every simple 2EC graph on `≤ 8` vertices that has such a `W`, plus `N(3..6)`: 2 083 graphs, 3 skipped
because the drawn `δ` was not in `U(H)`. Also asserted at all 2 080: the count
`def₂(G) = def₂(G/H)`, and no jump. JJ was exhibited at both `G` and `G/H` in every case.

> **(MC-60)** *(the `K₄` necklaces)* `N(k)` is `k` copies of `K₄` in a cycle, with bead `i`'s vertex
> 1 joined to bead `i + 1`'s vertex 0. It has minimum degree 3 and 2-edge-cuts, and
> `def₂ = k − 3`, `def₃ = max(0, k − 6)` (asserted).
> **(a)** `[CONSTRUCTED]` *(`x0arms.py --necklace 8`)* For `k = 3..8`, `N(k)` is covered: `N(3)` by
> FLAT, and `N(4..8)` by CONTRACT, with (i) and (ii) certified at every bead. `X₀(N(k))` attains at
> each: `maincomp.census` gives ranks 66/66, 90/90, 114/114, 138/138, 161/161 and 184/184.
> **(b)** `[PROVED]` *(no citation since the 2026-09-24 second reading, via (MC-59)(c3); first
> written modulo Jackson–Jordán)* **Every `N(k)`, `k ≥ 3`, attains on `X₀`.**

*Proof of (b).* Call a *unit cycle* a cycle of `j ≥ 3` units, each a `K₄` bead or a single vertex,
with consecutive units joined by one edge and a bead's two outside edges at distinct bead vertices.
- A unit cycle is 2EC and satisfies (H).
- A bead `W` in it is a proper `def₂`-rigid set.
- `G/H` is simple: the bead's two outside neighbours lie in the two adjacent units, which are
  distinct since `j ≥ 3`.
- `G/H` is again a unit cycle, with one fewer bead.

Induct on the number of beads, with the **strengthened motive** "`X₀(Γ)` attains **and**
`ℓ₀(Γ) = 3 + def₂(Γ)`" (the second reader's device).
- *Base.* `C_j` has no hubs, so `L = K^V` and `ℓ₀ = j = 3 + def₂(C_j)`; `X₀` attains by (MC-21)(a).
- *Step.* `L_{K₄}(q) = Aff(q)` at every admissible `q`, since every `N[v]` is all of `V(K₄)`. So JJ at
  the bead holds outright, and so does FLAT there (flat rank `24 − 6 = 18`). The induction
  hypothesis at the smaller unit cycle `G/H` gives both halves of the motive there. Then (MC-59)(b)
  gives (i), (MC-59)(c3) gives (ii) **and** `ℓ₀(G) = 3 + def₂(G)`, and (MC-39) gives attainment.

After `k` contractions we reach `C_k`. No step cites Jackson–Jordán. ∎

It is the corpus's first infinite family of minimum degree 3 shown to attain on `X₀`, to the
standard of (MC-19)(a)'s certificates, (MC-39) and (MC-59)(b), (c1)–(c3).

*Remark (the second reader's, not itself second-read): the equality `ℓ₀ = 3 + def₂` propagates.*
`[INFORMAL]` *(gap: SPLITOFF not checked; no second reader)* It passes from the consumed graphs to
`G` through CUT and BRIDGE ((MC-52)(iii), (MC-53)(iii) with the matching deficiency sums), EAR with
`k ≥ 2` (`ℓ₀` and `def₂` both rise by `k − 2`), EAR with `k = 1` and `U ≠ 0` (both fall by one,
since (MC-4)(b) at `G` forces `δ₂ ≥ 1`), and CONTRACT at a `def₂`-rigid core ((MC-59)(c3)). So under
the strengthened motive of (MC-60)(b)'s proof the citation is consumed only at FLAT (where `G`
itself is not consumed), at (MC-47)(i), and wherever SPLITOFF fails to propagate. FLAT covers most
small graphs (7 568 of 7 980 in (MC-57)), so this does not remove the citation from the strategy.
It says where a proof of Jackson–Jordán by the same induction would have to do its work. The hybrid recon's "REST is infinite" was an artifact
of a step set with no contraction.

> **(MC-61)** `[OPEN]` *(the coverage theorem — not proved)* **Coverage is measured, not proved.**
> (MC-57) is exhaustive only on ≤ 8 vertices, and those graphs were already certified to attain
> directly (MC-7). (MC-58) is sampled populations. The one infinite family proved is the `K₄`
> necklaces (MC-60), with no citation. By (MC-56), a theorem that **every** simple 2EC graph
> satisfying (H) is covered would prove (MC-10)(a) by this strategy. So the coverage theorem is the
> whole remaining problem here, not a side item. It has two halves, both open:
> - **The structural half:** that every such graph admits some step (a cut vertex, a bridge
>   chain, a usable ear, a split-off at `δ ≥ 5`, `def₂ = def₃`, or a proper rigid `W` with `G/H`
>   simple). There is no theorem. The candidate gaps are graphs with a proper rigid set but none with
>   a simple quotient (Katoh–Tanigawa's Lemma 6.5 case) and 2-edge-cut graphs with no degree-2 chain.
>   (MC-55)(iii) shows only that `def₂ > def₃` forces a 2-edge-cut.
> - **The certificate half:** that each step's per-graph conditions hold in general, where the
>   driver checks them at one exact picture per graph:
>   - Jackson–Jordán's equality, wherever FLAT or SPLITOFF is used, and at `H` and `G/H` where
>     (MC-59)(d) is used;
>   - `dim U ≥ 2` (and the orbit) for (MC-46), and for (MC-54) at `k = 1`;
>   - (MC-39)'s (i) and (ii) at a core with `def₂(H) > 0` ((MC-41)'s (∂1), (∂2)); (MC-59) settles
>     the `def₂`-rigid case modulo Jackson–Jordán, and (MC-59)(a) shows (i) impossible when
>     `def₂(H) > def₂(G)`;
>   - and the ear cells that are not steps at all: (MC-51)(a) and (c) at `δ ≥ 1`, and (b) where
>     Jackson–Jordán is not assumed.
>
> What was tested: with the default steps and `--ear23 antecedent`, nothing is uncovered — 7 980 /
> 7 980 on `≤ 8` vertices and every member of every population. Without (MC-54), one graph
> (`x8_60101824`) is uncovered, stuck in (MC-51)(c) at `δ = 0`; with `--ear23 none`, the uncovered pool
> members are stuck at (MC-45)/(MC-46), which have landed. The 2 graphs of (MC-57) that need
> CONTRACT are the tested instances of (MC-51)(a)/(c) at `δ ≥ 1`. The stop rule (more than 3
> structurally distinct failures, or a graph with no candidate step) does not fire on the tested
> populations. The deferred adversarial census (`n = 9–14`) is the natural test of the structural half.

**What would change this.**
- A consumed graph that is not smaller, or that fails (H). The driver asserts both.
- A covered graph where `X₀` falls short. A `maincomp.py` SHORT at a covered member would refute
  the step it used.
- A glued instance failing an (MC-52) or (MC-53) identity (`--lemmas` asserts them).
- A pair with `δ₂ = 0` and `δ > 0` (asserted never to occur).
- A `def₂`-rigid core where `dim ker M₀ ≠ dim L_{G/H}(q′)`, or where (ii) fails with JJ exhibited at
  `G` and `G/H` (`--flatcore` asserts both).
- A structural class of uncovered graphs in a larger population. The adversarial census of P1's
  first hand-off (`n = 9–14`) is the natural place to look.

**Driver** (all at `PYTHONHASHSEED=0`, seed `20260924`; certificates in exact ℚ, ranks mod
`2⁶¹ − 1` only as certificates; sampler support in the docstring; re-runs byte-identical apart from
the timing lines, checked on `--exh 7` and `--pool habitats`):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/x0arms.py --lemmas` | cut vertex 21/21, bridge path (`k = 0..3`) 84/84, leaf 6/6 glued instances; every identity asserted | 4 s |
| `python3 notes/scripts/w4/x0arms.py --exh 7` | 577/577 covered | 2 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8` / `--ear23 antecedent` | 7 980/7 980 covered ((MC-57)'s table) | 17 s / 20 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --delta0 off` / `--ear23 antecedent --delta0 off` | 1 uncovered, `x8_60101824`, in (MC-51)(c) at `δ = 0` | 24 s / 23 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --contract off` (with `--ear23 antecedent`, `--delta0 off`) | 2 / 2 / 67 / 27 uncovered, each with its cells | 17–20 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --contract cert-core --delta0 off` | CONTRACT 66, CONTRACT* 1 (`x8_60101824`), 0 uncovered | 27 s |
| `python3 notes/scripts/w4/x0arms.py --round1` (and `--ear23 antecedent`, `--delta0 off`, `--delta0 off --contract off`) | the recon's 48: 0 / 0 / 1 / 39 uncovered | ≤ 6 s |
| `python3 notes/scripts/w4/x0arms.py --pool habitats` (and `--ear23 antecedent`, each with `--delta0 off`) | 511 / 888; 25 terminal graphs under `none` | 3–9 s |
| `python3 notes/scripts/w4/x0arms.py --pool battery,thetas,smark` (and `--ear23 antecedent [--delta0 off]`) | 9, 109, 63 / 9, 109, 78 | 9 s / 2 s / 6 s |
| `python3 notes/scripts/w4/x0arms.py --pool peels,residuals` (and `--ear23 antecedent [--delta0 off]`) | 928, 208 / 928, 260 | 51 s / 56 s / 142 s |
| `python3 notes/scripts/w4/x0arms.py --necklace 8` (and `--ear23 antecedent`) | `N(3..8)` covered, `X₀` attains at each | 18 s / 15 s |
| `python3 notes/scripts/w4/x0arms.py --flatcore 8` | the kernel identity at 2 080 / 2 080; no jump at 2 080 / 2 080 | 171 s |
| `python3 notes/scripts/w4/x0arms.py --tree x8_60101824,x10_3584739737600` (and `x8_60101824 --ear23 antecedent --delta0 off`) | both (MC-54) → THETA / uncovered, with its cells | < 1 s |

#### Literature, checked 2026-09-24 (a read-only agent over `.refs/` plus the web; bibliographic data from Crossref)

- **Jackson–Jordán**, "Pin-collinear body-and-pin frameworks and the molecular conjecture",
  *Discrete Comput. Geom.* 40(2) (2008) 258–278, doi:10.1007/s00454-008-9100-z. Read in its
  report form, EGRES TR-2006-06 (`.refs/`).
  - Thm 6.1 (TR p.14) and Thm 7.1 (p.21): simple graphs; the generic rank is
    `3|V| − 3 − def(G)`, with `def` exactly our `def₂` (p.7).
  - Thm 7.3: rigidity is equivalent to 2G packing 3 spanning trees.
  - p.21: the rod-and-pin 2-polymatroid **equals** the body-and-pin one, so the formula gives the
    rank of **every edge subset**. That is the form (MC-13)(c) and (MC-14) use, at `G_e` and at
    rigid subgraphs.
  - Setting: `ℝ²`, generic meaning algebraically independent over `ℚ` (TR p.4 for bar-joint, p.12
    for body-and-pin and rod-and-pin), with the genericity placed on the pin-lines, each pin being
    `L_u ∩ L_v`. This is exactly our dual picture: pin-line `L_v` dual to `q_v` (`p(v) = −q_v`),
    pin `ℓ_e`, and motion coordinates changed by `diag(1, −1, 1)`. The rank statement is about
    polynomials over the prime field. **It transfers to characteristic 0.** Beyond that, see
    *Jackson–Jordán beyond ℝ* (MC-33):
    - a second reading finds every step field-free over any infinite field after two small repairs
      and one bypass (`INFORMAL`);
    - `jjchar.py` exhibits the equality in characteristics 2, 3, 101 and 10 007 at all 7 980 simple
      2EC graphs on ≤ 8 vertices.
  - Proof technique: a minimal counterexample. The geometric steps are bar-joint 0-extensions,
    1-extensions and vertex splits on the body-and-pin graph; the combinatorics is the theory of
    bricks and superbricks.
- **The flat correspondence of Step MC4** (`F(q) ≅ L(q)`).
  - Crapo–Whiteley, "Statics of frameworks and motions of panel structures: a projective geometric
    introduction", *Structural Topology* 6 (1982) 43–82. Example 4.4 (pp. 72–73) is the flat
    tetrahedron: motions of the flat panel structure ↔ polyhedra over it, "true in great
    generality, as we shall see in the sequel".
  - Whiteley, "A correspondence between scene analysis and motions of frameworks", *Discrete Appl.
    Math.* 9(3) (1984) 269–295, doi:10.1016/0166-218X(84)90027-1. By its abstract this is the
    general isomorphism between scenes over a picture and motions of a plane framework. **Not read
    in full; read it before citing it for Step MC4.**
  - The scene-analysis count is Whiteley, "A matroid on hypergraphs, with applications in scene
    analysis and geometry", *Discrete Comput. Geom.* 4 (1989) 75–95, doi:10.1007/BF02187716
    (Sugihara's conjecture; Whiteley 1996 §8.3).
- **Katoh–Tanigawa**, "A proof of the molecular conjecture", *Discrete Comput. Geom.* 45 (2011)
  647–700, doi:10.1007/s00454-011-9348-6, checked against the local text (running head and DOI
  line), for Step MC12. The places used are all in §6.2, "G contains a proper rigid subgraph"
  (p. 673): Lemma 6.2 with eq. (6.3), p. 673; Lemma 6.3 with the hinge choice (6.6), p. 674;
  Claim 6.4 with (6.7)–(6.9), p. 675, where `v*` "may be realized as a d-dimensional body";
  Lemma 6.5 with Claim 6.6, p. 676. Also Lemma 3.5 (contraction of a rigid subgraph, p. 658) and
  Lemma 5.1 (column deletion, p. 667).
- **Vertical/horizontal split, (MC-11)(i): not found.** Searched Crapo–Whiteley 1982; the
  nearest is its Prop. 5.1 on cross-sections of panel structures. Also searched Whiteley 1988,
  1996, 1999, 2005, Katoh–Tanigawa 2011 and Jordán 2016.
- **The pencil statement itself: not found**, in any local source or by web search. The hinge
  coplanar and hinge concurrent cases always appear separately. Whiteley 1999 p.25 notes only that
  three coplanar concurrent hinges are dependent. One place could not be checked: Whiteley 1989
  p.93, cited by Jackson–Jordán §8 for "a similar conjecture for 3-dimensional frameworks". The
  download was blocked.
- Also verified, for P3's Edmonds-problem idea: Lovász, "Singular spaces of matrices and their
  application in combinatorics", *Bol. Soc. Brasil. Mat.* 20(1) (1989) 87–99,
  doi:10.1007/BF02585470. Sugihara, *Machine Interpretation of Line Drawings*, MIT Press, 1986.
