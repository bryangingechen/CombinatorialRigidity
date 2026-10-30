# CERT workbook

Proved results of the CERT attack, numbered S1, S2, … and cited by number (`HARNESS.md` *Attack
track*). Appending is right here; a result found wrong is struck through with a pointer to the result
that corrects it. The notation is the brief's (`brief.md` §2–§3).

**Standing notation.** `d ≥ 3`, `V = K^{d+1}`, `D = C(d+1, 2) = dim Λ²V`. Coordinates of `V` are
`(x, y, z¹, …, z^{d−2}, t)`; `λ(v) = t` is the last coordinate, so `v` is *affine* iff `λ(v) = 1`, and
the heights are `z¹, …, z^{d−2}`. `P₀ = (0, …, 0, 1)`, `P_i = e_i + P₀` (`1 ≤ i ≤ d`). A closed `m`-gon
is a tuple `Y = (Y₀, …, Y_{m−1})` of vectors of `V`, indices mod `m`, with joins `J_i = Y_i ∧ Y_{i+1}`;
it is *good* if `m ≥ 3` and `J₀, …, J_{m−1}` are linearly independent in `Λ²V`. `W(Y)` is the span of
its joins and `star(y) = y ∧ V`.

---

## S1 — three consecutive points of a good polygon are independent (session 1, 2026-10-30)

R1 (i) of the brief, over every field.

**Statement.** Let `Y` be a good closed `m`-gon. Then every vertex `Y_i` is nonzero, and for every
`i` the three vectors `Y_{i−1}, Y_i, Y_{i+1}` are linearly independent. In particular consecutive
vertices are not proportional, so affine consecutive vertices differ.

**Proof.** `J_{i−1} = Y_{i−1} ∧ Y_i ≠ 0` (a member of an independent family), so `Y_{i−1}, Y_i` are
independent and both nonzero. If `Y_{i+1} = αY_{i−1} + βY_i`, then
`J_i = Y_i ∧ Y_{i+1} = α Y_i ∧ Y_{i−1} = −α J_{i−1}`, so `J_i + α J_{i−1} = 0`. As `m ≥ 3`, the indices
`i − 1` and `i` differ mod `m`, so this is a nontrivial relation (coefficient 1 on `J_i`) among
members of an independent family: a contradiction. ∎

## S2 — normalizing a good polygon: affine, three consecutive vertices at `P₁, P₀, P₂` (session 1)

R1 (ii) of the brief. Part (a) needs affine input and holds over every field; part (b) is R1 (ii) as
the brief states it, any input, over an infinite field. The route uses (a) only (S6); (b) is checked
because the brief asks for R1's four steps, and it lets any good polygon (R3's KT witness, say) feed S3.

**Statement.** Let `Y` be a good closed `m`-gon and fix an index `i`.
- (a) If every `Y_j` is affine, there is `g ∈ GL(V)` with `λ ∘ g = λ` and `g(Y_{i−1}) = P₁`,
  `g(Y_i) = P₀`, `g(Y_{i+1}) = P₂`. Then `gY` is a good closed `m`-gon of affine points whose
  vertices `i − 1, i, i + 1` are at height zero. Every field.
- (b) If `K` is infinite, there is a good closed `m`-gon `Y′` of affine points with
  `Y′_{i−1} = P₁`, `Y′_i = P₀`, `Y′_{i+1} = P₂`.

**Proof.** First, for every `g ∈ GL(V)` the map `Λ²g` is invertible (inverse `Λ²(g⁻¹)`) and sends
`J_j` to `gY_j ∧ gY_{j+1}`, so `gY` is good; and scaling vertices by nonzero scalars scales each join
by a nonzero scalar, so it keeps a polygon good.

(a) Write `Y_j = (ȳ_j, 1)` with `ȳ_j ∈ K^d`, and `v₁ = ȳ_{i−1} − ȳ_i`, `v₂ = ȳ_{i+1} − ȳ_i`. These are
independent: `αv₁ + βv₂ = 0` makes `αY_{i−1} + βY_{i+1} − (α + β)Y_i` zero (its affine part is
`αv₁ + βv₂`, its last coordinate `α + β − (α + β)`), so `α = β = 0` by S1. As `d ≥ 2`, extend to a
basis `v₁, …, v_d` of `K^d` and let `M ∈ GL_d(K)` send `v_j` to `e_j`. Put
`g(x̄, t) = (M(x̄ − t ȳ_i), t)`: linear, invertible (inverse `(x̄, t) ↦ (M⁻¹x̄ + t ȳ_i, t)`), with
`λ ∘ g = λ`. Then `g(Y_i) = (0, 1) = P₀`, `g(Y_{i−1}) = (Mv₁, 1) = (e₁, 1) = P₁`,
`g(Y_{i+1}) = (e₂, 1) = P₂`; every `gY_j` is affine as `λ(gY_j) = λ(Y_j) = 1`; and `P₀, P₁, P₂` have
all heights zero.

(b) By S1, `Y_{i−1}, Y_i, Y_{i+1}` are independent, as are `P₁, P₀, P₂`; extend both triples to bases
of `V` and let `g ∈ GL(V)` send the first basis to the second. `Z = gY` is good with
`Z_{i−1}, Z_i, Z_{i+1} = P₁, P₀, P₂`. Let `T = {i − 1, i, i + 1}` and treat the coordinates of the
other `m − 3` vertices as indeterminates `X = (X_j)_{j ∉ T}`. The Plücker coordinates of the joins of
the polygon with `Z_j` replaced by `X_j` (`j ∉ T`) are polynomials in `X`, so each `m × m` minor of
the `m × D` matrix of joins is one. Some minor `Δ` is nonzero at `X = (Z_j)`, so `Δ ≠ 0` as a
polynomial; and `Λ = ∏_{j ∉ T} λ(X_j)` is a nonzero polynomial (a product of distinct
indeterminates). `K[X]` is a domain, so `ΔΛ ≠ 0`, and over the infinite `K` it has a non-root `X*`
(the fact the Lean steps cite as `MvPolynomial.exists_eval_ne_zero`). The polygon with `X*_j` at
`j ∉ T` and `P₁, P₀, P₂` on `T` is good (`Δ(X*) ≠ 0`) with every last coordinate nonzero; divide each
vertex by its last coordinate (those on `T` are already affine) to get `Y′`. ∎

## S3 — an open ear from a good closed polygon, with `p_b = p_a` (session 1)

R1 (iii) of the brief, over every field (affine input) or every infinite field (any input).

**Statement.** Let `k ≥ 2` and let `Y` be a good closed `(k + 1)`-gon, of affine points (any field) or
of any vectors (`K` infinite). Then there are affine points `p_a = p_b = P₀`, `p₁ = P₂`, `p_k = P₁`
and `p₂, …, p_{k−1}` whose `k + 1` ear joins `p_a∧p₁, p₁∧p₂, …, p_{k−1}∧p_k, p_k∧p_b` are linearly
independent; joined points differ, and `p_a, p₁, p_k, p_b` are at height zero.

**Proof.** S2 (a) (affine `Y`) or S2 (b) (`K` infinite) at `i = 0` gives a good closed `(k + 1)`-gon
`Y′` of affine points with `Y′_k = P₁`, `Y′₀ = P₀`, `Y′₁ = P₂` (indices mod `k + 1`, so `i − 1 = k`).
Put `p_a = p_b = Y′₀` and `p_j = Y′_j` (`1 ≤ j ≤ k`). The ear's joins are, in order,
`Y′₀∧Y′₁, Y′₁∧Y′₂, …, Y′_{k−1}∧Y′_k, Y′_k∧Y′₀`: exactly the `k + 1` joins of `Y′`, independent.
Joined points differ by S1. `P₀, P₁, P₂` are at height zero. ∎

**Consumer reading** (`Graph.X0Attains.of_openEar_of_cert`, read in `Pᵈ` through
`pencilConfigPointGrade`, which is `(q_v, z_v, 1)`): put bodies `a` and `b` at `P₀` (`q₀ = (0, 0)`),
`x_j` at `p_j`, every other body anywhere, with every height zero on `V₁ ∪ {x₁, x_k}` and off
`V(G)`. The heights `zs` are then zero on every closed neighbourhood of a body of `V₁`, which is what
`hzs`'s discharge `Graph.mem_liftingSpace_of_ear` asks (with `h = 0`, as the `P³` callers do), and the
`n = k + 1` links `e 0, …, e k` (`j = id`) carry the independent joins. `a ≠ b` as bodies at one point
is what `of_openEar` already does at `d = 3` (`a` and `b` both at `certPt 0`).

## S4 — some vertex's star leaves the span of the joins (session 1)

The first half of R1 (iv), over every field.

**Statement.** Let `Y` be a good closed `m`-gon with `m < D`, `W = W(Y)`, `S = span(Y₀, …, Y_{m−1})`.
- If `S = V`, there are vertices `Y_i, Y_j` with `Y_i ∧ Y_j ∉ W`.
- If `S ≠ V`, then for every vertex `Y_i` and every `u ∉ S`, `Y_i ∧ u ∉ W`; a standard basis vector
  `e_c ∉ S` exists.
So in either case some vertex `Y_i` and some `u ∈ {Y₀, …, Y_{m−1}} ∪ {e₁, …, e_{d+1}}` have
`Y_i ∧ u ∉ W`.

**Proof.** `dim W = m` as the joins are independent. If `S = V`, some subset `B` of the vertices is a
basis of `V`, and `{b ∧ b′ : b ≠ b′ ∈ B}` spans `Λ²V`. Were every `b ∧ b′` in `W`, then `W = Λ²V`,
`m = D`: a contradiction. If `S ≠ V`, every join lies in `Λ²S = span{s ∧ s′ : s, s′ ∈ S}`, so
`W ⊆ Λ²S`. Let `Y_i ≠ 0` (S1) and `u ∉ S`; take a basis `s₁ = Y_i, s₂, …, s_r` of `S` and extend it by
`s_{r+1} = u, s_{r+2}, …, s_{d+1}` to a basis of `V`. The `s_α ∧ s_β` (`α < β`) are a basis of
`Λ²V`, `Λ²S` is spanned by those with `β ≤ r`, and `Y_i ∧ u = s₁ ∧ s_{r+1}` is another basis vector,
so it is not in `Λ²S ⊇ W`. A standard basis vector outside the proper subspace `S` exists, as the
standard basis spans `V`. ∎

## S5 — the insertion step, kept affine (session 1)

The second half of R1 (iv), in affine form, over every field with at least four elements. It is the
chapter's insertion lemma (`lem:pencil-insertion`) with `ρ = 0`, plus a rescaling.

**Statement.** Let `Y` be a good closed `m`-gon of affine points, and `Y_i ∧ u ∉ W(Y)` for a vertex
`Y_i` and some `u ∈ V`. For `t ∈ K` with `c(t) = 1 + tλ(u) ≠ 0` put `y(t) = (Y_i + tu)/c(t)`, an affine
point, and let `Y(t)` be the closed `(m + 1)`-gon `Y₀, …, Y_i, y(t), Y_{i+1}, …, Y_{m−1}`. Then `Y(t)`
is good for every `t` outside a set of at most three elements: `0`, `−1/λ(u)` if `λ(u) ≠ 0`, and at
most one more value.

**Proof.** The joins of `Y(t)` are `J_j` (`j ≠ i`), `Y_i ∧ y(t) = (t/c) Y_i ∧ u` and
`y(t) ∧ Y_{i+1} = (1/c)(J_i + t u ∧ Y_{i+1})`. For `t ≠ 0` and `c(t) ≠ 0` they are nonzero multiples
of the family `F(t) = ((J_j)_{j ≠ i}, Y_i ∧ u, J_i + t u ∧ Y_{i+1})`, so `Y(t)` is good iff `F(t)` is
independent. `F(0)` is `J₀, …, J_{m−1}` and `Y_i ∧ u`: independent, as the `J_j` are and
`Y_i ∧ u ∉ W(Y)`. In coordinates, `F(t)` is an `(m + 1) × D` matrix (so `m + 1 ≤ D`) with one row
affine in `t` and the others constant; some `(m + 1)`-minor `δ` has `δ(0) ≠ 0`, and by linearity of
the determinant in that row `δ(t) = δ(0) + tδ₁`, which has at most one root. Off `0`, `−1/λ(u)` and
that root, `F(t)` is independent and `y(t)` is defined. ∎

**Remark.** With `u` from S4's set, `λ(u) ∈ {0, 1}`, so the excluded values are `0`, possibly `−1`, and
at most one more: over `ℚ` one of `t = 1, 2` works.

## S6 — CERT (C1)–(C3) over every field with at least four elements (session 1)

**Statement.** Let `d ≥ 3` and `K` a field with `|K| ≥ 4` (every infinite field qualifies). Then:
- (C1) for every `3 ≤ m ≤ D` there is a good closed `m`-gon of affine points, and (S2 (a)) one with
  any three consecutive vertices at `P₁, P₀, P₂`;
- (C2) and (C3), together with `k = 2`: for every `2 ≤ k ≤ D − 1` there are affine points
  `p_a = p_b = P₀, p₁ = P₂, p₂, …, p_{k−1}, p_k = P₁` with the `k + 1` ear joins independent.

**Proof.** `m = 3`: `(P₀, P₁, P₂)`. The unimodular basis `P₀, …, P_d` is a basis of `V`, so the
`P_α ∧ P_β` (`α < β`) are a basis of `Λ²V`, and the triangle's joins `P₀∧P₁, P₁∧P₂, P₂∧P₀` are three of
them up to sign: the triangle is good and affine. For `3 ≤ m < D`, given a good affine `m`-gon, S4
gives `Y_i ∧ u ∉ W` and S5 (`|K| ≥ 4` leaves some `t`) a good affine `(m + 1)`-gon. Induction gives
(C1) for `3 ≤ m ≤ D`. Then S3 (affine input, every field) at `k = m − 1` gives the ears for
`2 ≤ k ≤ D − 1`: (C3) at `3 ≤ k ≤ D − 2`, (C2) at `k = D − 1`, and the flat ear at `k = 2`. ∎

**What this uses.** S1–S5 only: no Zariski-openness (S2 (b) is not used), no KT, no dimension count
beyond `m < D`. So R1 stands, with (ii) replaced by S2 (a), which holds over every field because the
insertion of S5 keeps every polygon affine. The field bound `|K| ≥ 4` is S5's three exclusions; the
consumers assume `[Infinite K]`.

## S7 — the collapsing placements: cycles with `m > D`, long ears with `k ≥ D − 1` (session 1)

The consumers' `hcard = min(m, D)` and `of_openEar`'s `n = D`, read in `Pᵈ`; every field.

**Statement.** Let `Y` be a good closed `D`-gon of affine points with `Y_{D−1}, Y₀, Y₁` at height
zero (S6 with S2 (a) at `i = 0`). For `m ≥ D` let `π_m(j) = Y_{min(j, D−2)}` for `0 ≤ j ≤ m − 2` and
`π_m(m − 1) = Y_{D−1}` (`strata.py`'s `placed`).
- (a) *Cycle*, bodies `c₀, …, c_{m−1}` in cyclic order, `m > D`: with `c_j` at `π_m(j)`, the `D` links
  `c_j c_{j+1}` (`0 ≤ j ≤ D − 3`), `c_{m−2} c_{m−1}` and `c_{m−1} c₀` are distinct links of the cycle,
  and their joins are `J₀, …, J_{D−1}` of `Y`, independent.
- (b) *Long ear* `a, x₁, …, x_k, b`, `k ≥ D − 1`: with `c₀ = a`, `c_j = x_j`, `c_j` at `π_{k+1}(j)` and
  `b` at `Y₀`, the `D` ear links `e₀, …, e_{D−3}`, `e_{k−1}`, `e_k` (`e_j` joining `c_j, c_{j+1}`,
  `c_{k+1} = b`) are distinct and their joins are `J₀, …, J_{D−1}` of `Y`; `a, x₁, x_k, b` sit at
  `Y₀, Y₁, Y_{D−1}, Y₀`, at height zero.

**Proof.** (a) For `j ≤ D − 3`, `c_j, c_{j+1}` sit at `Y_j, Y_{j+1}`; `c_{m−2}` sits at `Y_{D−2}`
(`m − 2 ≥ D − 2`) and `c_{m−1}` at `Y_{D−1}`; `c₀` at `Y₀`. So the joins are `J₀, …, J_{D−3}`,
`J_{D−2}`, `J_{D−1}`. The links are distinct because `D − 3 < m − 2`. (b) The same with `m = k + 1 ≥ D`
and `c_{m} = b` at `Y₀ = π(0)`: `e_{k−1}` joins `c_{k−1}` at `Y_{D−2}` (`k − 1 ≥ D − 2`) to `c_k` at
`Y_{D−1}`, and `e_k` joins `c_k` to `b` at `Y₀`; distinct since `D − 3 < k − 1`. `x₁ = c₁` is at `Y₁`
since `1 ≤ D − 3` (`D ≥ 6`). At `k = D − 1` the `D` links are all of `e₀, …, e_k`. ∎

At `d = 3` this is Phase 40's placement: `of_cycle` puts `x₄, …, x_k` at `Y₄` and `of_openEar` puts
`a, b` at `Y₀`, `x_k` at `Y₅` (`MC/Chain.lean`, read at `97a631ba`).

## S8 — exact control: S6's construction over `ℚ` at `d = 3..9` (session 1)

`PYTHONHASHSEED=0 python3 notes/attacks/cert/drivers/cert_r1.py` (default `--dims 3,4,5,6,7,8,9`).
Deterministic, no draw and no seed: every choice is the first in a fixed order. It reuses `strata.py`
read-only (`ext`, `closed_joins`, `placed`, `elementary_divisors`, `unimodular`, `cert_search`,
`cert_ear`, `cert_top`, `CERT_HEXAGON`).

**Population.** Each `d ∈ {3, …, 9}`; at each, the S6 polygons for every `3 ≤ m ≤ D`, their S3 ears for
every `2 ≤ k ≤ D − 1`, and S7's placements on cycles of `D + 1`, `D + 3` bodies and ears of `k = D`,
`D + 2`. No cap beyond `d ≤ 9`. The check is over `ℚ` only; S6 is the proof for other fields.

**Asserted** (exit 1 otherwise): S4's claim at each insertion (a vertex pair when `S = V`; when
`S ≠ V`, `Y_i ∧ e_c ∉ W` at every vertex); S5's "at most one bad value" as "at most one of
`t = 1, 2, 3` fails"; each affine `m`-gon good, joined points distinct; S2 (a)'s `g` making it affine
and good with `Y_{m−1}, Y₀, Y₁` at `P₁, P₀, P₂`; each ear's `k + 1` joins independent with
`a, x₁, x_k, b` at height zero; each collapse with exactly `D` nonzero joins, the `D`-gon's, independent.
Controls: the three `P³` placements on `certPt` (`of_cycle` `m = 3..6, 7, 9`; `of_openEar` `k = 5, 6, 8`;
`of_openEar_two`), unimodular, heights zero where needed; S2 (a) on the hexagon; Result 21's `d ≤ 6`
certificates re-asserted unimodular; negatives `[[1, 1], [1, −1]]` (factors 1, 2), a closed 4-gon in a
3-space, three consecutive collinear points, and the insertion at `t = 0`, each rejected.

**Figures.** All assertions pass at `d = 3..9`. Insertions with `S = V` / `S ≠ V`: 2/1, 5/2, 9/3, 14/4,
20/5, 27/6, 35/7 (the `S ≠ V` steps are the first `d − 2`). `t = 1` failed, and `t = 2` was taken, at 0, 0,
0, 1, 1, 1, 2 steps: S5's excluded root does occur, never twice in one step. **Reported** (R2's data,
not R1's): `strata.cert_top`'s closed `D`-gon is unimodular at `d = 7, 8, 9`, the brief's unretained
probe now retained.

## S9 — G1's revival trigger cannot fire (session 1; the verdict brief §6 asks for)

**Statement.** SHORT-CORE parks G1 with the trigger "CERT's open ears fail at some `d ≥ 7`"
(`notes/attacks/short-core/workbook.md` S56, *Parked, G1*). By S6, the open ears (C2) (`k = D − 1`) and
(C3) (`3 ≤ k ≤ D − 2`), and the flat ear at `k = 2`, exist at every `d ≥ 3` over every field with at
least four elements, so over every infinite field the consumers admit. So the trigger cannot fire.

**What it leaves.** Read from S56's own text (not re-derived here): S53's "no" then rests on S35 with
S20's factoring (`short` rows at `k ≥ 4`) and row 9's formal work at `D`; the `ear` and `long` rows'
other inputs (`hcount`'s deficiency facts, the ear rank formula at `D`, the hinge form) are PD-STEPS's
formal work, not CERT's. Whether G1 is retired is the PI's decision.
