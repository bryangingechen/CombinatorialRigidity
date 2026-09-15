# Attack `smark` — workbook (the 2-cut composition step)

Owner: attack `smark` (`notes/attacks/smark/`; brief and state there). Discipline:
`notes/pencil/workbook/README.md`. This file is the one place the attack appends
proved statements with their full hypotheses; the informal state of the attack
lives in `notes/attacks/smark/state.md`.

**No labels minted.** The brief assigns no label prefix and the attack may not edit
`notes/pencil/labels.md`, so results are numbered **S1, S2, …** and are cited by this
file's path until the PI assigns a prefix and registers it.

**Notation, aligned with BUNIF ((BE-94), owning section `bare-ext/BUNIF.md`).** A
2-separation `{u, v}` with generic flag pair `ϕ = (p_u, π_u, p_v, π_v)`: `p_u ≠ p_v`,
`π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v` (BUNIF's "generic regime"; its `x, y` are our
`u, v`). Coordinates on `K⁴`: `e₁ = p_u`, `e₂ = p_v`, `e₃, e₄` a basis of the line
`L := π_u ∩ π_v`, so `π_u = ⟨e₁, e₃, e₄⟩`, `π_v = ⟨e₂, e₃, e₄⟩`. The four blocks of
`Λ²K⁴` ((BE-94)(iii)):

| block | span | meaning | dim |
|---|---|---|---|
| `⟨M⟩` | `e₁∧e₂` | the line `p_u p_v` | 1 |
| `Π_u` | `e₁∧e₃, e₁∧e₄` | pencil of lines through `p_u` in `π_u` | 2 |
| `Π_v` | `e₂∧e₃, e₂∧e₄` | pencil of lines through `p_v` in `π_v` | 2 |
| `⟨L⟩` | `e₃∧e₄` | the line `π_u ∩ π_v` | 1 |

Write `x = (x_M; x_u; x_v; x_L)` with `x_u, x_v ∈ W := ⟨e₃, e₄⟩ ≅ K²`. The stabiliser
`S(ϕ) = {(a, b, C) : a, b ∈ K*, C ∈ GL₂}/K*` ((BE-94)(i)) acts by

    (a, b, C)·x = (ab·x_M ; a·Cx_u ; b·Cx_v ; det C·x_L),

with `(c, c, cI)` acting as the scalar `c²`; so `S(ϕ)` acts effectively on `P⁵ = P(Λ²K⁴)`
with `dim S(ϕ) = 5`. For a subspace `A ⊆ Λ²K⁴` and a block sum `U` write
`c_A(U) := dim(A ∩ U)` (BUNIF's `c_i(U)`). `K` is algebraically closed of
characteristic `0` throughout; "generic `g`" means "for `g` in a dense open subset of
`S(ϕ)`", and every dimension statement descends to an infinite subfield in the usual
way (a nonempty open set of a variety defined over `K₀` with a `K₀`-rational point …
is not automatic — see the field worry in the state file).

## S1 — the two semi-invariant quadrics and the orbit strata of `S(ϕ)` on `P⁵`

**S1(i) (semi-invariants).** `Q₁(x) := x_M·x_L` and `Q₂(x) := det[x_u | x_v]` satisfy
`Q_j(g·x) = χ(g)·Q_j(x)` with `χ(a, b, C) = ab·det C`. The Klein form (the quadratic
form whose zero set is the decomposable 2-forms, i.e. the lines of `P³`) is
`Q := Q₁ − Q₂` up to a scalar. *Proof.* Direct: `x_M x_L ↦ ab·det C·x_M x_L`;
`det[aCx_u | bCx_v] = ab·det C·det[x_u|x_v]`. For the Klein form: `x∧x` has
`e₁∧e₂∧e₃∧e₄`-coefficient `2(x_M x_L − det[x_u|x_v])` by expanding
`(x_M e₁∧e₂ + e₁∧x_u + e₂∧x_v + x_L e₃∧e₄)^{∧2}` — the only nonzero cross terms are
`e₁∧e₂ ∧ e₃∧e₄` and `(e₁∧x_u)∧(e₂∧x_v) = −e₁∧e₂∧x_u∧x_v`. ∎
The torus `T = {(a, b, diag(c₃, c₄))}` has weights `a+b, a+c₃, a+c₄, b+c₃, b+c₄, c₃+c₄`
on the six coordinates; the quadratic monomials of weight `a+b+c₃+c₄` are exactly
`x_M x_L`, `x_{u3}x_{v4}`, `x_{u4}x_{v3}`, and of the last two only the determinant is
`GL₂`-semi-invariant (`W^*⊗W^* = Sym² ⊕ Λ²`). So **the χ-semi-invariant quadratic forms
are exactly `span(Q₁, Q₂)`**, a pencil of quadrics containing the Klein quadric. (The
only other characters carrying a nonzero semi-invariant quadratic form are `a²b²` and
`(det C)²`, with the forms `x_M²` and `x_L²` — the squares of the two 1-dimensional block
coordinates, whose zero sets are the stable hyperplanes already in the table.) Control:
`notes/attacks/smark/drivers/orbits/task3_semiinvariants.py`.

**S1(ii) (orbit strata).** Set `I(x) := Q₁(x)/Q₂(x)` where defined. The following
locally closed `S(ϕ)`-stable subsets partition `P⁵`; in each, every orbit has the
dimension `d_Σ` listed, and `Σ` has the dimension `dim Σ` listed.

| stratum `Σ` | defining conditions | closure | `dim Σ` | `d_Σ` |
|---|---|---|---|---|
| `Gen` | `Q₁Q₂ ≠ 0`, `rank[x_u|x_v] = 2` | `P⁵` | 5 | 4 (orbits = `Gen ∩ {I = const}`) |
| `Z₀` | `x_M = 0`, `x_L ≠ 0`, rank 2 | `P(⟨L⟩^⊥)`, `⟨L⟩^⊥ = Π_u⊕Π_v⊕⟨L⟩` | 4 | 4 |
| `Z_∞` | `x_L = 0`, `x_M ≠ 0`, rank 2 | `P(⟨M⟩^⊥)`, `⟨M⟩^⊥ = ⟨M⟩⊕Π_u⊕Π_v` | 4 | 4 |
| `Z₀∞` | `x_M = x_L = 0`, rank 2 | `P(Π_u ⊕ Π_v)` | 3 | 3 |
| `R_gen` | rank 1, `x_u, x_v ≠ 0`, `x_M x_L ≠ 0` | `{Q₂ = 0}` (a quadric cone) | 4 | 4 |
| `R₀` | rank 1, `x_u, x_v ≠ 0`, `x_M = 0 ≠ x_L` | `{x_M = 0, Q₂ = 0}` | 3 | 3 |
| `R_∞` | rank 1, `x_u, x_v ≠ 0`, `x_L = 0 ≠ x_M` | `{x_L = 0, Q₂ = 0}` | 3 | 3 |
| `R₀∞` | rank 1, `x_u, x_v ≠ 0`, `x_M = x_L = 0` | Segre quadric in `P(Π_u⊕Π_v)` | 2 | 2 |
| `U_gen` | `x_v = 0 ≠ x_u`, `x_M x_L ≠ 0` | `P(Π_u^⊥)`, `Π_u^⊥ = ⟨M⟩⊕Π_u⊕⟨L⟩` | 3 | 3 |
| `U₀` | `x_v = 0 ≠ x_u`, `x_M = 0 ≠ x_L` | `P(Π_u ⊕ ⟨L⟩) = Λ²π_u` (lines in `π_u`) | 2 | 2 |
| `U_∞` | `x_v = 0 ≠ x_u`, `x_L = 0 ≠ x_M` | `P(⟨M⟩ ⊕ Π_u)` (lines through `p_u`) | 2 | 2 |
| `P_u` | `x_v = x_M = x_L = 0` | `P(Π_u)` | 1 | 1 |
| `V_gen, V₀, V_∞, P_v` | the same with `u ↔ v` | `P(Π_v^⊥)`, `Λ²π_v`, `P(⟨M⟩⊕Π_v)`, `P(Π_v)` | 3, 2, 2, 1 | same |
| `Ax` | `x_u = x_v = 0`, `x_M x_L ≠ 0` | `P(⟨M⟩ ⊕ ⟨L⟩)` | 1 | 1 |
| `pt_M`, `pt_L` | `x = e₁∧e₂`, `x = e₃∧e₄` | themselves | 0 | 0 |

*Proof.* Stability: each defining condition is a union of conditions "a block
coordinate vanishes / does not vanish", "rank[x_u|x_v] = r", or a level set of `I`,
all preserved by the action (S1(i)). Orbit dimensions: for `x ∈ Gen`, normalise
`(x_u, x_v) = (e₃, e₄)` by `C`, then `(a, b, diag(c₃, c₄))` with `ac₃ = bc₄ = 1` moves
`(x_M, x_L) ↦ (x_M/(c₃c₄), c₃c₄·x_L)`, sweeping the curve `x_M x_L = const` in the
2-dimensional normal slice; so the orbit is the 4-fold `Gen ∩ {I = I(x)}` and the
stabiliser has dimension 1. For `x ∈ Z₀` the same normalisation leaves `x_L` free to
scale (`c₃c₄`), so the orbit is open in `{x_M = 0}`; symmetrically `Z_∞`; in `Z₀∞` the
stabiliser is `{ac₃ = bc₄}`, 2-dimensional, orbit dimension 3. Rank 1 with both
nonzero: normalise `x_u = e₃`, `x_v = e₃`; then `C` is upper triangular in `(e₃, e₄)`,
`a = b = 1/c₃`, `x_L ↦ c₃c₄ x_L` (free), `x_M ↦ x_M/c₃²` (free over `K̄`); the
off-diagonal entry of `C` acts trivially, giving stabiliser dimensions 1, 2, 2, 3 for
`R_gen, R₀, R_∞, R₀∞`. For `x_v = 0 ≠ x_u`: normalise `x_u = e₃`; `b` scales `x_M` freely
and `c₄` scales `x_L` freely, giving stabiliser dimensions 2, 3, 3, 4 for
`U_gen, U₀, U_∞, P_u`. `Ax`: `ab` and `det C` scale `x_M, x_L` independently. The
dimensions of the strata are read off the conditions. ∎ *(Whether each special stratum
is a single orbit is irrelevant below — only `d_Σ` is used. Control:
`notes/attacks/smark/drivers/orbits/task12_orbits.py` checks `d_Σ` at three exact
representatives of every stratum, `mismatches: none`.)*

Consequences used below: (a) the 16 `S(ϕ)`-stable subspaces are the block sums
((BE-94)(iii)), and each is the span of a stratum's closure in the table; (b)
`Q`-orthogonal complements permute the block sums (`⟨M⟩^⊥ = {x_L = 0}`,
`⟨L⟩^⊥ = {x_M = 0}`, `Π_u^⊥ = {x_v = 0}`, `(Π_u⊕Π_v)^⊥ = ⟨M⟩⊕⟨L⟩`, and
`⟨M⟩⊕Π_u`, `Π_u⊕⟨L⟩` are self-orthogonal — the α- and β-planes through `p_u`, in `π_u`).

## S2 — Theorem (gauge transversality: the block cap is attained by `S(ϕ)`, outside an explicit list)

Let `A, B ⊆ Λ²K⁴` with `ρ₁ := dim A`, `ρ₂ := dim B`, `ρ₁ + ρ₂ ≤ 6`. Assume

- **(B)** for every block sum `U`: `c_A(U) + c_B(U) ≤ dim U`;
- **(X1)** not: `ρ₁ = ρ₂ = 3` and `P(A), P(B)` both lie on one smooth member
  `{Q₁ = I₀Q₂}`, `I₀ ∈ K*`, of the pencil (both maximal isotropic for the same `Q_{I₀}`);
- **(X2)** not: `ρ₁ + ρ₂ = 6` and `Q₂|_A ≡ 0 ≡ Q₂|_B`;
- **(X3)** not: `{c_A(E), c_B(E)} = {2, 3}` with `Q₂|_{A∩E} ≡ 0 ≡ Q₂|_{B∩E}`, for
  `E = ⟨L⟩^⊥` or `E = ⟨M⟩^⊥`;
- **(X4)** not: `c_A(E) = c_B(E) = 2` with `Q₂|_{A∩E} ≡ 0 ≡ Q₂|_{B∩E}`, for
  `E = Π_u ⊕ Π_v` (i.e. both `A ∩ E`, `B ∩ E` are ruling planes of the Segre quadric:
  a pencil `y ∧ L` with `y ∈ M`, or a pencil `w ∧ M` with `w ∈ L`).

Then `A ∩ g·B = 0` for generic `g ∈ S(ϕ)`. Condition (B) is necessary for the
conclusion; (X1)–(X4) are the cases where the proof's count is inconclusive, and in
**(X1) with `A, B` in the same family** of maximal isotropic subspaces of `Q_{I₀}` the
conclusion is **false** for every `g` (S4).

*Proof.* Necessity of (B): `U` is `g`-stable, so `A ∩ gB ⊇ (A∩U) ∩ g(B∩U)`, of dimension
`≥ c_A(U) + c_B(U) − dim U`.

Sufficiency. Put `Bad := {g : A ∩ gB ≠ 0} = pr₁(I)` for the incidence
`I := {(g, y) ∈ S(ϕ) × P(B) : g·y ∈ P(A)}`. It suffices to show `dim I ≤ 4 < 5 = dim S(ϕ)`.
Stratify `P(B)` by the strata `Σ` of S1(ii): `I = ⊔_Σ I_Σ`, `I_Σ := I ∩ (S(ϕ) × Σ)`. The
fibre of `I_Σ → P(B) ∩ Σ` over `y` is `F_y = {g : g·y ∈ P(A) ∩ S(ϕ)·y}`, a union of
cosets of `Stab(y)` indexed by `P(A) ∩ S(ϕ)·y`, so

    dim F_y = dim(P(A) ∩ S(ϕ)·y) + 5 − d_Σ  ≤  dim(P(A) ∩ Σ) + 5 − d_Σ,      (∗)

and `dim I_Σ ≤ dim(P(B) ∩ Σ) + dim(P(A) ∩ Σ) + 5 − d_Σ`, both intersections nonempty
(else `I_Σ = ∅`).

*The generic stratum.* For `y ∈ P(B) ∩ Gen`, `S(ϕ)·y ⊆ Q_{I(y)} := {Q₁ = I(y)Q₂}`, so
`dim(P(A) ∩ S(ϕ)·y) ≤ dim(P(A) ∩ Q_{I(y)})`, which is `ρ₁ − 2` unless `P(A) ⊆ Q_{I(y)}`,
when it is `ρ₁ − 1`. If `I` is non-constant on `P(B) ∩ Gen` (an open subset of the
irreducible `P(B)`, hence irreducible), the locus where `I(y) = I₀` has dimension
`≤ ρ₂ − 2` for each `I₀`, and `dim I_Gen ≤ max((ρ₂−1) + (ρ₁−2) + 1, (ρ₂−2) + (ρ₁−1) + 1)
= ρ₁ + ρ₂ − 2 ≤ 4`. If `I ≡ I₀` on `P(B) ∩ Gen`, then `P(B) ⊆ Q_{I₀}` and
`dim I_Gen ≤ (ρ₂−1) + dim(P(A) ∩ Q_{I₀}) + 1`, which is `≤ ρ₁ + ρ₂ − 2 ≤ 4` unless also
`P(A) ⊆ Q_{I₀}`, when it is `≤ ρ₁ + ρ₂ − 1`. That exceeds 4 only at `ρ₁ + ρ₂ = 6`, and a
linear space on a smooth 4-dimensional quadric has dimension `≤ 2`, forcing
`ρ₁ = ρ₂ = 3`: this is (X1).

*Strata with linear closure.* For each of `Z₀, Z_∞, Z₀∞, U_∗, V_∗, P_u, P_v, Ax, pt_M, pt_L`
the closure is `P(E)` for a block sum `E` with `d_Σ = dim Σ = dim E − 1`, and
`P(A) ∩ Σ ⊆ P(A ∩ E)`. By (∗),
`dim I_Σ ≤ (c_A(E) − 1) + (c_B(E) − 1) + 5 − (dim E − 1) = c_A(E) + c_B(E) − dim E + 4 ≤ 4`
by (B).

*The rank-one strata.* Their closures are quadric sections: `R_gen ⊆ {Q₂ = 0}`,
`R₀ ⊆ P(⟨L⟩^⊥) ∩ {Q₂ = 0}`, `R_∞ ⊆ P(⟨M⟩^⊥) ∩ {Q₂ = 0}`, `R₀∞ ⊆ P(Π_u⊕Π_v) ∩ {Q₂ = 0}`.
For a subspace `A' = A ∩ E`, `P(A') ∩ {Q₂ = 0}` is the zero set of the quadratic form
`Q₂|_{A'}`: a hypersurface of dimension `dim A' − 2` if `Q₂|_{A'} ≢ 0`, all of `P(A')`
(dimension `dim A' − 1`) if `Q₂|_{A'} ≡ 0`. Write `ε_A(E) = 1` if `Q₂|_{A∩E} ≢ 0`, else `0`.
Then, with `E = Λ²K⁴, ⟨L⟩^⊥, ⟨M⟩^⊥, Π_u⊕Π_v` and `d_Σ = 4, 3, 3, 2`:

    dim I_Σ ≤ (c_A(E) − 1 − ε_A) + (c_B(E) − 1 − ε_B) + 5 − d_Σ.

- `R_gen`: `≤ ρ₁ + ρ₂ − 1 − ε_A − ε_B`; this is `≤ 4` unless `ρ₁ + ρ₂ = 6` and
  `ε_A = ε_B = 0`, which is (X2).
- `R₀`, `R_∞`: `≤ c_A(E) + c_B(E) − ε_A − ε_B`, and (B) gives `c_A(E) + c_B(E) ≤ 5`; so
  `≤ 4` unless the sum is `5` and both `ε = 0`. A `Q₂`-isotropic subspace of `E = ⟨L⟩^⊥`
  has dimension `≤ 3` (`Q₂|_E` has radical `⟨L⟩` and induces the split rank-4 form on
  `Π_u ⊕ Π_v`, whose isotropic subspaces have dimension `≤ 2`), so the sum `5` splits as
  `{2, 3}`: this is (X3).
- `R₀∞`: `≤ c_A(E) + c_B(E) + 1 − ε_A − ε_B` with `c_A(E) + c_B(E) ≤ 4` by (B); `≤ 4` unless
  the sum is `4` and both `ε = 0`; isotropic subspaces of `(Π_u⊕Π_v, det)` have
  dimension `≤ 2`, so both are `2`: this is (X4). The isotropic 2-planes of the
  determinant form on `W ⊗ K²` are the two rulings `{w ⊗ K²}` and `{W ⊗ e}`; in
  `Λ²K⁴` these are the pencils `(αe₁ + βe₂) ∧ w` (vertex `w ∈ L`, plane `⟨w, M⟩`) and
  `y ∧ W` with `y = e₁ + μe₂ ∈ M` (vertex `y ∈ M`, plane `⟨y, L⟩`), together with `Π_u`,
  `Π_v` themselves.

Summing over the finitely many strata, `dim I ≤ 4`, so `Bad` is a proper closed subset
of the irreducible `S(ϕ)`. ∎

**Remarks.** (1) The count is only an upper bound; in (X2)–(X4) it can be beaten by a
direct argument in specific cases (e.g. `A ∩ E = Π_u`, `B ∩ E = Π_v` in (X4) is harmless),
so those clauses are *hypotheses of this proof*, not obstructions. (X1) same-family is
an obstruction (S4). (2) Where `ρ₁ + ρ₂ ≥ 7` the conclusion `A ∩ gB = 0` is impossible;
the relevant statement is S3.

## S3 — Corollary (the dual case; the unified block criterion; (BE-96)(iv)'s `⟸`)

For `ρ₁ + ρ₂ ≥ 6`: `A + gB = Λ²K⁴ ⟺ A^⊥ ∩ (gB)^⊥ = 0 ⟺ A^⊥ ∩ g(B^⊥) = 0`, because
`Q(gx, gy) = χ(g)Q(x, y)` gives `(gB)^⊥ = g(B^⊥)` (`⊥` is Klein-orthogonality). Apply S2
to `(A^⊥, B^⊥)`, of dimensions `6 − ρ₁`, `6 − ρ₂`. Using
`c_{A^⊥}(U) = dim U − ρ₁ + c_A(U^⊥)` and S1's list of complements, hypothesis (B) for
`(A^⊥, B^⊥)` reads

    c_A(U) + c_B(U) ≤ dim U + (ρ₁ + ρ₂ − 6)   for every block sum U,

and (X1)–(X4) become the corresponding conditions on `A^⊥, B^⊥`. Hence, for all
`ρ₁, ρ₂`: **if `c_A(U) + c_B(U) ≤ dim U + max(0, ρ₁ + ρ₂ − 6)` for all 16 block sums `U`,
and the pair `(A, B)` (resp. `(A^⊥, B^⊥)` when `ρ₁ + ρ₂ > 6`) is not in (X1)–(X4), then
`dim(A + gB) = min(6, ρ₁ + ρ₂)` for generic `g ∈ S(ϕ)`.**

This is the `⟸` direction of (BE-96)(iv) — BUNIF's "law", there a measurement
(`bunif.py abst`, 400/400, (BE-96)(iii)) and a theorem only where its degeneration
bound meets the cap ((BE-96)(i)–(ii)) — proved outside (X1)–(X4). Read against
(BE-95)(i): `blockcap` is attained by the gauge group alone, without the side moduli,
whenever the isotropy exceptions are absent. Read against BEARCASE: for an ear side
with `m ≥ 3`, (BE-35)(iv)'s `max dim(A + ρ̄₂) = min(6, δ₁ + δ₂ − max(P, Z, R))` has
`(P)` = the block `Π_u` (or `Π_v`) inequality, `(Z)` = the block `Π_u ⊕ Π_v` inequality
and `(R)` = the ruling clause (X4) — S3 is that classification for an arbitrary
partner in place of the ear.

## S4 — Example (the block inequalities do not suffice: the Klein parity obstruction)

Let `p, p' ∈ P³` be points in general position with respect to `ϕ` (not on `M`, `L`,
`π_u`, `π_v`), `A := star(p) = p ∧ K⁴` and `B := star(p')` — the 3-dimensional
subspaces of lines through `p`, through `p'`. Both are maximal isotropic for the Klein
form `Q = Q₁ − Q₂` and lie in the *same* family (the α-planes of the Klein quadric), so
`dim(A ∩ B') ∈ {1, 3}` for every α-plane `B'`; `gB` is an α-plane for every `g ∈ PGL₄`,
hence **`A ∩ gB ≠ 0` for every `g`** — concretely `A ∩ gB ∋ p ∧ g(p')`, the line joining
the two vertices. Yet (B) holds with `ρ₁ + ρ₂ = 6` (slack 0): `c(Π_u) = 0` (`p ∉ π_u`),
`c(⟨M⟩) = c(⟨L⟩) = 0`, `c(⟨M⟩⊕Π_u) = 1` (the line `p p_u`), `c(Π_u ⊕ ⟨L⟩) = 0`,
`c(Π_u^⊥) = 1`, `c(Π_u⊕Π_v) = 1` (the transversal through `p` of `M` and `L`),
`c(⟨L⟩^⊥) = 2` (the pencil at `p` in the plane `⟨p, L⟩`), `c(⟨M⟩^⊥) = 2`, and the same
for `p'`; every sum is `≤ dim U`. This is (X1) at `I₀ = 1`, same family.
Control: `notes/attacks/smark/drivers/orbits/task45_parity.py` (exact ℚ, seeded):
`dim(A ∩ gB) = 1` at 20 pairs × 30 group elements, all 16 defects `≤ 0`. The
opposite-family pair `A = star(p)`, `B = Λ²π` (lines in a plane `π`) has
`dim(A ∩ gB) = 0` at 20 × 30 (task 5): (X1) is an obstruction only in the same-family case.

*Consequence for the corpus.* (BE-96)(iv)'s criterion "(BE-67)(iii) holds ⟺ the 14
block inequalities" is **incomplete as an abstract statement about subspaces**: the
right-hand side must add "and the pair avoids the isotropy exceptions (X1)–(X4)" (or
at least (X1) same-family). Whether a *side* `(H_i, u, v)` can have `ρ̄_i` maximal
isotropic — a spherical joint between `u` and `v`, or `v` sliding in a plane — is a
question about sides, addressed under S5. `bunif.py abst`'s support (generic,
block-adapted, or confined-to-a-block-sum draws) contains no isotropic pair, which is
why 400/400 saw none.

## S5 — What S2–S3 do to the Lemma (route R1 of the attack)

Setting of the attack's statement (`notes/attacks/smark/state.md` *Statement*): `G`
2-connected of girth `≥ 5`, `{u, v}` a 2-separation with `u ≁ v`, generic `ϕ`,
components `Y_i ⊆ Y°(H_i; ϕ)` at whose generic point `H_i` and `H_i/uv` attain
(`a_i = 0`, `ρ_i = δ_i`). By (BE-94)(ii) `S(ϕ)` acts on side 2 alone and
`Y₁ × gY₂ = Y₁ × Y₂` (`S(ϕ)` connected). On the open subset of `Y₁ × Y₂` where both sides
attain, `dim(ρ̄₁ + ρ̄₂) = rank R(G) − rank R₁ − rank R₂ + 6` is lower semicontinuous, so one
good pair `(q₁, g·q₂)` makes the generic point good. Hence, by S3 with `A = ρ̄₁(q₁)`,
`B = ρ̄₂(q₂)` at generic `q_i`:

> **The Lemma holds at `(G; u, v)` as soon as the generic profiles satisfy the 14
> block inequalities `c₁(U) + c₂(U) ≤ dim U + max(0, δ₁ + δ₂ − 6)` and the generic pair
> avoids (X1)–(X4)** (on `(ρ̄₁, ρ̄₂)` if `δ₁ + δ₂ ≤ 6`, on the Klein complements otherwise).

Both conditions are per-side data at `ϕ` plus a finite check on the pair. What remains
open is exactly the attack's obligation **O4/O5**: prove the profile bounds for
girth-`≥ 5` sides from their structure at `u, v`. The exceptions are structural
statements about sides: (X1) says `ρ̄_i` is a star or a plane-of-lines (or their `Q_I`
analogues), (X2)–(X4) say `ρ̄_i` (or its trace on a block sum) is isotropic for the
determinant form, i.e. lies in a ruling. None is known to occur for a side with
`ρ_i = δ_i` at generic `ϕ`; none is excluded yet.

**Control data (session 1) — `notes/attacks/smark/drivers/sideprof.py`.** Exact ℚ, seed
`20260915`, 6 draws per side at a prescribed generic flag pair (`bimage.sample_flags`,
`bdecor.sample_by_branches(..., fixed=…)`), every draw guarded by
`verify_pencil_witness`, `assert_generic_star`, the four exact genericity conditions on
`ϕ`, and the pendant-trick identity. "excess" is `c(U) − max(0, ρ + dim U − 6)`, listed
only where nonzero; Gram = ranks of `(Q₁, Q₂, Q)` on `ρ̄`. All eleven sides have girth
`≥ 5`, `ρ = δ` and attain at every draw; the profile is constant across draws except
one `theta34` draw (excess 1 at `Π_v ⊕ ⟨L⟩`), gone at 24/24 draws on seed `1`.

| side (`u`, `v` side-degrees) | `ρ = δ` | excess (block: amount) | Gram |
|---|---|---|---|
| `ear1` (1, 1) | 2 | `Π_u`, `Π_v`, `⟨M⟩⊕Π_u`, `⟨M⟩⊕Π_v`, `Π_u⊕⟨L⟩`, `Π_v⊕⟨L⟩`, `⟨M⟩⊕Π_u⊕Π_v`, `Π_u^⊥`, `Π_v^⊥`, `Π_u⊕Π_v⊕⟨L⟩`: 1; `Π_u⊕Π_v`: 2 | (0, 0, 0) |
| `ear2` (1, 1) | 3 | `Π_u`, `Π_v`, `⟨M⟩⊕Π_u`, `⟨M⟩⊕Π_v`, `Π_u⊕Π_v`, `Π_u⊕⟨L⟩`, `Π_v⊕⟨L⟩`: 1 | (1, 3, 2) |
| `ear3` (1, 1) | 4 | `Π_u`, `Π_v`: 1 | (2, 4, 4) |
| `ear4`, `ear5` (1, 1) | 5, 6 | none | (2, 4, 5), (2, 4, 6) |
| `theta33`, `theta34`, `theta44` (2, 2) | 2, 3, 4 | none | (2, 2, 2), (2, 3, 3), (2, 4, 4) |
| `tail` (1, 1; a degree-3 hub inside) | 4 | `Π_u`, `Π_v`: 1 | (2, 4, 4) |
| `cycletail` (2, 1) | 2 | `Π_v`, `⟨M⟩⊕Π_v`, `Π_u⊕Π_v`, `Π_v⊕⟨L⟩`, `Π_v^⊥`: 1 | (1, 1, 0) |
| `dumbbell` (2, 2) | 1 | none | (1, 1, 0) |

Read-offs (measurements, not theorems): excess at a terminal pencil `Π_u` appears exactly
at side-degree 1 of `u` (the hinge `L_{uw}` itself is a relative screw), never at
side-degree 2; `ρ̄` is Klein-isotropic only at `ρ ≤ 2` (a line, a pencil) — no
3-dimensional isotropic `ρ̄`, so (X1) is not realised here; `ear1`'s `ρ̄` is the ruling
plane `w ∧ M` (`w = p_{w₁} ∈ L`), so a *side* can realise the (X4) shape — the pair is in
(X4) only if the partner's trace on `Π_u ⊕ Π_v` is also a ruling plane, which at girth
`≥ 5` cannot be a second 2-path (two common neighbours of `u, v` form a 4-cycle).

**Verdict.** S1–S4: *proven-informally* (S1(ii)'s orbit dimensions and S4's counts
computer-checked in exact arithmetic by `drivers/orbits/`). S5: *true-modulo-named-gap*,
the gap being the per-side profile bounds (O4/O5 in the state file). **What would
change this:** a girth-`≥ 5` side pair at generic `ϕ` with `ρ_i = δ_i` violating a block
inequality (a genuine shortfall, by (BE-95)(i)), or realising (X1) same-family (a
shortfall S2 cannot see); either would refute the Lemma as stated, not S2.

## S6 — Lemma (side-degree 1 at a terminal: the reduction to `H − u`)

Let `(H; u, v)` be a side with `u` of side-degree 1, neighbour `w`, `L := L_{uw} = p_u ∧ p_w ∈ Π_u`.
Then `H − u` is connected (else `u` is a cut vertex of `G`), and with `ρ̄' := ρ̄_{wv}(H − u)`,
`f' := def₃(H − u)`, `g' := def₃((H − u)/wv)`, `δ' := f' − g'`:

- **(i)** `m ↦ (m|_{H−u}, t)` with `m(w) − m(u) = t·L` is an isomorphism `M(H) ≅ M(H − u) × K`;
  hence `ρ̄_{uv}(H) = ρ̄' + K·L` and `ρ_{uv}(H) = ρ' + 1 − [L ∈ ρ̄']`.
- **(ii)** `f(H) = f' + 1`; `g(H) = max(g', f'_sep − 5)` where `f'_sep` is the maximum of the
  partition count of `H − u` over partitions separating `w` from `v` (so `g(H) = max(g', f' − 5)`
  when `δ' ≥ 1`); `δ(H) = min(δ' + 1, 6)`.
- **(iii)** `H` attains ⟺ `H − u` attains. `H` welded-attains at `(u, v)` ⟺ `H − u`
  welded-attains at `(w, v)` **and** (`δ' = 6` or `L ∉ ρ̄'`).
- **(iv)** (profile transfer, assuming `L ∉ ρ̄'`) for a block sum `U`: if `Π_u ⊆ U` then
  `c_H(U) = c'(U) + 1`; if `Π_u ∩ U = 0` then `c_H(U) = dim(ρ̄' ∩ (U ⊕ K·L))`.

*Proof.* (i) Given `(m', t)`, set `m(u) := m'(w) − tL`; the only constraint on `u` is the hinge
`uw`. Then `m(v) − m(u) = (m'(v) − m'(w)) + tL`. (ii) For a partition `P` of `V(H)`: if `{u}` is
a part, the count is that of `P − {u}` plus `6 − 5 = 1`; otherwise deleting `u` from its part
changes the count by `+5·[uw crosses P] ≥ 0`. So `f(H) = f' + 1`. The welded graph `H/uv` is
`(H − u)` plus an edge `wv` (parallel if `w ∼ v`): partitions of `V(H − u)` not separating
`w, v` count as in `(H − u)/wv`, separating ones lose `5`. For `δ` use `f' = max(f'_sep, g')`.
(iii) `dim M(H) = dim M(H − u) + 1 = 6 + f' + 1 + a'`, so `a(H) = a'`. Welded:
`M(H/uv) = {m : m(u) = m(v)} ≅ {(m', t) : m'(v) − m'(w) = −tL}`, the preimage of `ρ̄' ∩ KL`
under `m' ↦ m'(v) − m'(w)`, so `dim M(H/uv) = dim M((H−u)/wv) + [L ∈ ρ̄'] = 6 + g' + a'_w + [L ∈ ρ̄']`,
to be compared with `6 + g(H)`: for `δ' ≤ 5`, `g(H) = g'` and both terms must vanish; for
`δ' = 6`, `g(H) = g' + 1` and `a'_w = 0` forces `ρ̄' = Λ²K⁴ ∋ L`. (iv) `L ∈ U` iff `Π_u ⊆ U`
(a block sum meets the block `Π_u` in `0` or `Π_u`). If `L ∈ U`: `(ρ̄' ⊕ KL) ∩ U = (ρ̄' ∩ U) ⊕ KL`.
If `L ∉ U`: `x + tL ∈ U` with `x ∈ ρ̄'` iff `x ∈ ρ̄' ∩ (U ⊕ KL)`, and `x ↦ x + tL` is injective. ∎

*Reading.* The welded hypothesis at a side-degree-1 terminal is **not** inherited for free: it
demands `L_{uw} ∉ ρ̄_{wv}(H − u)` — the hinge at `u` must not already be a relative screw of
`v` against `w`. When it is, `ρ(H) = δ' = δ(H) − 1` and `H` has welded loss exactly `1`
(the brief's "planted degenerate stratum" shape). In (iv) the second case involves
`U ⊕ K·L_{uw}`, a block sum plus one line of the pencil `Π_u ∌`-block: this is *not* a block
sum of the flag pair `(p_w, π_w; p_v, π_v)` of `H − u`, which is why the block calculus does not
descend through a side-degree-1 terminal (state file, *Where it breaks*, third gap).

## S7 — Proposition (excess is attainment loss of a bar-augmented side; the witness principle)

Fix a side `(H; u, v)` at flags `ϕ`, a configuration `q`, and a subspace `U ⊆ Λ²K⁴`. Put
`M_U(H) := {m ∈ M(H) : m(v) − m(u) ∈ U}`.

- **(i)** `M_U(H)/M(H/uv) ≅ ρ̄ ∩ U`, so `c(U) = dim M_U(H) − dim M(H/uv)`.
- **(ii)** `M_U(H)` is the motion space of the **body–bar–hinge framework** `H ∪ bars(U^⊥)`:
  `H` plus `6 − dim U` bars between the bodies `u` and `v` along lines spanning the
  Klein-complement `U^⊥`. (A bar along a line `ℓ` imposes `Q(m(v) − m(u), ℓ) = 0`, the
  body–bar constraint; every block sum `U` and its complement `U^⊥` — again a block sum, S1 —
  is spanned by lines: `⟨M⟩`, `⟨L⟩` are lines, `Π_u`, `Π_v` pencils.) Concretely: the joint
  `U = ⟨L⟩^⊥` is one bar along `L = π_u ∩ π_v`; `U = ⟨M⟩^⊥` one bar along `M = p_u p_v`;
  `U = Π_u ⊕ Π_v` the two bars `M`, `L`; `U = Π_u` the four bars `M`, `L` and two lines of `Π_u`.
- **(iii)** (count) For every partition `P` of `V(H)`,
  `dim M_U(H) ≥ 6|P| − 5 d_H(P) − (6 − dim U)·[P separates u, v]`, hence
  `dim M_U(H) ≥ 6 + max(g, f_sep + dim U − 6)`, `= 6 + max(g, f + dim U − 6)` when `δ ≥ 1`.
- **(iv)** (excess = loss) If `H/uv` attains at `q` and `δ ≥ 1`, then
  `exc(U) := c(U) − max(0, δ + dim U − 6) = dim M_U(H) − [6 + max(g, f + dim U − 6)] ≥ 0`
  is the attainment loss of `H ∪ bars(U^⊥)` against its own Tay count. **No excess at `U` ⟺
  `H ∪ bars(U^⊥)` attains.** (The generic lower bound `c(U) ≥ max(0, ρ + dim U − 6)` is the
  count in (iii); it does not need welded attainment when stated with `ρ`.)
- **(v)** (Klein self-duality) `c(U) = ρ + dim U − 6 + dim(T ∩ U^⊥)` with `T := ρ̄^⊥` the space
  of wrenches transmissible from `u` to `v` through `H`; so `exc(U)` for `(ρ̄, U)` equals the
  excess of `(T, U^⊥)` — the pair `(ρ̄^⊥, U^⊥)` of S3.
- **(vi)** (witness principle) `q ↦ dim M_U(H)(q)` is upper semicontinuous on the space of
  configurations (rank of a matrix with entries polynomial in `q`, bars fixed by `ϕ`), and so
  are `q ↦ dim M(H)(q)` and `q ↦ dim M(H/uv)(q)`. Hence for every irreducible component `Y` of
  `Y°(H; ϕ)` and every `q₀ ∈ Ȳ` at which the hinge lines are defined: `H` attaining at `q₀`,
  `H/uv` attaining at `q₀`, and `dim M_U(H)(q₀) ≤ D` each hold at the generic point of `Y`;
  in particular `c(U) ≤ D − 6 − g` there. **One exact configuration certifies attainment,
  welded attainment, and upper bounds on all sixteen `c(U)` for every component through it.**

*Proof.* (i) `m ↦ m(v) − m(u)` maps `M_U(H)` onto `ρ̄ ∩ U` with kernel `M(H/uv)`. (ii) `m(v) − m(u) ∈ U`
iff `Q(m(v) − m(u), ℓ) = 0` for `ℓ` in a spanning set of `U^⊥`, since `Q` is nondegenerate.
(iii) Motions constant on the parts of `P` form a `6|P|`-dimensional space on which only the
crossing constraints act: `5` per crossing hinge, `6 − dim U` for the joint if it crosses.
The trivial partition gives `6`, non-separating ones `6 + g`, separating ones
`6 + f_sep − 6 + dim U`; when `δ ≥ 1`, `f_sep = f`. (iv) Combine (i), (iii) and
`dim M(H/uv) = 6 + g`: `c(U) ≥ max(0, f − g + dim U − 6)`, and the difference is the gap in
(iii). (v) `dim(ρ̄ ∩ U) = ρ + dim U − dim(ρ̄ + U)` and `(ρ̄ + U)^⊥ = T ∩ U^⊥`. (vi) Lower
semicontinuity of rank; on an irreducible variety an upper semicontinuous integer function
attains its minimum on a dense open set. ∎

*Reading for the attack.* Obligation **O4** ("per-side profile bounds") is, block by block,
**an attainment statement for the side plus one, two or four bars between its terminals along
the flag lines** — the same kind of statement as the target, for a body–bar–hinge framework
that is not a pencil configuration. Two consequences. (a) Per side and per `ϕ` it is
decidable by **one** exact witness (vi), which is what the S5 control table already contains:
each row of that table is a *theorem* for the component through the draw, not a measurement —
the README's "measurement of the sampled component at 6 draws" undersells it. (b) There is no
prospect of reading `c(U)` off the structure of `H` at `u, v` alone: `exc(U) = 0` is a global
rigidity statement about `H ∪ bars`.

## S8 — Corollary (sides without interior hubs: the fibre is irreducible; the ear and theta profiles are theorems)

If no vertex of `V(H) − {u, v}` has degree `≥ 3` in `H`, then `Y°(H; ϕ)` is a nonempty open
subset of `∏_{x ∈ N(u)∩N(v)} L × ∏_{x ∈ N(u)∖N(v)} π_u × ∏_{x ∈ N(v)∖N(u)} π_v × ∏_{others} P³`
(the only constraints are the flag incidences, distinctness of adjacent points, and the
open non-degeneracy conditions), hence irreducible. By S7(vi) a single exact configuration
then determines attainment, welded attainment and upper bounds on every `c(U)` at the generic
point of the whole fibre; the lower bounds are the count `max(0, ρ + dim U − 6)` and the
structural incidences (`L_{uw} ∈ ρ̄ ∩ Π_u` at side-degree 1). Applied to the S5 table
(`drivers/sideprof.py`, any single draw of the eleven, seed `20260915`):

- **Ears.** `ρ̄(ear_m) = span(L₀, …, L_m)` is `(m+1)`-dimensional for `m ≤ 5`
  (`ρ = δ = m + 1`), attains and welded-attains, with profile: `m = 1`: `ρ̄ = w ∧ M` (a ruling
  plane of `Π_u ⊕ Π_v`), `c(U) = dim(w∧M ∩ U)`; `m = 2`: `c(Π_u) = c(Π_v) = 1`,
  `c(Π_u ⊕ Π_v) = 2`, `c(⟨M⟩⊕Π_u) = c(Π_u⊕⟨L⟩) = 1` (and `u ↔ v`), `c(⟨M⟩) = c(⟨L⟩) = c(⟨M⟩⊕⟨L⟩) = 0`,
  all other blocks generic; `m = 3`: `c(Π_u) = c(Π_v) = 1`, all else generic; `m = 4, 5`:
  generic throughout.
- **Thetas** `theta33, theta34, theta44` (`ρ = δ = 2, 3, 4`, side-degree 2 at both ends)
  and **`dumbbell`** (`ρ = δ = 1`): **no excess** — every `c(U)` equals `max(0, ρ + dim U − 6)`.
  In particular `c(Π_u) = c(Π_v) = 0` at side-degree 2, the first gap of the state file, is a
  theorem for these four sides (not for side-degree `≥ 2` in general).
- `tail` and `cycletail` have an interior hub; their rows are theorems for the component
  through the draw (S7(vi)) — `cycletail`'s `ρ̄` is the pencil `⟨L_{vt}, L_{c₂t}⟩` at `p_t`,
  by S6(i) applied at `v` and then at `t` (the 5-cycle is rigid, `ρ̄_{uc₂}(C₅) = 0`).

## S9 — Theorem (the `ear1` composition criterion: the consumed shape, in closed form)

Let side 2 be `ear1 = u x v` (so `p_x ∈ L`, `ρ̄₂ = p_x ∧ M := ⟨p_x∧p_u, p_x∧p_v⟩`, `δ₂ = 2`,
`a₂ = 0`, welded-attaining, fibre `Y₂ = L ≅ P¹`), and side 1 any `(H; u, v)` with a
component `Y₁` at whose generic point `H` and `H/uv` attain, `δ := δ₁`. Write
`A' := ρ̄₁ ∩ (Π_u ⊕ Π_v)` at the generic point of `Y₁`, and `T₁ := ρ̄₁^⊥`. In the adapted
coordinates `Π_u ⊕ Π_v = {(x_u, x_v)} ≅ W ⊗ K²`, `Q₂ = det[x_u|x_v]`, and the Segre quadric
`{Q₂ = 0}` has the two rulings `R_w := w ∧ M = {(αw, βw)}` (`w ∈ L`) and
`R^y := y ∧ W = {(αw, βw) : w ∈ W}` for fixed `y = αe₁ + βe₂ ∈ M` (so `R^{p_u} = Π_u`,
`R^{p_v} = Π_v`). Then the generic point of `Y₁ × Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ + 2, 6)`
— i.e. `G = H ∪ ear1` attains there — **if and only if**

- `δ ≤ 4`: `dim A' ≤ 2` and `A'` is not a ruling plane `R^y`, `y ∈ M`;
- `δ = 5`: `dim A' ≤ 3`, equivalently `T₁ ⊄ ⟨M⟩ ⊕ ⟨L⟩`;
- `δ = 6`: always.

Moreover `dim A' = δ − 2 + dim(T₁ ∩ (⟨M⟩ ⊕ ⟨L⟩))`, so the dimension clause is: `δ ≤ 2`:
automatic; `δ = 3`: not both `M, L ∈ T₁`; `δ = 4` or `5`: `T₁ ∩ ⟨M, L⟩ = 0` — **no nonzero
wrench `αM + βL` is transmissible from `u` to `v` through `H`**. By S7, `dim A'` is
`dim M(H ∪ bar(M) ∪ bar(L)) − dim M(H/uv)`.

*Proof.* `S(ϕ)` acts on `L = P(W)` through `C ∈ GL₂`, transitively, so "generic `p_x ∈ L`"
is "generic `g ∈ S(ϕ)`" and the conclusion is the one S5 composes. *Case `δ ≤ 4`.* The
conclusion is `ρ̄₁ ∩ R_w = 0` for generic `w ∈ L`; since `R_w ⊆ Π_u ⊕ Π_v`, this is
`A' ∩ R_w = 0`. `dim A' = 0`: trivial. `dim A' = 1`: a point of `P³ = P(Π_u⊕Π_v)` lies on at
most one line of the ruling `{P(R_w)}` (two lines of one ruling are disjoint). `dim A' = 2`:
a line `ℓ ⊂ P³` not on the quadric meets it in `≤ 2` points, each on exactly one `P(R_w)`;
a line on the quadric is some `P(R_{w₀})` (disjoint from every other `P(R_w)`) or some
`P(R^y)` (meeting every `P(R_w)`, in the point `y ∧ w`). `dim A' ≥ 3`: a plane in `P³`
meets every line. *Case `δ ≥ 5`.* The conclusion is `ρ̄₁ + R_w = Λ²K⁴`, i.e.
`T₁ ∩ R_w^⊥ = 0`. From `Q = Q₁ − Q₂`: `Q(x, w∧e₁) ∝ det[w | x_v]` and `Q(x, w∧e₂) ∝ det[w | x_u]`,
so `R_w^⊥ = ⟨M⟩ ⊕ ⟨L⟩ ⊕ R_w = {x : x_u, x_v ∈ Kw}`. For `δ = 6`, `T₁ = 0`. For `δ = 5`,
`T₁ = Kt` and `t ∈ R_w^⊥` for generic `w` iff `t_u = t_v = 0` iff `t ∈ ⟨M⟩⊕⟨L⟩` iff
`ρ̄₁ ⊇ Π_u ⊕ Π_v` iff `dim A' = 4`. *The dimension formula* is S7(v) with
`(Π_u⊕Π_v)^⊥ = ⟨M⟩⊕⟨L⟩` and `ρ₁ = δ`. Finally `G` attains iff `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6) + a₁ + a₂`
at the configuration (brief §2, re-derived in session 1), with `a₁ = a₂ = 0` at the generic
point. ∎

*Why this matters.* The Lean consumer `hbareSplit` (brief §3) supplies a degree-2 vertex
`x` with neighbours `u ≁ v`; so **the consumed shape is exactly `H = G − x` composed with
`ear1`**, and S9 is that instance of the Lemma with no residue: the whole of O4/O5 for it is
the single statement *"`T(H; u, v) ∩ ⟨M, L⟩ = 0` (or the weaker clause at `δ ≤ 3`) and
`A' ≠ y ∧ W`"* about the transmissible wrenches of `G − x` between the neighbours of `x`,
at generic flags. `A' = Π_u` (i.e. `c₁(Π_u) = 2`) is the case `y = p_u` of the excluded
shape, which is why BEARCASE's "meets each terminal pencil in `≤ 1` dimension" is necessary.
Control: `drivers/earone.py` (below) evaluates both sides of the equivalence exactly on every
side of the battery and on the composed graph `H + x`.

**Verdict.** S6–S9: *proven-informally*. **What would change this:** for S7(ii), a block sum
not spanned by lines (there is none: each block is a line or a pencil); for S9, a side at
which the predicted verdict and the exact rank of `H + x` disagree at a draw
(`earone.py` checks this at every draw).

**Control data (session 2) — `drivers/sideprof.py --side all2`, `drivers/earone.py --side both`
(exact ℚ, seed `20260915`, 6 draws per side, `s = 20`; commands and caps in `drivers/README.md`).**
Twelve sides added to the battery: `theta344`, `theta444`, `theta445`, `theta555` (both
terminals of side-degree 3), `theta4444` (side-degree 4), `hubpend`, `hubpend2` (3 at `u`,
1 at `v`), `hubcyc` (3 at `u`; `v` of side-degree 2 on a rigid 5-cycle), `cross44`, `cross55`
(two interior degree-3 hubs), `theta45`, `theta55`; `δ ∈ {2, 3, 4, 5, 6}`, `dist(u, v)` up to 6,
girth 5–12. At 72/72 draws `ρ = δ`, `H` and `H/uv` attain, and the profile is constant per
side: **no excess on any block for the ten sides with side-degree `≥ 2` at both ends; excess
exactly `Π_v: 1` on `hubpend`, `hubpend2`** — the side-degree-1 hinge, as S6(i) forces. By
S7(vi) each row is a theorem for the component through the draw. `earone.py` on all 23 sides
(138 draws, 3 points `p_x ∈ L` each): S9's predicted verdict equals the exact rank test of
`H + x` at **138/138**, the identities `dim A' = ρ − 2 + dim(T ∩ ⟨M, L⟩)` and
`dim A' = dim M(H + bar M + bar L) − dim M(H/uv)` hold at every draw, no `A'` is a `y ∧ W`
plane, and `T ∩ ⟨M, L⟩ ≠ 0` occurs **only** on the four sides with `dist(u, v) ≤ 3`
(`ear1`: 2, `ear2`: 1, `cycletail`: 1, `dumbbell`: 1), never on the 19 with `dist ≥ 4`.
*Measured law (not a theorem):* at generic `ϕ`, on the attaining + welded-attaining component
of a girth-`≥ 5` side with `dist(u, v) ≥ 4`, no wrench of `⟨M⟩ ⊕ ⟨L⟩` is transmissible —
which is the whole of S9's dimension clause for the consumed shape (`dist ≥ 5` there). The
mechanism is transparent only for paths: a wrench of `⟨M, L⟩` passes every terminal hinge
(`⟨M, L⟩ = (Π_u ⊕ Π_v)^⊥`), and two interior hinges in general position cut the 2-plane to
`0`; for a general side `T` strictly exceeds the path-generated `Σ_P span(P)^⊥`.
