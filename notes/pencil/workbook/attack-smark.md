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
`ear1`** *[review 2026-09-15: not quite — `hbareSplit` also carries
`¬ G.PencilHub a ∨ ¬ G.PencilHub b`, so the consumed `H` has side-degree `1` at one of `u, v`,
and after peeling the whole degree-2 chain the consumed shape is `ear_m`, `m ≥ 2`, against a
hub-terminal side; see S10(iii). S9 stands as a theorem about the one-vertex ear between two
hubs, which the consumer does not take.]*, and S9 is that instance of the Lemma with no residue: the whole of O4/O5 for it is
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

## S10 — Review notes (2026-09-15, `/review-attack` after session 2; the reviewer's claims, not the attack's — verify before building on them)

**(i) A missing sentence in S2's generic-stratum count.** The count bounds
`dim(P(A) ∩ S(ϕ)·y)` by `dim(P(A) ∩ Q_{I(y)})` and treats the case `P(A) ⊆ Q_{I₀}` as confined
to one level set of `I`. If `Q₁|_A ≡ 0 ≡ Q₂|_A` (a *base-locus* subspace: `A ⊆ {x_L = 0}` or
`{x_M = 0}` with `Q₂`-isotropic trace — e.g. `star(y)` for `y ∈ M ∪ L`, `Λ²π` for `π ⊃ M` or
`π ⊃ L`, and every ruling plane `R_w`, `R^y`, in particular `ρ̄(ear1)`), then `P(A) ⊆ Q_I` for
every `I`, and the level-set argument gives only `ρ₁ + ρ₂ − 1`, which is `5` at `ρ₁ + ρ₂ = 6`.
The count still closes, because such an `A` misses `Gen` entirely — `Gen` requires `Q₁ ≠ 0` —
so `I_Gen = ∅` by the tighter bound `(∗)`, `dim(P(A) ∩ S(ϕ)·y) ≤ dim(P(A) ∩ Σ)`; symmetrically
for `B`. S2's statement is unaffected; its proof should say this.

**(ii) The brief's §2 identities, re-derived** (S9 cites "re-derived in session 1" with no
written record). *Gluing:* `M(G)` is the kernel of `M₁ × M₂ → (Λ²K⁴)²`,
`(m₁, m₂) ↦ (m₁(u) − m₂(u), m₁(v) − m₂(v))`; each `M_i` contains the constant screws, so the
image is `{(s, s + r₁ − r₂) : s ∈ Λ²K⁴, r_i ∈ ρ̄_i}`, of dimension `6 + dim(ρ̄₁ + ρ̄₂)`; hence
`dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)`. *Deficiency:* a partition `P` of `V(G)`
restricts to `P₁, P₂`; with `u, v` in one part, `|P| = |P₁| + |P₂| − 1` and
`d(P) = d(P₁) + d(P₂)`, so `count(P) = count(P₁) + count(P₂)`, maximum `g₁ + g₂`; with `u, v`
separated, `|P| = |P₁| + |P₂| − 2`, so `count(P) = count(P₁) + count(P₂) − 6`, maximum
`f₁^sep + f₂^sep − 6`. Hence `def₃(G) = max(g₁ + g₂, f₁^sep + f₂^sep − 6) = f₁ + f₂ − min(δ₁ + δ₂, 6)`
(when `δ_i ≥ 1`, `f_i = f_i^sep`; when `δ_i = 0` the second term is `≤` the first).
*Attainment:* with `dim M_i = 6 + f_i + a_i` and `dim M(G) = 6 + def₃(G) + a(G)`, the two
identities give `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6) + a₁ + a₂ − a(G)`; so `G` attains iff
`dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6) + a₁ + a₂`.

**(iii) The consumed shape, and the chain-length stratification.** `hbareSplit`
(`Escape.lean:467`) carries `¬ G.PencilHub a ∨ ¬ G.PencilHub b` for the two neighbours `a, b` of
the degree-2 vertex `x`; a pencil hub has degree `≥ 3` (`Motive.lean:73`) and 2-edge-connectivity
gives degree `≥ 2`, so one neighbour has degree exactly `2`. Thus `x` lies on a maximal degree-2
chain of `m ≥ 2` interior vertices whose ends `w, v` have degree `≥ 3` (or `G` is a cycle);
`G = H′ ∪ ear_m` at `{w, v}`, with `w ≁ v` (else a cycle of length `m + 2 ≤ 6` on a proper vertex
subset, i.e. a proper rigid subgraph, unless `G` is that cycle), `H′ = G − chain` connected
(2-edge-connectivity), side-degree `≥ 2` at both ends, `dist_{H′}(w, v) ≥ 6 − m` (girth `≥ 7`).
Also: "no proper rigid subgraph ⇒ girth `≥ 7`" fails exactly for `G ∈ {C₅, C₆}` — a spanning
short cycle is not *proper* (`Deficiency.lean:483`); cycles are base case (b) of the brief's
induction.

Apply S5 with side 2 = `ear_m` (S8: fibre irreducible, `ρ₂ = δ₂ = min(m+1, 6)`, attains and
welded-attains, profile from the S5 table) and side 1 = `H′` with `A = ρ̄′`, `ρ₁ = δ′`, at the hub
cut's generic flags. Write the S3 inequality as `c′(U) ≤ dim U + max(0, δ′ + δ₂ − 6) − c₂(U)`.

- **`m ≥ 5`:** `ρ̄₂ = Λ²K⁴` (S8 at `m = 5`; a longer ear contains six lines with at least that
  freedom), so `dim(ρ̄′ + ρ̄₂) = 6 = min(δ′ + 6, 6)`: nothing to prove.
- **`m = 4`** (`ρ₂ = 5`, no excess: `c₂(U) = dim U − 1` for `dim U ≥ 1`): the inequality reads
  `c′(U) ≤ 1 + max(0, δ′ − 1) = max(1, δ′)`, true for every `U` since `c′(U) ≤ δ′`. Exceptions:
  for `δ′ ≥ 2` they are checked on `(A^⊥, B^⊥)`, of dimensions `(6 − δ′, 1)` — (X1) needs two
  3-dimensional spaces, (X3)/(X4) need `c_{B^⊥}(E) ≥ 2`, (X2) needs a `Q₂`-isotropic `A^⊥` of
  dimension `5 > 4` (the maximum for a rank-4 form); at `δ′ = 1` (sum exactly `6`) on `(A, B)`
  of dimensions `(1, 5)` the same four fail. **So for `m = 4` the Lemma holds whenever `H′`
  attains and welded-attains at `(w, v)` — no condition on `H′`'s profile.**
- **`m = 3`** (`ρ₂ = 4`; excess `1` at `Π_w`, `Π_v` only, so `c₂(Π) = 1`, otherwise
  `c₂(U) = max(0, dim U − 2)`): for `dim U ≥ 2`, `U ∉ {Π_w, Π_v}`, the inequality is
  `c′(U) ≤ max(2, δ′)`, trivial; for `dim U = 1` it is `c′(U) ≤ 1 + max(0, δ′ − 2)`, trivial; at
  `U = Π_w` (and `Π_v`) it is `c′(Π_w) ≤ 1 + max(0, δ′ − 2)`, which bites only at `δ′ = 2`:
  **`ρ̄′ ≠ Π_w, Π_v`**. Exceptions: (X4) is avoided because `ρ̄(ear3) ∩ (Π_w ⊕ Π_v) = ⟨L₀, L₃⟩`
  (one line of each terminal pencil, `Q₂ = det[x|y] ≠ 0` generically) is not a ruling plane; (X2)
  is avoided because `Q₂` has rank `4` on `ρ̄(ear3)` (S5 table, Gram `(2, 4, 4)`); (X3), and the
  dual-side (X3)/(X4) at `δ′ ≥ 3`, are finite checks on `ear3`'s fixed `ρ̄` and `T` — not done here.
- **`m = 2`** (`ρ₂ = 3`; excess `1` at `Π_w`, `Π_v`, `Π_w ⊕ Π_v`, `⟨M⟩⊕Π_w`, `⟨M⟩⊕Π_v`,
  `Π_w⊕⟨L⟩`, `Π_v⊕⟨L⟩`, so `c₂ = 1, 1, 2, 1, 1, 1, 1` there and `max(0, dim U − 3)` elsewhere):
  with slack `s = max(0, δ′ − 3)`, `c′(Π_w), c′(Π_v) ≤ 1 + s`; `c′(Π_w ⊕ Π_v) ≤ 2 + s`;
  `c′(⟨M⟩⊕Π), c′(Π⊕⟨L⟩) ≤ 2 + s` at both pencils; every other block is trivial. So at `δ′ ≤ 3`:
  **both terminal pencils met in `≤ 1` dimension, `Π_w ⊕ Π_v` in `≤ 2`, and the two 3-dimensional
  blocks at each pencil in `≤ 2`** (the last bites only at `δ′ = 3`); at `δ′ = 4`:
  `c′(Π_w ⊕ Π_v) ≤ 3` only; at `δ′ ≥ 5` nothing. Plus (X1)–(X4) on the pair (dual at `δ′ ≥ 4`);
  `ρ̄(ear2)`'s trace on `Π_w ⊕ Π_v` is `⟨L₀, L₂⟩`, again not a ruling plane.

*Reading.* The consumed obligation is the `m = 2` list on a side with side-degree `≥ 2` at both
terminals — session 1's "first gap" in its weakest needed form — not the general wrench claim
`T ∩ ⟨M, L⟩ = 0` at `dist ≥ 4`. The general 2-cut Lemma is still what the global induction on
`H′` needs; its needed form is the induction frame's to state (state file, *Worries*).
**Status:** reviewer's arithmetic from S3 + S8 and the S5 table, unverified by the attack and
uncontrolled by a driver; session 3's first step is to check it (state file, *Next steps* 1).

## S11 — Formalization corrections (2026-09-15; the Lean-track design pass, `notes/Phase39-design.md` § *Lean-track design pass* — statements compiler-checked against the tree, proofs not yet built; the brief and state file were amended for these the same day, edits marked *[formalization 2026-09-15]*)

Read `hbareSplit`'s hypotheses (`Escape.lean:573–579`) against the definition bodies
(`IsProperRigidSubgraph`, `Deficiency.lean:483`; `PencilHub`/`closedNbhd`, `Motive.lean:73,95`;
`TwoEdgeConnected`, `Deficiency.lean:1166`; `CycleData`, `Operations.lean:3204`). Four corrections
to S10(iii) and the brief's §3, and the field resolution. Blueprint nodes named are red
(`pencil.tex` § *Girth and degree-two chains under no proper rigid subgraph*).

**(i) Girth: a hub forces it, and the alternative is "a cycle", not "`C₅` or `C₆`".** S10(iii)'s
"no proper rigid subgraph ⇒ girth `≥ 7` fails exactly for `G ∈ {C₅, C₆}`" is true but is not the
split the consumer takes. Pinned (`lem:pencil-short-cycle-spanning`, `lem:pencil-girth-of-hub`):

```lean
theorem Graph.range_vtx_eq_vertexSet_of_cycle_of_noRigid [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 3 ≤ bodyBarDim n) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {m : ℕ} (hm : 3 ≤ m) (hmD : m ≤ bodyBarDim n) {vtx : Fin m → α} {edge : Fin m → β}
    (hvtx : Function.Injective vtx) (hedge : Function.Injective edge)
    (hlink : ∀ i : Fin m, G.IsLink (edge i) (vtx i) (vtx (i + ⟨1, by omega⟩))) :
    Set.range vtx = V(G)
theorem Graph.girthGE_of_noRigid_of_three_le_degree [Finite α] [Finite β] {G : Graph α β}
    [G.Simple] {n : ℕ} (hD : 3 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) {w : α} (hw : 3 ≤ G.degree w) :
    G.GirthGE (bodyBarDim n + 1)
```

Proof shape of the second: a cycle on `m ≤ D = 6` vertices spans (first statement), so a vertex
`w` of degree `≥ 3` lies on it with a third edge `g`; `g` is a chord (not parallel to a cycle edge,
by simplicity), and the two cycles it cuts off have `a + 1, b + 1 ≤ m − 1 < |V|` vertices with
`a + b = m` — non-spanning cycles on `≤ 6` vertices, contradicting the first statement. So in the
consumer's class: **some vertex has degree `≥ 3` ⇒ girth `≥ 7`; no such vertex ⇒ `G` is a cycle
of any length `≥ 5`** (2EC + all degrees 2, item (ii) case (i)), and on a cycle the disjunct
`¬ PencilHub a ∨ ¬ PencilHub b` is automatic. `C₇, C₈, …` are in the habitat too.

**(ii) The consumed shape is a trichotomy — the chain can close at a single hub.** S10(iii)
says the ends `w, v` have degree `≥ 3` "or `G` is a cycle" and then treats `{w, v}` as a 2-cut.
The maximal degree-2 chain through `x` can also return to the *same* hub. Pinned
(`lem:pencil-degree-two-chain`; `WList` paths, the E2d ladder's carrier):

```lean
theorem Graph.cycleData_or_hubLollipop_or_hubChain_of_degree_two_pair [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] (h2ec : G.TwoEdgeConnected)
    {v a b : α} {eₐ e_b : β} (hdeg : G.degree v = 2) (hne : eₐ ≠ e_b)
    (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b) (hab : G.degree a = 2 ∨ G.degree b = 2) :
    Nonempty G.CycleData ∨
    (∃ C : WList α β, G.IsCyclicWalk C ∧ 3 ≤ G.degree C.first ∧
      (∀ x ∈ C, x ≠ C.first → G.degree x = 2) ∧ v ∈ C ∧ 3 ≤ C.length) ∨
    (∃ P : WList α β, G.IsPath P ∧ 3 ≤ G.degree P.first ∧ 3 ≤ G.degree P.last ∧
      (∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) ∧ v ∈ P ∧ 3 ≤ P.length)
```

*Witness for the middle case, verified:* `G` = two 7-cycles `C, C′` sharing one vertex `w`
(`|V| = 13`, `|E| = 14`, `deg w = 4`, all other degrees `2`). Simple: yes. 2-edge-connected: for a
nonempty proper `V′`, if `V′ ∩ V(C)` is a nonempty proper subset of `V(C)` the cycle `C` alone
crosses it `≥ 2` times; otherwise `V′ ∩ V(C) ∈ {∅, V(C)}`, which forces `V′ ∩ V(C′)` to be a
nonempty proper subset of `V(C′)` (if `V′ ⊇ V(C)` then `w ∈ V′` and `V′ ≠ V(G)`; if
`V′ ∩ V(C) = ∅` then `w ∉ V′` and `V′ ≠ ∅`), so `C′` crosses it `≥ 2` times. No proper rigid
subgraph: a proper subgraph `H` with `|V(H)| = k ≥ 2` has `|E(H)| ≤ k` if it contains one of
the heptagons (it cannot contain both and stay proper) and `|E(H)| ≤ k − 1` otherwise; the
all-singletons partition gives `def(H̃) ≥ 6(k − 1) − 5k = k − 6 ≥ 1` in the first case (`k ≥ 7`)
and `≥ 6(k − 1) − 5(k − 1) = k − 1 ≥ 1` in the second, so `H` is not `0`-dof. A degree-2 vertex
`x` at distance 2 from `w` on `C` has two degree-2 neighbours, so the disjunct holds; its
maximal chain runs both ways to `w`: the closed walk `w u₁ … u₆ w` of length `7` — case (ii),
not a 2-separation. The brief's Lemma is stated for a 2-separation of a **2-connected** `G`
(§1) and does not apply; the induction's cut-vertex case (d) is the informal owner. **PI decision
pending** on the frame's treatment of this case (`notes/Phase39.md` *Blockers*).

**(iii) `w ≁ v` only for `m ≤ 4`.** What girth gives is the side-distance bound, pinned
(`lem:pencil-chain-side-connected`, `lem:pencil-chain-side-distance`):

```lean
theorem Graph.connected_deleteVerts_interior_of_twoEdgeConnected [Finite β] {G : Graph α β}
    [G.Loopless] (h2ec : G.TwoEdgeConnected) {P : WList α β} (hP : G.IsPath P)
    (hlen : 1 ≤ P.length) (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) :
    (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).Connected
theorem Graph.degree_deleteVerts_interior_add_one [Finite β] {G : Graph α β} [G.Loopless]
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) :
    (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).degree P.first + 1 = G.degree P.first
theorem Graph.le_length_add_length_of_isPath_deleteVerts_interior_of_noRigid [Finite α] [Finite β]
    {G : Graph α β} [G.Simple] {n : ℕ} (hD : 3 ≤ bodyBarDim n)
    (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    {P : WList α β} (hP : G.IsPath P) (hlen : 2 ≤ P.length)
    (hdeg : ∀ x ∈ P, x ≠ P.first → x ≠ P.last → G.degree x = 2) (hfirst : 3 ≤ G.degree P.first)
    {Q : WList α β} (hQ : (G - {x | x ∈ P ∧ x ≠ P.first ∧ x ≠ P.last}).IsPath Q)
    (hQf : Q.first = P.first) (hQl : Q.last = P.last) :
    bodyBarDim n + 1 ≤ P.length + Q.length
```

With `P.length = m + 1` and `D = 6`: every `w`–`v` path in `H′` has `≥ 6 − m` edges, i.e.
`dist_{H′}(w, v) ≥ 6 − m` as S10(iii) says; a `wv` edge is a side path of length `1`, excluded
exactly when `6 − m ≥ 2`. **At `m ≥ 5` adjacency is allowed** — harmless, since S10 needs nothing
at `m ≥ 5`, but the brief's unconditional `w ≁ v` was an overclaim. Side-degree `≥ 2` at both ends
is `deg − 1 ≥ 2` (the second statement), and `H′ = G − chain` is connected without any hub
assumption (the first).

**(iv) The neighbourhood bound needs only girth `≥ 5` and `v ≠ h`.** Not hubness, not
simplicity (`lem:pencil-closed-nbhd-girth-five`): three shared members force a triangle if
`v ~ h` and a 4-cycle otherwise, edges distinct by their endpoint pairs.

```lean
theorem Graph.ncard_closedNbhd_inter_le_two_of_girthGE [Finite α] {G : Graph α β}
    (hg : G.GirthGE 5) {v h : α} (hvh : v ≠ h) :
    (G.closedNbhd v ∩ G.closedNbhd h).ncard ≤ 2
```

Here `Graph.GirthGE G g` is the pinned predicate "no cycle on `m` vertices with `3 ≤ m < g`"
(`Fin m` data, injective vertices and edges, cyclic links; `def:girth`).

**(v) The field.** Settled by the PI (option C, 2026-09-15; `notes/Phase39-design.md`
§ *Field-hypothesis recon*, `fmlnote:pencil-conditional-realization-pair-field`): the Lean
reduction stays `[Infinite K]`. *This route needs no characteristic at all*; S1–S9 use a factor
`2` only cosmetically (define `Q := Q₁ − Q₂` directly) and the Klein pairing is nondegenerate in
every characteristic. Its genuine field item is that it argues over an algebraically closed field
(generic points of irreducible components), and descending "generic point" statements to
`K`-points is not automatic — to be settled together with the induction-frame decision by
restating the frame in witness form over `K` (S7(vi): one exact configuration certifies
attainment, welded attainment and the `c(U)` bounds; `S(ϕ)` is `K`-split with dense `K`-points).
Kernel (K-bare)'s Lean lemma is expected with `[Infinite K]` in that form, `IsAlgClosed K` in
the interim. (For the grid route to `hK`, the same recon finds `char K ≠ 2` and nothing more;
the characteristic-2 probe is the (GR-10) attack's, `notes/attacks/gr10/brief.md` §6 item 4.)

## S12 — Verification of S10, and the K4-minor adversarial frontier (session 3, 2026-09-16)

Session 3's charge (state file *Next steps* 1): verify S10's chain-length arithmetic
against S3 + S8, then push the `m = 2` profile bounds into the population S8 could not
reach — girth-`≥ 7` sides with a **K4 minor** (not series-parallel; the state file's
"no 3-connected chunk" gap). Two new drivers, exact ℚ, seed `20260916`, caps in
`drivers/README.md`.

**(i) S10's arithmetic is correct (checked by hand, block by block).** Writing the S3
inequality as `c′(U) ≤ dim U + max(0, δ′ + δ₂ − 6) − c₂(U)` with `c₂` the S8 profile of
`ear_m` (`δ₂ = min(m+1, 6)`):
- **`m ≥ 5`** (`ρ̄₂ = Λ²K⁴`): `dim(ρ̄′ + ρ̄₂) = 6` unconditionally.
- **`m = 4`** (`c₂(U) = dim U − 1`, `dim U ≥ 1`): every inequality is `c′(U) ≤ max(1, δ′)`,
  true since `c′(U) ≤ δ′`; the four exceptions fail on `(A^⊥, B^⊥)` (dims `(6−δ′, 1)`) for
  `δ′ ≥ 2` and on `(A, B)` (dims `(1, 5)`) at `δ′ = 1`. **No condition on `H′`.**
- **`m = 3`** (`c₂(Π) = 1`, else `max(0, dim U − 2)`): the only binding inequality is
  `c′(Π_w), c′(Π_v) ≤ 1 + max(0, δ′−2)`, which bites **only at `δ′ = 2`**: `ρ̄′ ∉ {Π_w, Π_v}`.
  (`Π_w ⊕ Π_v` and the two 3-dim blocks are all `≤ 2 + s`, automatic since `c′ ≤ δ′`.)
- **`m = 2`** (`c₂ = 1,1,2,1,1,1,1` at `Π_w, Π_v, Π_w⊕Π_v, ⟨M⟩⊕Π_w, ⟨M⟩⊕Π_v, Π_w⊕⟨L⟩, Π_v⊕⟨L⟩`,
  else `max(0, dim U − 3)`; slack `s = max(0, δ′−3)`): binding are `c′(Π_w), c′(Π_v) ≤ 1+s`;
  `c′(Π_w⊕Π_v) ≤ 2+s`; `c′(⟨M⟩⊕Π), c′(Π⊕⟨L⟩) ≤ 2+s`. So at `δ′ ≤ 3`: both terminal pencils
  met in `≤ 1`, `Π_w⊕Π_v` in `≤ 2`, the two 3-dim blocks in `≤ 2` (last bites at `δ′ = 3`);
  at `δ′ = 4`: `Π_w⊕Π_v ≤ 3` only; at `δ′ ≥ 5` nothing. **This confirms S10 exactly.**

**(ii) S10 confirmed end-to-end — `drivers/earcompose.py`.** For side 1 in the
14-member hub-terminal battery (`theta33..theta555`, `theta4444`, `cross44/55`, `hubcyc`,
`dumbbell` — side-degree `≥ 2` at both terminals) and `m ∈ {2, 3, 4}`: the composed
`G = H′ ∪ ear_m` at generic flags. Per draw the driver samples both sides, asserts the
**2-cut deficiency law** `def₃(G) = f₁ + f₂ − min(δ₁+δ₂, 6)` (exact `d3`), computes the
gluing prediction `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂, 6)`, evaluates the S3 block criterion, and
compares against the **exact rank** of the combined pencil configuration
`rk R(G) = 6|V(G)| − 6 − def₃(G)`. At **252/252 draws** (`--seed 20260916 --draws 6
--ears 2,3,4 --side hub`): 2-cut law holds, S3 criterion `⟺` actual attainment,
predicted `=` actual, **no side ever exceeds S10's per-block bound on `c′`**. Each draw
is an exact witness (S7(vi)), so each row is a theorem for the component through it.

**(iii) The K4-minor adversarial frontier — `drivers/adversarial.py`.** The consumed
`H′ = G − chain` inherits girth `≥ 7` from `G`, so a genuine "3-connected chunk" means a
**topological `K4`** (subdivided `K4`, the minimal non-series-parallel graph). Sides:
`sk4_d2, sk4_d3, sk4_d4` = `K4` on `{u,v,p,q}` (`u, v` the terminals, `p, q` interior
hubs) with edges `(uv,up,uq,vp,vq,pq)` subdivided to lengths `(4,3,3,3,3,4)`,
`(3,3,3,4,4,4)`, `(4,3,3,4,4,4)` (girth 10, `|V| = 18,19,20`, `δ = 2,3,4`); `prism` =
subdivided triangular prism (girth 9, `|V| = 24`, `δ = 3`). At 6 draws each, all attain
and welded-attain; the terminal-pencil profile is (u ↔ w):

| side | `δ′` | `c′(Π_w)` | `c′(Π_v)` | `c′(Π_w⊕Π_v)` | `c′(⟨M⟩⊕Π)`, `c′(Π⊕⟨L⟩)` | S10 `m=2` bound |
|---|---|---|---|---|---|---|
| `sk4_d2` | 2 | 0 | 0 | 0 | 0 | `1,1,2` — **slack** |
| `sk4_d3`, `prism` | 3 | **1** | **1** | **2** | 1 | `1,1,2` and 3-dim `≤2` — **tight, holds** |
| `sk4_d4` | 4 | 1 | 1 | 2 | 0 | `Π_w⊕Π_v ≤ 3` — **holds** |

**Reading.** The series-parallel thetas (S8) had `c′(Π_w) = 0`; the **K4-minor sides
saturate S10's bound at `c′(Π_w) = 1` (never exceed it)** once `δ′ ≥ 3`. So the bound
`c′(Π_w) ≤ 1` is *tight* — the non-series-parallel structure genuinely puts one relative
screw into the terminal pencil, which is exactly why S10 needs `≤ 1`, not `= 0` (S8's
value). Composing these K4-minor sides with `ear_{2,3}` (`earcompose --side sk4_d*`): the
consumed graph attains at every draw, S3 criterion `⟺` actual, no bound exceeded. These
are the first witnesses (theorems for their components, S7(vi)) that the `m = 2`/`m = 3`
profile bounds hold on a side with a K4 minor and three interior hubs.

**Sharpened target (replaces the state file's "no proof for a side with an interior
hub").** By S7, `c′(Π_w) = max(0, δ′−4) + exc(Π_w)`, `exc(Π_w) =` attainment loss of the
**four-bar framework** `H′ ∪ bars(Π_w^⊥)` (bars `M`, `L`, two lines of `Π_w` between
bodies `w, v`). The measured `c′(Π_w) ≤ 1` at `δ′ ≤ 5` is exactly `exc(Π_w) ≤ 1`. The
open obligation O4, in its weakest consumed form, is therefore:

> **(O4′)** For a girth-`≥ 7` side `H′` with side-degree `≥ 2` at both hub terminals, at
> generic `ϕ` on the attaining + welded-attaining component: the four-bar framework
> `H′ ∪ bars(Π_w^⊥)` loses **at most one** dof against its Tay count (`exc(Π_w) ≤ 1`),
> and symmetrically at `v`; and `H′ ∪ bars(M) ∪ bars(L)` loses `≤ 0` beyond the count
> forcing `c′(Π_w⊕Π_v) ≤ 2` at `δ′ ≤ 3`.

Measured `= 1` on every K4-minor and prism draw at `δ′ ≥ 3`, `= 0` on every
series-parallel draw. **Not a theorem** — the population is the four named K4/prism sides
plus the 23 battery sides, at the caps disclosed; "`exc(Π_w) ≤ 1` never violated" is *not
found above 1*, not proved for the class.

**Verdict.** S10: *verified* (arithmetic by hand in (i); end-to-end control in (ii)). The
adversarial probe (iii) **does not refute** the `m = 2` clean form and sharpens O4 to
(O4′), a bar-augmented attainment-loss bound of exactly one. **What would change this:**
a girth-`≥ 7` hub-terminal side with `c′(Π_w) ≥ 2` (or `c′(Π_w⊕Π_v) ≥ 3` at `δ′ ≤ 3`) at
generic `ϕ` on its attaining+welded component — none found in `sk4_d*`, `prism`, or the
23-side battery.

## S13 — Composition at the cut, the ear-in-disguise diagnosis, irreducibility at hub-distance `≥ 2`, and the short-path kill (session 4, 2026-09-16)

Session 4's charge (state file *Next steps* 1–2): attack `exc(Π_w) ≤ 1` (O4′) on the
K4-minor family where it was measured tight, and widen the adversarial net. Both were
done and the picture changed: the K4-minor "frontier" is an ear in disguise, the
consumed obligation decomposes over the pieces of `H′` at the cut, and the genuine
remainder is a single piece all of whose `w`–`v` paths have `≥ 6` lines. Drivers
`pencilline.py`, `census.py`, `specialcfg.py` (exact ℚ, seed `20260916`, caps in
`drivers/README.md`).

**(i) Diagnosis — the tight `c′(Π_u) = 1` of S12(iii) is S8's ear line.** `pencilline.py`
computes the line `ρ̄′ ∩ Π_u` on `sk4_d3`, `sk4_d4`, `prism` and the motion realising it.
At 6/6 draws the line is the hinge `L_{ux}`, `x` the first vertex of the *direct* `u`–`v`
branch, and in the motion every hinge of that branch except `L_{ux}` is inactive: the branch
is welded to `v` and rotates about `L_{ux}` (symmetrically at `v`). Reason, by (ii): with
`H″ :=` the side minus that branch, `(f, g, δ)(H″) = (6, 0, 6)` for all three
(`d3`/`weld_d3`), so `ρ̄(H″) = Λ²K⁴` and `ρ̄′ = ρ̄(H″) ∩ span(P) = span(P)` — the `ear2`
profile `(1,1,2,1,1,1,1)` for `sk4_d3`, `prism` and the `ear3` profile for `sk4_d4`, exactly
the S12(iii) table. **S12(iii)'s reading ("the non-series-parallel structure puts one
relative screw into the pencil") is withdrawn:** the K4 chunk is fully flexible and
contributes nothing; the pencil line is the ear's. Only `sk4_d2` (`δ(H″) = 4`) is genuinely
mixed, and it has `c′(Π_u) = 0`.

**(ii) Proposition (composition of `ρ̄` at the cut).** Fix a configuration of a side `H` at
flags `ϕ`, terminals `w ≁ v`.
- **(a) Parallel.** If `H − {w, v}` has components `C₁, …, C_k` and `H_j := H[C_j ∪ {w, v}]`
  (the *pieces*), then `ρ̄_{wv}(H) = ∩_j ρ̄_{wv}(H_j)`, and `δ(H₁ ∪ H₂) = max(0, δ₁ + δ₂ − 6)`.
- **(b) Series.** If `z` is a cut vertex of `H` separating `w` from `v`, `H = H_a ∪_z H_b`
  (`w ∈ H_a`, `v ∈ H_b`), then `ρ̄_{wv}(H) = ρ̄_{wz}(H_a) + ρ̄_{zv}(H_b)`.
- **(c) Monotonicity.** For a subgraph `H₀ ⊆ H` containing `w, v`: `ρ̄_{wv}(H) ⊆ ρ̄_{wv}(H₀)`,
  hence `c_H(U) ≤ c_{H₀}(U)` for every block sum `U`.

*Proof.* (a) A motion of `H` is a tuple of motions of the `H_j` agreeing at `w` and at `v`
(the pieces share no other vertex and no edge). Normalise `m(w) = 0`; then `m(v) ∈ ρ̄(H_j)` for
all `j`. Conversely for `r` in the intersection pick `m_j ∈ M(H_j)` with `m_j(w) = 0`,
`m_j(v) = r` and glue. For `δ`: `f = f₁ + f₂ − min(δ₁ + δ₂, 6)` (S10(ii)) and `g = g₁ + g₂`
(a partition with `w, v` together restricts to the pieces and its count adds). (b) Motions
of `H` are pairs agreeing at `z`; `m(v) − m(w) = (m_b(v) − m_b(z)) + (m_a(z) − m_a(w))` with
the summands chosen independently. (c) A motion of `H` restricts to a motion of `H₀`. ∎

*Reading.* `c_H(Π_w) = dim ∩_j (ρ̄_j ∩ Π_w) ≤ min_j c_j(Π_w)`: **the consumed bound
`c′(Π_w) ≤ 1` holds as soon as one piece fails to contain `Π_w`**, and likewise for every
block. In the SPQR tree of `H + wv`: P-nodes intersect, S-nodes add, and the content sits in
the R-nodes (subdivided 3-connected skeletons carrying the virtual edge `wv`). The multi-piece
case also gets the gauge for free — `S(ϕ)` acts on each piece's configuration independently,
so `ρ̄′ = ρ̄₁ ∩ g ρ̄₂` for generic `g ∈ S(ϕ)` and S2–S3 give its *dimension* from the pieces'
profiles; what S2 does not give is the block profile of the intersection (see (viii)).

**(iii) Corollary (an ear piece discharges the `m = 2` list).** If some piece `H_j` is a
path of length `k ≤ 5` (an ear of `H` between `w` and `v`; `k ≥ 4` in the consumed shape,
`dist_{H′}(w, v) ≥ 4`), then at the generic point of *every* component of `Y°(H; ϕ)`:
`c(Π_w), c(Π_v) ≤ 1`; the four 3-dimensional blocks `≤ k − 3 ≤ 2`; `c(Π_w ⊕ Π_v) ≤ k − 2`
(`= 2` for `k = 4`; `3` for `k = 5`). *Proof.* The ear's interior vertices meet the rest of
`H` only at `w, v` and their constraints are `p_{first} ∈ π_w`, `p_{last} ∈ π_v`, so
`Y°(H; ϕ) = Y°(H − int(P); ϕ) × Y°(P; ϕ)` up to open conditions; `Y°(P; ϕ)` is irreducible
(S8), so every component is `Y′ × Y°(P;ϕ)` and its generic point has a generic ear. Apply
(ii)(c) with `H₀ = P` and S8's `ear_{k−1}` profile. ∎ So an ear piece of length 4 discharges
the whole S10 `m = 2` list; one of length 5 discharges all but `c′(Π_w ⊕ Π_v) ≤ 2` at `δ′ = 3`.

**(iv) Proposition (irreducible fibre when hubs are pairwise non-adjacent — S8 extended).**
If no two vertices of degree `≥ 3` are adjacent in `H` (every branch has length `≥ 2`), then
`Y°(H; ϕ)` is irreducible. *Proof.* Tower. Base `B := ∏_{interior hubs z} {(p_z, π_z) :
p_z ∈ π_z}`, irreducible (the terminal flags are fixed by `ϕ`). Over a point of `B` the
remaining coordinates are the branch interiors: for a branch `z, y₁, …, y_{k−1}, z′` with
`k ≥ 2`, `p_{y₁} ∈ π_z`, `p_{y_{k−1}} ∈ π_{z′}`, the other `p_{y_i}` free (`k = 2`: the single
point lies on `π_z ∩ π_{z′}`), and these are *all* the constraints of a pencil configuration
— a degree-2 vertex's plane is the plane of its three points, and a hub's plane is `π_z` once
its neighbours lie in it. Over the dense open `B° ⊆ B` on which the two end-planes of every
length-2 branch differ, the fibre is an open subset of a product of linear spaces of constant
dimension, so the part of `Y°` over `B°` is irreducible; a point over `B ∖ B°` (`π_z = π_{z′}`,
`p_y` anywhere in the common plane) is a limit of points over `B°` — rotate `π_{z′}` about the
line `p_{z′} p_y ⊆ π_z`, so that `π_z ∩ π_{z′}` contains `p_y` throughout. Hence `Y°(H; ϕ)` is
irreducible (the auxiliary `π_z` are functions of the points on the open set where each hub's
closed star spans a plane). ∎ *Consequences.* Every row of `census.py` (all lengths `≥ 2`) is
a theorem for its side, not for a component (S7(vi)); and for such sides the frame's
"attaining + welded component" is the whole fibre. Not covered: sides with adjacent hubs
(allowed at girth `≥ 7`) — a hub with three earlier-placed hub neighbours forces a concurrency
condition and the tower stops; the state file keeps this as a worry.

**(v) Corollary (the short-path kill).** Let `H` have pairwise non-adjacent hubs, girth `≥ 7`,
`w ≁ v`, and `k := dist_H(w, v) ∈ {4, 5}`. Then at the generic point of `Y°(H; ϕ)`:
`c(Π_w), c(Π_v) ≤ 1`; `c(⟨M⟩⊕Π), c(Π⊕⟨L⟩) ≤ k − 3`; `c(Π_w ⊕ Π_v) ≤ k − 2`. In particular
the consumed `m = 2` list holds except `c(Π_w ⊕ Π_v) ≤ 2` at `(k, δ) = (5, 3)`; and `δ ≤ k`.
*Proof.* Let `P` be a shortest path; `ρ̄ ⊆ span(P)` (telescoping along `P`). Order the tower
of (iv) with the chain of `P` first — first point in `π_w`, last in `π_v`, the rest free; a hub
on `P` takes as plane the span of its two `P`-lines. No hub off `P` is adjacent to a vertex of
`P` (its `P`-neighbour would have degree `≥ 3`, hence be a hub — excluded; the terminals are
either hubs or have their planes prescribed). A degree-2 vertex off `P` adjacent to `y_i ∈ P`
is placed afterwards in `π_{y_i}`; it cannot be adjacent to two vertices of `P` (a cycle of
length `|i − j| + 2 ≤ k + 2 ≤ 7` forces `{y_i, y_j} = {w, v}`, a common neighbour,
contradicting `k ≥ 4`); a longer chord path between vertices of `P` has its interior placed
after its end-planes. So the chain moduli of `P` is a free factor at the bottom of the tower,
the projection `Y°(H; ϕ) → (chain moduli)` is dominant, and (irreducibility) the generic point
of `Y°` has a generic chain. Then (ii)(c) with `H₀ = P` and the `ear_{k−1}` profile of S8:
`k = 4`: `(c(Π), c(Π⊕Π), 3-dim) = (1, 2, 1)`; `k = 5`: `(1, 3, 2)`. ∎

**(vi) The census — `census.py` (each row a theorem for its side by (iv) + S7(vi)).** Girth-`≥ 7`
sides from thirteen skeleton families, every skeleton edge subdivided with lengths in
`{2, 3, 4}` (seeded), kept when `dist(u, v) ≥ 4`, `δ ∈ {2, 3, 4}`, `|V| ≤ 32`, three sides per
`(skeleton, δ)`, two draws each: `K4−e`; `K4-tail`, `K4−e-tail` (a bridge `u – x` into the
chunk: side-degree 1 at `u`); `K₃,₃`, `K₃,₃ − e`; prism with `u, v` on the same / on different
triangles; cube at skeleton distance 2 / 3; Wagner `V8`; `K₅ − e`; wheel `W₅`; Petersen (no
member survived the caps). **`ROWS: 200`, `FLAGGED: 0`** — no row exceeds S10's `m = 2` bound.
Per row, with `u ↔ w`:
- single pieces, side-degree `≥ 2` at `u`: `c(Π_u) = 0` at every row with `δ ≤ 3`; at `δ = 4`,
  `c(Π_u) = 1` exactly when `dist = 4` (then `ρ̄ = span(P₄)` by dimension — the `ear3` profile)
  and `0` otherwise; `c(Π_u ⊕ Π_v) = max(0, δ − 2)`, the 3-dim blocks `max(0, δ − 3)`,
  `c(⟨M⟩) = c(⟨L⟩) = 0` — **no excess at any block**;
- a bridge at `u` (`K4-tail`, `K4−e-tail`): `c(Π_u) = 1` (S6's `L_{ux}`), `c(Π_v) = 0`,
  `c(Π_u ⊕ Π_v) = max(1, δ − 2)` (the same line), the rest generic;
- the two-piece `K₃,₃ − e` rows follow the intersection of (ii)(a).
Reading: on this population excess at a terminal pencil arises only from a bridge or from
`δ = dist ≤ 5` (where `ρ̄` *is* a path span). Not a theorem for the class — population and
caps as disclosed (README).

**(vii) `specialcfg.py` — the pointwise form on the minimal uncovered instance.** `K4−e` with
lengths `(4, 2, 3, 4, 2)`: `|V| = 14`, girth 8, `dist = 6`, `δ = 3`, `g = 0` (the welded side
is rigid). Nine families of special interior-hub placements, pinned through the sampler's
`fixed` flags: (a) `p_p ∈ π_u` and `p_u ∈ π_p`; (b) `p_p, p_q ∈ π_u`; (c) `p_u ∈ π_p`; (d) the
four hub points coplanar; (e) `p_p ∈ L`; (f) `π_p = π_q`; (g) `p_p ∈ M`; (h) `π_p = π_u`;
(i) `π_p = π_q = π_u`. Three draws each: at (a)–(h) `c(Π_u) = 0`, attaining and welded-attaining;
at (i) the side stops attaining (`ρ = 4 > δ`), the welded side still attains, and `c(Π_u) = 1`.
`Π_u` is never contained — on these loci the target holds *pointwise*, with no appeal to
component genericity (a hint toward a structural argument, not a proof).

**(viii) Sharpened target (replaces (O4′)).** By (ii)–(iii) the consumed `m = 2` bounds for
`H′` reduce to the pieces of `H′` at the hub cut; an ear piece of length 4 discharges them all
(length 5: all but `Π_w ⊕ Π_v ≤ 2` at `δ′ = 3`); for a single piece with pairwise non-adjacent
hubs and `dist ≤ 5`, (v) discharges the pencil and 3-dim bounds. What remains:

> **(O4″)** A single piece `H` (`H − {w, v}` connected, no cut vertex separating `w` from
> `v`), `w ≁ v`, girth `≥ 7`, side-degree `≥ 2` at both terminals, **`dist(w, v) ≥ 6` and
> `δ ≤ 3`**: show `ρ̄ ∩ Π_w = 0`. Measured `0` at every such census row (52 rows, 8 skeleton
> families, `dist` 6–7) and at the nine special families of (vii). Equivalently (S7(v)):
> among the `6 − δ ≥ 3` transmissible wrenches — the self-stresses of the welded `H/wv`
> modulo those of `H` — one exerts a nonzero moment about some axis of `Π_w`
> (`T ⊄ Π_w^⊥`). Every `w`–`v` path has `≥ 6` lines, so `span(P) = Λ²K⁴` and no path
> argument applies; sub-sides of a stiff side are floppier ((ii)(c) goes the wrong way), so
> there is no reduction to `K4 − e`; the wrench is cycle-generated. Minimal instance:
> `K4 − e (4,2,3,4,2)`.

Also open: the series case ((ii)(b): `Π_w ⊄ ρ̄_a + ρ̄_b`); `c(Π_w ⊕ Π_v) ≤ 2` at
`(dist, δ) = (5, 3)`; irreducibility for hub-adjacent-hub sides; and, for an `H′` with two or
more non-ear pieces, the *block profile* of `ρ̄₁ ∩ g ρ̄₂` for generic `g ∈ S(ϕ)` (S2 gives its
dimension only) — the composition rule the SPQR view needs at P-nodes.

**Verdict.** O4′ as stated in S12 is *not* the right target: its tight instances were ears.
The consumed obligation is now (O4″) plus the listed side items; every measured instance of
(O4″) has no excess at all, and the pointwise probe finds none either. **What would change
this:** a single piece with `dist ≥ 6`, `δ ≤ 3`, side-degree `≥ 2` at `w` and `c(Π_w) ≥ 1` on
its (irreducible, by (iv)) fibre — none found in the census.

## S14 — Theorem (the consumed step closes from the split-off antecedent: `ear_{m−1} ⟹ ear_m`; (O4″) is not consumed) (session 5, 2026-09-16)

Session 5's charge was (O4″) on `K4−e (4,2,3,4,2)` by hand. Before attacking it the session
re-read what the Lean consumer actually *gives*: `hbareSplit` and `hK` (`Escape.lean:334–430`)
both carry the antecedent `HasPencilRealization K 3 (G.splitOff x a b e₀)` — and
`splitOff x a b e₀` deletes the degree-2 vertex `x` and joins its two neighbours by a fresh
edge (`Molecular/Induction/Operations.lean:770`). For `G = H′ ∪ ear_m` (the trichotomy's case
(iii), S11; `x` any interior vertex of the chain) that graph is **`G₋ := H′ ∪ ear_{m−1}`**: the
same side with the ear one shorter. The brief (§3, §5) had discarded this antecedent, reading it
as "a realization of `G − x` into which `x` must be placed". Used as a *certificate for the
generic point* instead of as a configuration to extend, it supplies every block inequality
S10 needs, at every consumed `m`, and the welded hypothesis with it. Dispatch
(`pencilPair_of_splitOff_of_habitat`, `Escape.lean:412–430`): `hbareSplit` fires when
`¬ PencilNondegFeasible K G`, `hK` otherwise, fed `HasGenericPencilRealization K 3 (G.splitOff …)`
from the IH; neither arm receives the IH itself.

**Setting.** Generic flags `ϕ` at the hub cut `{w, v}`, `w ≁ v`; `Y` an irreducible component of
`Y°(H′; ϕ)`; at its generic point `a′`, `a′_w` the attainment losses of `H′`, `H′/wv`, and
`ρ′ = δ′ + a′ − a′_w` (brief §2). `ρ̄_k := ρ̄(ear_k)` at a generic ear: `(k+1)`-dimensional for
`k ≤ 5`, `ear_k` attains and welded-attains, profile from S8 (`Y°(ear_k; ϕ)` irreducible, S8).
`ear_k` has `δ = k + 1`. By S5, a generic ear is a generic gauge translate `g·ear₀`.

**(i) Lemma (what `G₋` attaining says about `H′`).** `G₋` attains at the generic point of
`Y × Y°(ear_{m−1}; ϕ)` iff
- `δ′ + m ≤ 6`: `a′_w = 0` **and** `ρ̄′ ∩ ρ̄_{m−1} = 0` (hence `ρ′ + m ≤ 6`, i.e. `δ′ + a′ ≤ 6 − m`);
- `δ′ + m > 6`: `a′ = 0` **and** `ρ̄′ + ρ̄_{m−1} = Λ²K⁴`.

*Proof.* S10(ii): `G₋` attains iff `dim(ρ̄′ + ρ̄_{m−1}) = min(δ′ + m, 6) + a′` (`a(ear) = 0`); the
left side is `ρ′ + m − dim(ρ̄′ ∩ ρ̄_{m−1}) ≤ min(6, ρ′ + m)`. If `δ′ + m ≤ 6` the equation reads
`δ′ + a′ − a′_w + m − dim ∩ = δ′ + m + a′`, i.e. `dim ∩ = −a′_w`, so both vanish. If `δ′ + m > 6`
the right side is `6 + a′ ≤ 6`, forcing `a′ = 0` and the sum full. ∎

**(ii) Lemma (the same for `G`).** `G` attains at the generic point of `Y × Y°(ear_m; ϕ)` iff
`dim(ρ̄′ + g ρ̄_m) = min(δ′ + m + 1, 6) + a′` for generic `g ∈ S(ϕ)`; so only if
[`δ′ + m + 1 ≤ 6`: `a′_w = 0`, `ρ̄′ ∩ gρ̄_m = 0`, `δ′ + a′ ≤ 5 − m`] or [`δ′ + m + 1 > 6`: `a′ = 0`].

**(iii) Theorem.** *Assume `H′` attains at the generic point of `Y` (`a′ = 0`) and `G₋` attains
at the generic point of `Y × Y°(ear_{m−1}; ϕ)`. Then `G` attains at the generic point of
`Y × Y°(ear_m; ϕ)`.* No further condition on `H′` — in particular no profile bound — is used.

*Proof, by `m`.* Coordinates as in the header: `p_w = e₁`, `p_v = e₂`, `W = ⟨e₃, e₄⟩ = L`,
`x = (x_M; x_u; x_v; x_L)`, `Q₁ = x_M x_L`, `Q₂ = det[x_u | x_v]`, `Q = Q₁ − Q₂`.

*`m ≥ 5`.* `ρ̄_m = Λ²K⁴`, so `dim(ρ̄′ + ρ̄_m) = 6 = min(δ′ + m + 1, 6) + a′`. (The antecedent is not
used; only `a′ = 0`.)

*`m = 4`* (`ρ̄₄` 5-dimensional, `c₄(U) = dim U − 1` for `dim U ≥ 1`). If `δ′ = 0` then `ρ̄′ = 0`
and `dim(ρ̄′ + ρ̄₄) = 5 = min(5, 6)`. If `δ′ ≥ 1` we need `ρ̄′ + gρ̄₄ = Λ²`, i.e. `T′ ∩ gT₄ = 0`
(S3), `T₄ = ρ̄₄^⊥` a line. By (i) with `ear₃`: for `δ′ ≤ 2`, `a′_w = 0` and `ρ′ = δ′ ≥ 1`; for
`δ′ ≥ 3`, `ρ̄′ + ρ̄₃ = Λ²` gives `ρ′ ≥ 2`. So `ρ′ ≥ 1` and S2 applies to `(T′, T₄)`, dimensions
`(6 − ρ′, 1)`: (B) is `c′(U) + c₄(U) ≤ dim U + ρ′ − 1`, i.e. `c′(U) ≤ ρ′`, always true; (X1) needs
two 3-dimensional spaces, (X3)/(X4) need `c_{T₄}(E) ≥ 2`, and (X2) needs `Q₂|_{T′} ≡ 0` on a
space of dimension `6 − ρ′ ≥ 3` together with `6 − ρ′ + 1 = 6`, i.e. `dim T′ = 5 > 4`, the
maximal dimension of a `Q₂`-isotropic subspace (radical `⟨M⟩ ⊕ ⟨L⟩` plus an isotropic 2-plane of
the split form on `Π_w ⊕ Π_v`). Hence `G` attains. (This is S10's "`m = 4` needs only attainment
and welded attainment", with the welded half now *supplied* by (i).)

*`m = 3`* (`ρ̄₃ = span(L₀, L₁, L₂, L₃)`, `L₀ = p_w ∧ p_x ∈ Π_w`, `L₃ = p_{x'} ∧ p_v ∈ Π_v`;
profile `c₃(Π_w) = c₃(Π_v) = 1`, otherwise `max(0, dim U − 2)`, S8). Need
`dim(ρ̄′ + gρ̄₃) = min(δ′ + 4, 6)`. From (i) with `ear₂`: `δ′ ≤ 3` gives `a′_w = 0` and
`ρ̄′ ∩ ρ̄₂ = 0`; `δ′ ≥ 4` gives `ρ̄′ + ρ̄₂ = Λ²`.
- `δ′ ≥ 4`: place the middle vertex `p_y` on the line `p_x p_{x'}` (a point of the irreducible
  ear moduli): then `L_{xy} = L_{yx'} = L_{xx'}` and `span(L₀..L₃) = ρ̄₂(p_x, p_{x'})`, so
  `dim(ρ̄′ + ρ̄₃) = 6` there; `ear ↦ dim(ρ̄′ + span(lines))` is a matrix rank, lower
  semicontinuous, so it is `6` at the generic ear.
- `δ′ = 3`: need the sum full; S3 on `(T′, T₃)`, dimensions `(3, 2)`. (B) is
  `c′(U) + c₃(U) ≤ dim U + 1`, trivial throughout (S12(i)). Exceptions on `(T′, T₃)`: (X1) needs
  `(3, 3)`; (X2) needs sum `6`, here `5`; (X3) needs `c_{T₃}(E) ∈ {2, 3}` for `E = ⟨L⟩^⊥` or
  `⟨M⟩^⊥`, i.e. `T₃ ⊆ E`, i.e. `L ∈ ρ̄₃` resp. `M ∈ ρ̄₃`, but `c₃(⟨L⟩) = c₃(⟨M⟩) = 0`; (X4) needs
  `T₃ ⊆ Π_w ⊕ Π_v = ⟨M, L⟩^⊥`, i.e. `M, L ∈ ρ̄₃`, no.
- `δ′ ≤ 2`: need `ρ̄′ ∩ gρ̄₃ = 0`, `ρ′ = δ′ ≤ 2`. S2 on `(ρ̄′, ρ̄₃)`: (B) binds only at
  `U ∈ {Π_w, Π_v}`, `c′(Π) ≤ 1`, i.e. (at `δ′ = 2`) `ρ̄′ ≠ Π_w, Π_v` (S12(i)); if `ρ̄′ = Π_w` then
  `L_{wx} ∈ ρ̄′ ∩ ρ̄₂`, against (i). Exceptions: (X1) needs `ρ′ = 3`; (X2) needs `Q₂|_{ρ̄₃} ≡ 0`,
  but `ρ̄₃ ∩ (Π_w ⊕ Π_v) ⊇ span(L₀, L₃)` with `Q₂(L₀, L₃) = ½ det[s | s'] ≠ 0` (below); (X3): the
  traces `ρ̄₃ ∩ ⟨L⟩^⊥`, `ρ̄₃ ∩ ⟨M⟩^⊥` (3-dimensional, generic profile) contain `span(L₀, L₃)`, so
  `Q₂` does not vanish on them; (X4): `ρ̄₃ ∩ (Π_w ⊕ Π_v) = span(L₀, L₃)` (generic profile `2`),
  not isotropic, not a ruling plane.

*`m = 2`.* (Klein-orthogonals of the two lines, in coordinates: `⟨L⟩^⊥ = {x_M = 0}`, `⟨M⟩^⊥ = {x_L = 0}`, `⟨M, L⟩^⊥ = Π_w ⊕ Π_v = {x_M = x_L = 0}`.) Write `p_x = αe₁ + s`, `p_{x'} = βe₂ + s'` with `s, s' ∈ W`, `αβ ≠ 0`,
`D := det[s | s'] ≠ 0` (open conditions on the ear moduli). The three lines in block coordinates:

    L₀ = p_w ∧ p_x  = (0; s; 0; 0),   L₂ = p_{x'} ∧ p_v = (0; 0; −s'; 0),
    L₁ = p_x ∧ p_{x'} = (αβ; αs'; −βs; D).

Gram matrices on `ρ̄₂ = span(L₀, L₁, L₂)` in this basis: `Q₁ = diag(0, αβD, 0)` (rank 1);
`Q₂ = [[0, 0, −D/2], [0, αβD, 0], [−D/2, 0, 0]]` (rank 3); `Q = Q₁ − Q₂` rank 2 — the S5
Gram `(1, 3, 2)`. The Klein complement is `T₂ = span(L₁, P₁, P₂)` with `P₁ := p_w ∧ p_{x'} =
(β; s'; 0; 0)`, `P₂ := p_x ∧ p_v = (α; 0; −s; 0)` (each of the three meets all of `L₀, L₁, L₂`:
`L₁` trivially, `P₁` at `p_w`, `p_{x'}`, `P₂` at `p_x`, `p_v`; they are independent since the six
`p_i ∧ p_j` form a basis); `Q₂` on `T₂` in the basis `(L₁, P₁, P₂)`:
`[[αβD, βD/2, αD/2], [βD/2, 0, D/2], [αD/2, D/2, 0]]`. Need `dim(ρ̄′ + gρ̄₂) = min(δ′ + 3, 6)`.
From (i) with `ear₁` (`ρ̄₁ = R_y := y ∧ M = span(L_{wy}, L_{yv})`, `y ∈ L` generic): `δ′ ≤ 4`
gives `a′_w = 0` and `ρ̄′ ∩ R_y = 0`; `δ′ ≥ 5` gives `ρ̄′ + R_y = Λ²`.
- `δ′ ≥ 5`: the degenerate ear with `p_{x'} = y ∈ L` and `p_x` on the line `p_w y ⊂ π_w` has
  `span(L₀, L₁, L₂) = span(p_w ∧ y, y ∧ p_v) = R_y`, so `dim(ρ̄′ + ρ̄₂) = 6` there and, by lower
  semicontinuity over the irreducible ear moduli, at the generic ear.
- `δ′ = 4` (`ρ′ = 4`): need the sum full; S3 on `(T′, T₂)`, dimensions `(2, 3)`. (B) is
  `c′(U) + c₂(U) ≤ dim U + 1`; with the `ear₂` profile the only binding inequality is
  `c′(Π_w ⊕ Π_v) ≤ 3` (S12(i)), and `c′(Π_w ⊕ Π_v) = 4` would mean `ρ̄′ = Π_w ⊕ Π_v ⊇ R_y`,
  against (i). Exceptions on `(T′, T₂)`: (X1) needs `(3, 3)`; (X2) needs sum `6`, here `5`;
  (X3) for `E = ⟨M⟩^⊥ = {x_L = 0}`: `x_L(L₁) = D ≠ 0 = x_L(P₁) = x_L(P₂)`, so `T₂ ∩ E = span(P₁, P₂)`,
  `c_{T₂}(E) = 2`, and `Q₂(P₁, P₂) = D/2 ≠ 0` — not isotropic; for `E = ⟨L⟩^⊥ = {x_M = 0}`:
  `x_M = (αβ, β, α)` on the basis, so `T₂ ∩ E = {λ₁L₁ + λ₂P₁ + λ₃P₂ : αβλ₁ + βλ₂ + αλ₃ = 0}`,
  `c_{T₂}(E) = 2`, and the vector `αP₁ − βP₂` in it has `Q₂ = −2αβ·(D/2) = −αβD ≠ 0` — not
  isotropic; (X4): `T₂ ∩ (Π_w ⊕ Π_v)` needs `x_L = 0` (kills `λ₁`) and `x_M = 0`
  (`βλ₂ + αλ₃ = 0`): one-dimensional, `≠ 2`.
- `δ′ ≤ 3` (`ρ′ = δ′`): need `ρ̄′ ∩ gρ̄₂ = 0`; S2 on `(ρ̄′, ρ̄₂)`. (B) binds at (S12(i)):
  `c′(Π_w), c′(Π_v) ≤ 1`; `c′(Π_w ⊕ Π_v) ≤ 2`; `c′(⟨M⟩ ⊕ Π), c′(Π ⊕ ⟨L⟩) ≤ 2` at both pencils.
  Each failure produces a nonzero vector of `ρ̄′ ∩ R_y` for generic `y`, against (i):
  `c′(Π_w) = 2` means `Π_w ⊆ ρ̄′`, so `L_{wy} ∈ ρ̄′ ∩ R_y`; `c′(Π_w ⊕ Π_v) ≥ 3` means
  `A′ := ρ̄′ ∩ (Π_w ⊕ Π_v)` has dimension `≥ 3` inside the 4-dimensional `Π_w ⊕ Π_v ⊇ R_y`, so
  `A′ ∩ R_y ≠ 0`; `c′(⟨M⟩ ⊕ Π_w) = 3` means `ρ̄′ = ⟨M⟩ ⊕ Π_w ⊇ Π_w`, likewise `Π_w ⊕ ⟨L⟩`.
  Exceptions on `(ρ̄′, ρ̄₂)`, all excluded by `ρ̄₂` alone: (X1): `P(ρ̄₂) ⊆ {Q₁ = I₀Q₂}` needs
  `Q₁ − I₀Q₂ ≡ 0` on `ρ̄₂`; the `(L₀, L₂)` entry `I₀D/2` forces `I₀ = 0`, then the `(L₁, L₁)`
  entry is `αβD ≠ 0` — `ρ̄₂` lies on no member of the pencil; (X2): `Q₂|_{ρ̄₂}` has rank 3;
  (X3): `ρ̄₂ ∩ ⟨L⟩^⊥ = ρ̄₂ ∩ ⟨M⟩^⊥ = span(L₀, L₂)` (only `L₁` has `x_L ≠ 0`, `x_M ≠ 0`), with
  `Q₂(L₀, L₂) = −D/2 ≠ 0`; (X4): `ρ̄₂ ∩ (Π_w ⊕ Π_v) = span(L₀, L₂)`, not isotropic, so not a
  ruling plane (S10 already noted this). ∎

**(iv) Corollary (the consumed step, from two smaller-graph facts).** Let `G` fall in the
trichotomy's case (iii) with `H′` such that `Y(H′)` is irreducible (S13(iv): pairwise
non-adjacent hubs; see (vii) for the hub-adjacent case). If `H′` has an attaining configuration
and `G₋ = G.splitOff` has one (over `K̄`), then `G` attains on a dense open subset of `Y(G)`.
*Proof.* `Y(G₋) → Y(H′)` and `Y(G) → Y(H′)` are fibrations with irreducible fibres (ear points
in prescribed planes), so `Y(G₋)`, `Y(G)` are irreducible; rank is lower semicontinuous, so a
single attaining point makes the generic point attain (S7(vi)); the generic point of `Y(H′)`
lies over a generic flag pair and is the generic point of the irreducible `Y°(H′; ϕ)`; apply
(iii). ∎ Cases (i)–(ii) of the trichotomy: `G` a cycle (`G₋` a shorter cycle; cycles attain —
the `k` hinge lines of a generic pencil `C_k` are independent for `k ≤ 6` and span `Λ²` for
`k ≥ 6`, so `dim M(C_k) = 6 + max(0, k − 6)`), and `G = H″ ∪_w C_{m+1}` at a cut vertex, where
`G₋ = H″ ∪_w C_m` attaining gives `H″` attaining (brief §3(d): additivity at a cut vertex) and
`C_{m+1}` attains. Descent to `K`-points: the attaining locus is dense open in `Y(G)`, a tower of
open subsets of products of projective spaces and linear spaces defined over `K`, whose
`K`-points are dense for infinite `K` (S11(v)).

**(v) The `a′` gap — the kernels need the induction hypothesis on `H′`.** By (i) and (ii),
`G₋` attaining allows `δ′ + a′ ≤ 6 − m`, while `G` attaining needs `a′ = 0` or
`δ′ + a′ ≤ 5 − m`. In the gap `δ′ + a′ = 6 − m`, `a′ ≥ 1`, `G₋` attains generically and `G` fails
**at every configuration of the component**: `dim M(G) ≥ (6 + f′ + a′) + (7 + m) − 6 − 6 =
f′ + a′ + m + 1`, while `6 + def₃(G) = f′ + m + 1 + max(0, 5 − δ′ − m) = f′ + m + a′`. So if some
`H′` (with irreducible `Y(H′)`) never attained, the implication "`G.splitOff` attains ⟹ `G`
attains" would be *false* at `(δ′, m)` in the gap — e.g. `(3, 2)`, `(2, 3)`, `(1, 4)` with
`a′ = 1`. A proof of `hK` or `hbareSplit` *as stated* would therefore have to prove that `H′`
attains, i.e. the conjecture for the smaller graph `G − chain`, inside the kernel. **The natural
repair is to give both kernels the induction hypothesis** — `∀ G', |V(G')| < |V(G)| →
HasPencilRealization K 3 G'` (or just for `G − chain`); `pencilPair_of_splitOff_of_habitat` has
`hIH` in scope at both call sites (`Escape.lean:412–430`), so the Lean change is mechanical;
`hcontract` already takes the IH in this form. A pointwise witness of the gap: `specialcfg.py`
family (i) on `K4−e (4,2,3,4,2)` has `a′ = 1`, `a′_w = 0`, `δ′ = 3` (S13(vii)), so at those
special configurations `H′ ∪ ear₁` attains while `H′ ∪ ear₂` does not (control:
`drivers/splitoff.py --special`) — which is also why the antecedent must be read at the generic
point (via irreducibility) and not extended at the given point ("every placement fails", brief §5).

**(vi) What this does to the attack.** (O4″) — `ρ̄ ∩ Π_w = 0` on single pieces with `dist ≥ 6` —
is **not consumed**: the consumer needs `Π_w ⊄ ρ̄′` and the rest of the `m = 2` list, and (iii)
derives all of it from the split-off antecedent. The general two-sided Lemma, the frame's
welded-attainment supply (now (i)), the SPQR/piece decomposition, the short-path kill and the
census (S13) are not needed for `hK`/`hbareSplit`; they remain true statements about sides.
What the consumed step still needs, beyond (iii): (α) irreducibility of `Y(H′)` (or matching of
the attaining component of `H′` with the one `G₋` certifies); (β) that the configuration
variety's degenerate strata (coincident adjacent points, collinear hub stars — allowed by the
bare `HasPencilRealization`) lie in the closure of the nondegenerate locus, so a degenerate
witness still certifies the generic point (`hK`'s antecedent is nondegenerate, so this concerns
`hbareSplit` only); (γ) descent to `K`-points; (δ) the PI's decision on (v).

**(vii) Irreducibility and the two arms.** `hK` fires when `G` is nondegeneracy-feasible, which
forces `|closedHubNbhd z| ≤ 3` at every hub (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`;
reason: all normals of `closedHubNbhd z` are orthogonal to `p_z`, hence lie in a 3-space) — the
hub graph has maximum degree `≤ 2`, and the S13(iv) tower extends: along a hub path place
`p_{z_{i+1}} ∈ π_{z_i}` and `π_{z_{i+1}} ∋ p_{z_i}, p_{z_{i+1}}` (a `P¹`); closing a hub cycle
(length `≥ 7`) puts the last hub on the line `π_{z_{k−1}} ∩ π_{z_1}` with its plane determined
— constant-dimensional irreducible fibres over a dense open part of the base. So (α) holds on
`hK`'s whole domain. `hbareSplit`'s domain (some hub with `≥ 3` hub neighbours) is where the
tower may need a 2-degenerate ordering of the hub graph that need not exist; open, and now
the only structural residue of the consumed step.

**Verdict.** S14(i)–(iii): *proven-informally* (linear algebra on S8's ear profiles, S2/S3 and
the explicit Gram matrices above; control `drivers/splitoff.py`, session 5). (iv): true modulo
(α)–(γ) as named. (v): a statement-level finding for the PI. **What would change this:** a draw
with `G₋` attaining, `H′` attaining and `G` failing (the control asserts the implication at every
draw); or a Gram entry above disagreeing with the exact computation (`splitoff.py` prints
expected/got for each).

## S15 — Review notes (2026-09-16, `/review-attack` after session 5; the reviewer's checks, not the attack's — verify before building on them)

**(i) The consumer, diffed against the source.** `Escape.lean`, `pencilPair_of_splitOff_of_habitat`:
`hK` takes `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` and concludes the chart form
(hub selectors, `q`, an edge-indexed row set `s` of the target cardinality with linearly
independent `pencilRow`s); `hbareSplit` takes `¬ PencilNondegFeasible K G → HasPencilRealization
K 3 (G.splitOff v a b e₀)` and concludes `HasPencilRealization K 3 G`. Neither carries an
induction hypothesis; `hIH : ∀ G', V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G'`
is in scope at the sole call site and feeds both arms
(`hasGenericPencilRealization_of_splitOff_of_safe … hIH`; `(hIH _ hV'ne hV'lt).2`); `hcontract`
already takes the IH in that form. `splitOff` (`Molecular/Induction/Operations.lean:770`): vertex
set `V(G) \\ {v}`, links = those of `G` avoiding `v` plus the fresh `e₀` joining `a, b`. So S14's
reading stands, and the brief's §3 ("its antecedent may be discarded") and §5 first bullet were
wrong. The call site converts `hK`'s chart-form conclusion to `HasGenericPencilRealization K 3 G`
at once (`hasGenericPencilRealization_of_independent_pencilRow_target`) and uses nothing else of
it — so a kernel with that weaker conclusion would serve the same call site.

**(ii) S14(i), (ii), (v) re-derived.** From S10(ii), at every configuration
`dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6) + a₁ + a₂ − a(G)`, and `ρ_i = δ_i + a_i − a_i^w` (welding removes
exactly the relative motions: `dim M(H/uv) = dim M(H) − ρ`, with `dim M(H) = 6 + f + a` and
`dim M(H/uv) = 6 + g + a^w`). Side 2 = `ear_{m−1}`: `δ₂ = m`, `ρ₂ = m` (`m ≤ 6`), `a₂ = 0`. `G₋`
attains iff `ρ′ + m − dim(ρ̄′ ∩ ρ̄_{m−1}) = min(δ′+m, 6) + a′`; for `δ′ + m ≤ 6` this reads
`dim ∩ = −a′_w`, forcing both to `0`; for `δ′ + m > 6` the right side `6 + a′` exceeds the left's
cap `6` unless `a′ = 0` with the sum full. (ii) likewise with `m + 1`. (v):
`dim M(G) ≥ (6 + f′ + a′) + (7 + m) − 6 − 6 = f′ + a′ + m + 1`, while
`6 + def₃(G) = f′ + m + 7 − min(δ′+m+1, 6) = f′ + m + 1 + max(0, 5 − δ′ − m)`; at
`δ′ + a′ = 6 − m` this is `f′ + m + a′ < dim M(G)`, so `G` fails on the whole component. Correct.
The gap is hypothetical on a *never*-attaining side; its content is that no local argument can
prove the pinned kernels, whose truth on the gap cells is the conjecture for `G − chain`.

**(iii) S14(iii) traced against S2.** Each of (X1)–(X4) has a necessary condition on `B` alone —
`P(B)` on a smooth pencil member (X1), `Q₂|_B ≡ 0` (X2), an isotropic trace on `⟨L⟩^⊥` or
`⟨M⟩^⊥` (X3), a ruling-plane trace on `Π_w ⊕ Π_v` (X4) — and the Gram data of `ρ̄(ear₂)`,
`T(ear₂)`, `ρ̄(ear₃)` contradict each (`splitoff.py` item (6), `gram_mismatches = 0`). The
`m = 2`, `δ′ ≤ 3` step's three failure modes each put a vector into `ρ̄′ ∩ R_y` as claimed
(`L_{wy} ∈ Π_w`; `3 + 2 > 4` inside `Π_w ⊕ Π_v`; `⟨M⟩ ⊕ Π_w ⊇ Π_w`). The degenerate-ear steps
(`δ′ ≥ 4` at `m = 3`, `δ′ ≥ 5` at `m = 2`) are correct uses of lower semicontinuity of rank
over the irreducible ear moduli. Wording: S14 cites S5 for "a generic ear is a generic gauge
translate `g·ear₀`", which S5 does not say (the ear moduli, `3m − 2` dimensions, exceed the
5-dimensional `S(ϕ)` for `m ≥ 3`); what S14 uses is S5's actual mechanism — one good pair
`(q₁, g·q₂)` makes the generic point good by semicontinuity — and that holds. Not re-read here:
S1's stratum list beyond S2's use of it.

**(iv) Signals.** "Where it breaks" moved at every one of the five sessions (O4 → O4 general →
O4 at `m = 2` [review 1] → (O4′) → (O4″) → S14(v) + O7), so the first signal line never fires;
the count read `3` at every session end (7 → 3 inside session 1). By the review rule that is a
treadmill, and sessions 3–4 were one: (O4′) and (O4″) are rigidity statements about an
arbitrary side, of the same type as O4 and as the target (S7). Session 5 ended it by changing
the *target*, not by discharging anything on the old one: O4–O4″ were never proved, only shown
unconsumed. Session 3 was the one sweep-shaped session — its sketch change ((O4′), "the K4
structure puts one screw into the pencil") was a mechanism narrated from a measured `1`,
withdrawn by S13(i) once the vector was exhibited (`notes/harness/incidents.md` 2026-09-16).

**(v) Evidence gaps.** (a) No driver population contains a hub with three hub neighbours:
`census.py` subdivides every skeleton edge to length `≥ 2` (that is what makes S13(iv) apply),
the battery has at most two interior hubs, and S13(iv) itself lists adjacent-hub sides as
uncovered. So the bare arm — `¬ PencilNondegFeasible`, forced by a closed hub neighbourhood of
size `≥ 4` — has never been sampled; the (K-bare) extension-route recon flagged the same gap on
2026-07-30 (`notes/Phase39-design.md`). (b) S14(vii), "irreducibility on all of `hK`'s domain",
is a paragraph sketch of the tower along hub paths and cycles, not a proof; the state file's
"covered" overstates it. (c) The brief's "unchecked: the 5-rows-per-hinge matrix against Lean's
`rigidityRows`" has stood since the brief was written, and every line of S14 is a rank
statement — the Lean round's question (a). (d) `ρ̄(ear_m) = Λ²K⁴` at `m ≥ 5` is used at
*incident* flags (`w ~ v`) and measured at generic flags only; one exact witness settles it
(rank is lower semicontinuous), and the retirement of O6 leans on it.

**(vi) O8's stratum list, from the definition body.** `IsNondegPencilRealization` (`Motive.lean`)
= panel realization ∧ (each link's two points linearly independent) ∧ (normals linearly
independent on every closed hub neighbourhood) ∧ (points linearly independent on every
non-hub's closed neighbourhood). A bare witness may therefore sit on three strata: coincident
adjacent points; dependent normals on a closed hub neighbourhood; collinear degree-2 stars. The
second includes `π_w = π_v` for the `m = 2` antecedent `H′ ∪ ear₁`: there the fibre of
`y ∈ π_w ∩ π_v` jumps from a line to a plane, so S14(iv)'s "fibration with irreducible fibres of
constant dimension" fails over that locus and `Y(G₋)` may acquire a component there. On `hK`'s
arm it is excluded — `y`'s closed hub neighbourhood is `{w, v}`, whose normals must be
independent — so it is a bare-arm item. The state file's O8 names two strata and this locus not
at all.

**(vii) A question for the Lean round, not the attack: does a bare witness certify anything?**
The Lean's bare motive quantifies over a `BodyHingeFramework` carrying its own hinge extensor
per edge, constrained only to pass through both endpoint points (and lie in the panel planes).
At coincident adjacent points the hinge is any line through the point in both planes — freedom
the attack's `Y(G)` (hinge = the line through the two points) does not have. If such a
degenerate witness can attain the target rank without being a limit of nondegenerate
configurations, the bare arm's antecedent says nothing about the generic point and O8 cannot be
written against the attack's variety. The plausible fix is a conjunct "adjacent points
projectively distinct" on the bare motive, which costs the infeasible arm nothing (infeasibility
comes from hub normals). Settled by a definition-body derivation on the Lean side
(`notes/Phase39.md` checklist item 4(b)).

**(viii) Revived.** (a) S9 — the `ear₁` criterion in closed form — retired at review 1 as "a
shape the consumer does not take": at `m = 2` the antecedent graph *is* `H′ ∪ ear₁`, so S9
states what the antecedent says about `H′`, and its measured law `T ∩ ⟨M, L⟩ = 0` at `dist ≥ 4`
(19 sides) would make the antecedent nearly redundant there — the content would sit in the
side's attainment and welded attainment. (b) The brief's §5 first bullet ("every placement
fails; hence the bypass"): the observation stands, the conclusion does not — S14(v) explains the
failures as the `a′` gap at special configurations, and S14 uses the antecedent as a
generic-point certificate.

**(ix) Verdict, decision, sequence.** Switch to R2, gated on the PI adding the induction
hypothesis to both kernels — **decided by the PI 2026-09-16** (`notes/pencil/adjudications.md`).
Sequence (`notes/Phase39.md` *Hand-off*): a read-only Lean recon on (v)(c), (vii), and whether
feasibility and simplicity restrict from `G` to `G − chain` (the chain ends become non-hubs
there, where the fourth nondegeneracy conjunct bites); the kernel-restatement slice, restating
the design-doc and blueprint pins in the same commit; the brief rewritten from the landed
declarations (both kernels quoted verbatim, one hypothesis per line, each operator glossed from
its body; a justification for any unused hypothesis; a "consumed because" line per
obligation); then session 6, whose first move is O7 with an adjacent-hub control — build a side
with a hub of three hub neighbours, each continued by a branch of length `≥ 2` to `w` or `v` at
girth `≥ 7`, and sample from several starts before attempting the tower extension or component
matching. Small items for session 6: O8 with (vi)'s list against the bare space as (vii)
settles it; the O9 descent paragraph; the `m ≥ 5` incident-flag witness of (v)(d); S14(vii) as
a proof.

**What would change this review's verdict:** a proof that the pinned kernels are locally
provable after all (a local argument giving `a′ = 0` on the component the antecedent
certifies); or a bare-arm instance where `G₋` and `H′` attain and `G` fails at every
configuration — the control session 6 should run first on an adjacent-hub side.

## S16 — The hub order is forced by the habitat count; `m ≥ 5` without the 2-cut law; the irreducibility tower restated as a codimension check; descent (session 6, 2026-09-22)

Session 6's charges (state file, PI note of 2026-09-17): the `m ≥ 5` re-derivation, then O7 with
an adjacent-hub control, then O9. Tree at `c9dd58ca`. Driver `earspan.py` (exact ℚ, seed
`20260922`, caps in `drivers/README.md`).

**(i) The consumer, re-diffed at `c9dd58ca`.** `pencilPair_of_splitOff_of_habitat`
(`Escape.lean`): both kernels match the brief's §3.1 quote byte for byte, and every operator's
body matches its §3.2 gloss (`splitOff`, `PencilHub`, `closedHubNbhd`, `IsNondegPencilRealization`,
`PencilNondegFeasible`, `HasDistinctPencilRealization`, `HasGenericPencilRealization`,
`PencilPair`, `IsProperRigidSubgraph`, `TwoEdgeConnected`, `Simple`, `HasPencilPanelRealization`).
Two things the brief infers from those bodies do not follow from them:
- **(D1) `hK` carries no feasibility hypothesis.** Its list is `Simple`, `5 ≤ |V|`,
  `TwoEdgeConnected`, no proper rigid subgraph, `degree v = 2`, `eₐ ≠ e_b`, the two links, the
  disjunct, `e₀ ∉ E(G)`, the IH, and the antecedent `HasGenericPencilRealization K 3 (G.splitOff …)`
  — `PencilNondegFeasible K G` is a hypothesis of `hbareSplit`'s negation only. The brief's "`hK`'s
  domain — hub graphs of max degree `≤ 2`" (§6, S14(vii)) is therefore *derived*, not given: a proof
  of `hK` must first show `G` feasible from its antecedent. That is the upward transfer (v) below —
  true in the habitat, but an obligation the brief did not list.
- **(D2) "(α) deletes O8" is over-stated.** `HasDistinctPencilRealization` (`Statement.lean`) adds to
  the bare panel motive exactly one conjunct, `LinearIndependent K ![point u, point v]` at every
  link; it does **not** carry `IsNondegPencilRealization`'s third and fourth conjuncts. So a witness
  of `hbareSplit`'s antecedent, or of the IH's second conjunct, may still sit where a hub's closed
  star is collinear (its plane then one of a `P¹`) or where two hub planes coincide — strata outside
  S13(iv)'s `Y°` ("each hub's closed star spans a plane"). What (α) removes is the coincident-point
  stratum alone. The surviving residue is not a separate obligation: (iv) below proves
  irreducibility of the *closed* incidence variety, strata included, so it is absorbed into O7.

**(ii) Proposition (the habitat forces a 2-degenerate hub order — O7a).** Let `G` satisfy the
kernels' hypotheses and `K ⊆ G` be any subgraph with `V(K) ⊊ V(G)`, `|V(K)| ≥ 2`. Then
`5|E(K)| ≤ 6(|V(K)| − 1)`. Consequently the *hub graph* of `G − chain` (vertices: the hubs of `G`
lying in `H′`; edges: the hub–hub edges) — and every subgraph of it — has average degree
`< 2.4`, hence a vertex of degree `≤ 2`; i.e. the hub graph is 2-degenerate, and its hubs admit an
order in which every hub has at most two earlier hub neighbours.
*Proof.* If `5|E(K)| > 6(|V(K)| − 1)`, the 5-fold fibre of `E(K)` in `G̃` is dependent in the
tree-packing matroid `M(G̃)` (six copies of the cycle matroid; rank of any set on `t` vertices is
`≤ 6(t − 1)`), so it contains a circuit `C`; every vertex met by `C` has degree `≥ 2` in `C`
(deleting a degree-1 fibre edge would leave a dependent set on fewer vertices), so
`|C| = 6(|V(C)| − 1) + 1` with `C − e` independent, i.e. six edge-disjoint spanning trees of
`V(C)` (Nash-Williams–Tutte), i.e. `def₃(G[V(C)]) = 0`; and `V(C) ⊆ V(K) ⊊ V(G)`, `|V(C)| ≥ 2`,
so `G[V(C)]` is a proper rigid subgraph — against the habitat. The Lean already carries this
route: `circuit_induces_isRigidSubgraph` (`Induction/Operations.lean`), `matroidMG_indep_iff`
(`Deficiency.lean`), and the same argument at `k > 0` in `indep_edgeSet_mulTilde_of_noRigid_of_pos`
and `edgeBound_of_noRigid_of_degree_two` (`ReducibleVertex.lean`, KT Lemma 4.5). For the hub
graph: a subgraph `J` on `t ≥ 2` hubs has `|E(J)| ≤ (6t − 6)/5 < 1.2t`, so `2|E(J)| < 2.4t` and some
hub has `J`-degree `≤ 2`; peel it and recurse. ∎
*Reading.* The brief's O7 "first instance" — a hub `z` with three hub neighbours each continued by
a branch of length `≥ 2` to `w` or `v`, side-degree `≥ 2` at both — is **not in the habitat** unless
the branches are long: with `z`'s three hub neighbours each carrying two branches of length `k` to
`{w, v}` the count is `5(3 + 6k) − 6(4 + 6(k − 1)) = 27 − 6k ≤ −6` only for `k ≥ 6` (`|V| = 34`);
and in every habitat instance the hub graph is a tree or has a degree-`≤ 2` peeling. The control
the brief asked for is therefore replaced by this count; no adjacent-hub side was sampled
("attempted, no figure; script not retained" does not apply — nothing was attempted).

**(iii) Theorem (`m ≥ 5`, from the IH alone; `w ~ v` allowed).** Let `G = H′ ∪ ear_m` at the hub
cut `{w, v}` with `m ≥ 5` (the ear `w x₁ … x_m v`; `w ~ v` in `H′` is possible exactly here,
`lem:pencil-chain-side-distance`). Then (a) `def₃(G) = def₃(H′) + m − 5`; (b) at any configuration
at which `H′` attains and the `m + 1` ear lines span `Λ²K⁴`, `G` attains; (c) the `m + 1` lines of a
generic ear span `Λ²K⁴` at generic flags and at incident flags (`p_v ∈ π_w`, `p_w ∈ π_v`). Hence
`a′ = 0` at the generic point of `H′`'s configuration variety gives `G` attaining at the generic
point of `G`'s — the antecedent `G₋` is not used, and neither S14(i) nor the 2-cut deficiency law
(`deficiency_eq_of_vertexTwoCut`, which needs `w ≁ v`) enters.
*Proof.* (a) `≥`: extend an optimal partition of `V(H′)` by the `m` ear vertices as singletons:
`6m − 5(m + 1) = m − 5` more. `≤`: for a partition `P` of `V(G)` let `P′` be its trace on `V(H′)`,
`j` the number of parts inside the ear interior, `c` the number of ear edges crossing `P`; then
`|P| = |P′| + j`, `d(P) = d_{H′}(P′) + c`, so `6(|P| − 1) − 5d(P) ≤ f′ + 6j − 5c`. If `j = 0`,
`6j − 5c ≤ 0 ≤ m − 5`. If `j ≥ 1`, the path `w x₁ … x_m v` starts and ends outside the ear-only
parts, so it changes part at least `(number of ear-only runs) + 1 ≥ j + 1` times: `6j − 5c ≤ j − 5
≤ m − 5` (`j ≤ m`). (b) Gluing identity `finrank_span_rigidityRows_vertexTwoCut_eq` (no
non-adjacency needed) with `V₁ = V(H′)`, `V₂ = V(ear) ∪ {w, v}`: `rank(G) = rank(H′) + rank(G[V₂])
+ dim(ρ̄′ + ρ̄₂) − 6`. If `w ≁ v`: `G[V₂] = ear_m`, `rank = 5(m + 1)` (a path's rows are always
independent), `ρ̄₂ = span` of its `m + 1` lines `= Λ²`, so `rank(G) = rank(H′) + 5(m + 1)`. If `w ~ v`:
`G[V₂] = C_{m+2}` (ear plus the edge `wv`), whose `m + 2` lines span `Λ²` (they contain the ear's),
so `rank(C_{m+2}) = 6(m + 2) − (6 + (m + 2) − 6) = 5(m + 2)`; and `ρ̄(C_{m+2}) = ⟨L_{wv}⟩ ⊇ ρ̄′`
(the hinge `wv` constrains `m(v) − m(w)` to its line), so `dim(ρ̄′ + ρ̄₂) = 1` and again `rank(G) =
rank(H′) + 5(m + 1)`. With `rank(H′) = 6(|V(H′)| − 1) − f′` and (a), `rank(G) = 6(|V(G)| − 1) −
def₃(G)`. (c) `earspan.py`: at seed `20260922`, `m = 5, 6`, both flag regimes, rank `6` at 20/20
draws (control `m = 4`: rank `5` at 20/20); one exact draw is a certificate, and "generic ear"
follows by lower semicontinuity over the irreducible ear moduli at fixed flags. ∎
*Consequences.* S15(v)(d) is settled; the state file's `m ≥ 5` worry and the brief's §6 "worry the
Lean round surfaced" close; (a) is the edge-bipartition form of the 2-cut law at `m ≥ 5`, proved
directly (it is what `deficiency_eq_of_vertexTwoCut'`'s `¬ Adj` case cannot state).

**(iv) The irreducibility tower, restated as a codimension check (O7b, O7c).** For a side or
graph `H` in the habitat with hub set `Z` (the vertices of degree `≥ 3` in `G`; for `H′` include
`w, v`), let `X̄(H) ⊆ A := ∏_{z ∈ Z} Fl(P³) × ∏_{y ∉ Z} P³` (a hub carries a flag `(p_z, π_z)`,
`p_z ∈ π_z`; a non-hub a point) be the closed set cut out by the **incidences**: for every edge `zy`
with `z ∈ Z`, `p_y ∈ π_z` — one equation per (hub, neighbour) pair, `e := Σ_{z ∈ Z} deg z`
equations in all. A `HasDistinctPencilRealization` witness of `H` projects to a point of `X̄(H)`
(its hinges are `p_u ∧ p_v`, its normals at hubs are the `π_z`; the non-hub normals are dropped) and
rank depends only on the point coordinates, so **the attaining locus is an open subset of `X̄(H)`**
and a single witness certifies the generic point of every component through it. `Y°` of S13(iv)
is the open subset where each hub's closed star spans a plane; `X̄ ∖ Y°` is the collinear-star
stratum of (D2).
- **Krull.** `A` is smooth and irreducible, so every irreducible component of `X̄(H)` has dimension
  `≥ dim A − e` (height of a minimal prime over `e` generators is `≤ e`; `dim R/P + ht P = dim R`
  for a domain finitely generated over a field).
- **The tower.** Order the hubs `z¹, …, z^r` 2-degenerately ((ii)) and then the branch interiors.
  Step `k` places `(p_{z^k}, π_{z^k})` with `p ∈ ⋂_{earlier hub nbrs} π` and `π ⊇ ⟨p, earlier hub
  nbrs' points⟩`: fibre dimension `5, 3, 1` for `0, 1, 2` earlier neighbours (generic). A branch of
  length `k ≥ 2` between placed hubs adds `3(k − 1) − 2` (first point in one plane, last in the
  other, the rest free); length 1 is a hub adjacency, already counted. The sum is `dim A − e`. Over
  the locus `T_k°` where every step so far has generic fibre dimension, the fibre is the
  projectivisation of the kernel of a matrix of constant rank — a Zariski-locally-trivial bundle —
  so `X̄°` (all steps generic) is irreducible of dimension exactly `dim A − e`.
- **Reduction.** Inductively, `T_k` irreducible; `T_{k+1} = T°_{k+1} ∪ (part over the jump locus
  `J ⊆ T_k`)`. If a component `Z` of `T_{k+1}` misses `T°_{k+1}` then `Z` lies over some jump
  stratum `S ⊆ J` and `dim Z ≤ dim S + φ + j_S` (`φ` the generic fibre dimension, `j_S` the jump on
  `S`); Krull gives `dim Z ≥ dim T_k + φ`; so `codim_{T_k} S ≤ j_S`. **Hence `X̄(H)` is irreducible
  as soon as every jump stratum satisfies `codim > jump`.** The strata, all at a step with two
  earlier hub neighbours `z₁, z₂` or a length-2 branch `z — y — z′`:
  (a) `π_{z₁} = π_{z₂}` with `p_{z₁}, p_{z₂}, p` not collinear — jump `1` (`p` in a plane, `π` fixed);
  (a′) `π_{z₁} = π_{z₂}` and `p, p_{z₁}, p_{z₂}` collinear — jump `2`;
  (b) `π_{z₁} ≠ π_{z₂}`, `p_{z₁}, p_{z₂} ∈ π_{z₁} ∩ π_{z₂}` — jump `1` (`π` runs over a `P¹`);
  (d) `π_z = π_{z′}` at a length-2 branch — jump `1` (`p_y` in a plane, not a line).
  Codimension of each in the irreducible `T_k`, by imposing it at the step where the later of the
  two hubs is placed and counting: (a) costs `p_{z₂}`'s (or its earlier neighbours' points')
  incidence with `π_{z₁}` (`1` or `2` base conditions) plus the plane (`≥ 1`): `3` in each of the
  three sub-cases (`z₂` with `0, 1, 2` earlier neighbours); (a′) `≥ 3 > 2`; (b) two incidences
  `p_{z₁} ∈ π_{z₂}`, `p_{z₂} ∈ π_{z₁}`: `2 > 1`; (d) as (a): `3 > 1`. **What these counts assume
  (the open step, O7c):** that each such incidence between a hub plane and a *non-adjacent*
  vertex's point is a non-trivial condition on `T_k` — equivalently, the generic-incidence
  invariant *at the generic point of `T_k`, `p_b ∉ π_a` for every hub `a` and vertex `b ≁ a`, and
  `π_a ≠ π_{a′}` for distinct hubs* — proved by induction along the tower using girth `≥ 7` (no two
  hubs share two hub neighbours; no hub is adjacent to two vertices of a placed branch), which is
  the same pattern as S13(v)'s ordering argument. S13(iv)'s rotation limit for (d) is the special
  case of the reduction where the stratum's preimage is shown to lie in the closure directly.
- Two corollaries once (iv) closes: `X̄(G) → X̄(H′; w, v hubs)` is surjective with irreducible ear
  fibres, so the generic point of `X̄(G)` lies over the generic point of the base (S14(iv)'s
  fibration, now over the whole closed base); and the generic point of `X̄(H′)` has non-incident
  flags when `w ≁ v` (the invariant), so S14(iii)'s generic-`ϕ` setting is reached.

**(v) Upward feasibility (the obligation (D1) adds; closes).** In the habitat, `G.splitOff v a b e₀`
feasible ⟹ `G` feasible. *Proof.* `G₋ := G.splitOff …` is simple (`splitOff_simple_of_noRigid_of_card`),
so `a ≁ b` in `G` and degrees agree off `v`: `deg_{G₋} a = deg_G a − 1 + 1`, likewise `b`, all
others unchanged; hence the hub sets agree off `v`, and `v` is no hub. For `z ≠ v`,
`N_G(z) ∖ {v} ⊆ N_{G₋}(z)`, so `closedHubNbhd_G(z) ⊆ closedHubNbhd_{G₋}(z)` (`v` contributes to
neither); `|closedHubNbhd_G(v)| ≤ 2`. Feasible `G₋` has all closed hub neighbourhoods `≤ 3`
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), hence so does `G`, and `G` is simple
and triangle-free (`lem:pencil-girth-of-hub`; a hub-free `G` in the habitat is a cycle on `≥ 5`
vertices), so `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree` gives the
witness. ∎ So on `hK` the antecedent's nondegenerate witness makes `G` feasible, `H′` feasible by
(c), and the IH's first conjunct applies to `H′`.

**(vi) Descent (O9; closes modulo (iv)).** All of `X̄(G)`, its tower and the incidences are defined
over `K`. Over a `K`-point of `T_k°` the fibre is a projective `K`-linear space, whose `K`-points are
dense (`K` infinite); inductively the `K`-points of `X̄°(G)` are dense in it, hence in the irreducible
`X̄(G)`. The locus `U` of configurations that attain *and* meet the conclusion's open
nondegeneracy (`hK`: `IsNondegPencilRealization`, nonempty because `G` is feasible by (v); `hbareSplit`:
adjacent points distinct, nonempty) is open and nonempty in `X̄(G)`, so dense, so it contains a
`K`-point; its points, hub planes and (for non-hubs) any `K`-plane through the `≤ 3` points form
the Lean witness `(F, normal, point)` over `K`. ∎

**(vii) Verdict.** (ii) *proven-informally* (a count; Lean surfaces named). (iii) *proven-informally*
with (c) an exhibited certificate (`earspan.py`). (v), (vi) *proven-informally*, (vi) resting on (iv).
(iv): the reduction to `codim > jump` is proved; the codimension counts are stated with the one
assumption they rest on — the generic-incidence invariant — which is **the open step**. **What
would change this:** a habitat side whose tower has a jump stratum of codimension `≤` its jump
(the invariant failing: a hub plane forced through a non-neighbour's point by the incidences alone);
or a `HasDistinctPencilRealization` witness of some habitat `H′` isolated from `X̄°(H′)` — a
component of `X̄(H′)` of dimension `≥ dim A − e` over a jump stratum.

## S17 — The plane-first fibration: O7 as a codimension statement about free hub planes; two combinatorial lemmas; the kernels are pointwise at `m ≥ 6` (`hK`) and `m ≥ 5` (`hbareSplit`) (session 7 recovery, 2026-09-23)

Session 7 (2026-09-22/23) committed nothing: it spent ~4 h on O7c in twelve reasoning turns
that each hit the output-token cap, and its content was recovered from the local transcript
(a recovery note and twelve raw transcript blocks, kept under `notes/attacks/smark/` until
review 3 accepted this section; the PI deleted them on 2026-09-23, holding a backup). This section re-derives, by a different route, the one claim that recovery note
marks as found twice independently — S16(iv)'s stratum (a′) "jump 2" is an overcount — and
replaces the hub-by-hub tower of S16(iv) with a fibration in which O7c does not occur. Tree at
`ac3fbef6`; the consumer diff of S16(i) was re-run by session 7 with no change and is not
repeated. Drivers `planefirst.py` (new; pure combinatorics) and `earspan.py` (three regimes
added), caps in `drivers/README.md`.

**(i) The plane-first fibration.** Setting of S16(iv): `H` a habitat side or graph, `Z` its hub
set (for `H′` including `w, v`), `X̄(H) ⊆ A` the closed incidence variety. For a vertex `y` let
`E_y := N[y] ∩ Z` (a hub's own hyperedge contains itself) and `s_y := |E_y|`. Project
`X̄(H) → B := ∏_{z ∈ Z} P³*`, **planes only**. The fibre over `π ∈ B` is
`∏_y P(⋂_{c ∈ E_y} π_c)`, a product of projective linear spaces, of dimension
`Σ_y (3 − rk_y(π))` with `rk_y(π)` the rank of the normals `{n_c : c ∈ E_y}`; it is nonempty iff
`rk_y ≤ 3` for every `y`. `Σ_y s_y = |Z| + e`, so at `rk_y = s_y` the total is
`3|Z| + 3|V| − |Z| − e = dim A − e` — the expected dimension of S16(iv). The base is a
**product of projective spaces**: irreducible, with no hub order, no 2-degeneracy (S16(ii) is
not needed here) and no induction along the graph; degeneracy is *linear dependence among the
normals of one hyperedge*, a determinantal condition on `B`.

*Case 1 (`s_y ≤ 3` for all `y`).* This is exactly `|closedHubNbhd| ≤ 3` at every vertex, i.e.
`PencilNondegFeasible` (S16(v)) — `hK`'s whole domain — and it forces the hub graph to have
maximum degree `≤ 2` (a hub with three hub neighbours has `s = 4`). Every fibre is nonempty, so
`X̄ → B` is surjective; over the dense open `B° := {rk_y = s_y ∀ y}` (≤ 3 distinct free vectors
of `K⁴` are generically independent) the fibres are irreducible of constant dimension, so
`X̄° := X̄|_{B°}` is irreducible of dimension `dim A − e`. Let `J(π) := Σ_y (s_y − rk_y(π)) ≥ 0`
be the **total jump** and `D_j := {J ≥ j}` (closed, by upper semicontinuity of the fibre
dimension). Then `dim X̄|_{D_j ∖ D_{j+1}} ≤ dim D_j + (dim A − e − 3|Z|) + j = dim X̄° − codim D_j + j`,
and Krull (S16(iv)) bounds every component of `X̄` below by `dim X̄°`. Hence

> **(★)** `X̄(H)` is irreducible as soon as `codim_B D_j ≥ j + 1` for every `j ≥ 1`.

(★) is a statement about `|Z|` free planes in `P³` and the hypergraph `{E_y}`; it is the
plane-first form of S16(iv)'s "codim > jump", with **O7c gone**: no incidence between a plane
and a point ever has to be shown non-forced, because the points are not in the base.
*Case 2 (`hbareSplit`'s domain, some `s_y ≥ 4`)*: the image of `X̄ → B` is the closed set where
every hyperedge with `s_y ≥ 4` has `rk_y ≤ 3` (its `≥ 4` planes concurrent); (★) is then to be
read with `B` replaced by that image, whose irreducibility is a separate (determinantal) question
— see (vii).

**(ii) The hypergraph at girth `≥ 7`.** `|E_y ∩ E_{y′}| ≤ 1` for non-adjacent `y, y′` (a common
neighbour is unique: no 4-cycle) and `E_y ∩ E_{y′} = {y, y′}` for adjacent hubs (no triangle); a
pair `{c, c′} ⊆ Z` lies in `E_y` for `y ∈ {c, c′}` only when `c ~ c′` and for at most one `y`
otherwise. Checked on 132 girth-`≥ 7` sides by `planefirst.py` (0 violations). The abstract
setting for everything below: `G` in the habitat, `Z ⊆ V(G)` *any* marked set, `E_y := N[y] ∩ Z`
with `s_y ≤ 3` — deleting marked vertices stays in the class, and "hub" is never used.

**(iii) Two combinatorial lemmas (the cost of a degeneracy against the jump it buys).** The rank
pattern of `π` is determined by its *parallel classes* (sets of equal planes) and its *lines*
(sets of `≥ 3` distinct planes through a common line of `P³`, i.e. collinear normals in `P³*`);
only these matter for `J` since `s_y ≤ 3`. Placing the normals one class at a time, a
non-representative member of a class costs codimension `3` and a class lying on a line through
two earlier classes costs `2` — a valid *lower* bound on the codimension of the pattern's locus
(sequential upper bound on its dimension). Writing `J = Σ_A J_A + J_line` with
`J_A := Σ_y (|E_y ∩ A| − 1)⁺` for a parallel class `A` and `J_line := #{y : E_y = three distinct
collinear classes}`:

- **Lemma P.** For every `A ⊆ Z` with `|A| ≥ 2`: `J_A ≤ 3|A| − 4` (one less than the cost
  `3(|A| − 1)`). *Proof.* Let `Y_A := {y ∉ A : |N(y) ∩ A| ≥ 2}` and `Γ_A` the subgraph on
  `A ∪ Y_A` with the edges inside `A` and between `A` and `Y_A`; `Γ_A ⊆ H′ ⊊ G` (an ear-interior
  vertex has one hub neighbour at most, `m ≥ 2`), so `5e(Γ_A) ≤ 6(|A| + |Y_A| − 1)` (S16(ii)).
  `J_A = Σ_{a ∈ A} deg_A(a) + Σ_{y ∈ Y_A} (|N(y) ∩ A| − 1) = e(Γ_A) + e(A) − |Y_A|`. From
  `2|Y_A| ≤ e(A, Y_A) ≤ e(Γ_A)`: `|Y_A| ≤ 1.5(|A| − 1)`; and `e(A) ≤ 1.2(|A| − 1)`; so
  `J_A ≤ (6|A| − 6 + |Y_A|)/5 + 1.2(|A| − 1) ≤ 2.7(|A| − 1) ≤ 3|A| − 4` for `|A| ≥ 5`.
  `|A| = 2`: `J_A ≤ 2` by pair visibility. `|A| = 3`: `Γ_A` has `≤ 6` vertices and girth `≥ 7`,
  a forest, `e(Γ_A) ≤ 2 + |Y_A|`, `e(A) ≤ 2`, `J_A ≤ 4 ≤ 5`. `|A| = 4` (`|Y_A| ≤ 4`): by
  `|Y_A|`: `0 → 2e(A) ≤ 6`; `1 → e(Γ) ≤ 4, e(A) ≤ 2, J ≤ 5`; `2 → e(Γ) ≤ 6, e(A) ≤ 2, J ≤ 6`;
  `3 → e(Γ) ≤ 7, e(A) ≤ 3, J ≤ 7`; `4 → e(Γ) ≤ 8, e(A) ≤ 3, J ≤ 7`; all `≤ 8`. ∎ Tight at an
  adjacent pair (`J_A = 2`, cost `3`): `planefirst.py` finds slack `0` there and nowhere below.
- **Lemma L.** For every `L ⊆ Z` of `t ≥ 3` marked vertices with distinct collinear normals:
  `J_line(L) := #{y : E_y ⊆ L, |E_y| = 3} ≤ 2(t − 2) − 1`. *Proof.* In Case 1 a marked vertex
  has `≤ 2` marked neighbours, so `G[L]` has maximum degree `≤ 2`; a hyperedge `E_y ⊆ L` of size 3
  is either `y ∈ L` with both marked neighbours in `L` (`deg_L y = 2`; at most `e(L)` such `y`)
  or `y ∉ L` with three neighbours in `L` (impossible in Case 1: a non-hub has degree 2 and a
  hub `y ∉ L` with three marked neighbours has `s_y = 4`). So `J_line(L) ≤ #{y ∈ L : deg_L y = 2}
  ≤ e(L) ≤ 1.2(t − 1)`, and `1.2(t − 1) ≤ 2(t − 2) − 1` for `t ≥ 5`; `t = 3`: one hyperedge at
  most (two would overlap in 3); `t = 4`: `G[L]` a forest of maximum degree `≤ 2` on 4 vertices,
  `≤ 2` interior vertices, `J ≤ 2 ≤ 3`. ∎ (The general-`s_y` version, allowing outside `y` with
  three neighbours in `L`, goes through the habitat count on `L ∪ Y_L` exactly as Lemma P and
  gives the same bound; written in the recovery scratch, not needed in Case 1.) Tight at a hub
  path `a — z — b` (`J = 1`, cost `2`); `planefirst.py` slack `0` there, never negative.

*Consequences.* (★) holds when the degeneracies of `π` are parallelisms only (cost
`Σ_A 3(|A| − 1) ≥ Σ_A (J_A + 1) ≥ J + 1`), or a single line of distinct planes (Lemma L), and for
every `j ≤ 2` outright (a first degeneracy costs at least `J + 1`: `3 ≥ 2 + 1` for a parallel
pair, `2 ≥ 1 + 1` for a collinear triple). The locus of a pattern is a product over the
hub-disjoint connected components of its defective hyperedges, so codimensions add and (★)
reduces to **connected** patterns.

**(iv) The residue — O7d, replacing O7c.** What (★) still needs in Case 1: for every *connected*
pattern that mixes parallel classes with at least one line, or has two lines meeting, or a
class that is the third point of several lines, `cost ≥ J + 1`, where `cost` is the maximum over
placement orders of the sequential codimension (a class forced onto two already-determined
lines costs `3`, onto one costs `2`, a non-representative class member costs `3`). This is finite
combinatorics on `(G, Z)` with girth `≥ 7`, the habitat count and `s_y ≤ 3` — no algebraic
geometry is left in it, and no "generic point of a partial tower". The two lemmas cover its
two pure cases with slack exactly `1` each, which is why the mixed case is not automatic: the
surplus must be shown not to cancel when a class both carries parallel members and sits on a
line. A checker that enumerates all rank patterns on `|Z| ≤ 6` marked vertices and lower-bounds
each pattern's codimension by the Jacobian rank of its defining minors at a random exact
realisation is the natural control; it was commissioned in this session and its figure, if it
lands, is recorded in the state file's *Tried* section, not here.

**(v) Theorem (the kernels are pointwise at long chains).** Let `G = H′ ∪ ear_m` at the hub cut
`{w, v}` (trichotomy case (iii)). (a) *`hbareSplit`, `m ≥ 5`:* from the IH's second conjunct
alone. (b) *`hK`, `m ≥ 6`:* from the antecedent alone. Neither uses irreducibility, S14(i)–(iii),
or the 2-cut law; both produce a `K`-point directly.
*Proof.* Certificate first: `earspan.py` (seeds `20260922`, `20260923`; `s = 20`; 20 draws per
cell) finds the `m + 1` hinge lines of a random ear at rank `6` in every cell `m ∈ {5, 6, 7}` ×
{generic, incident, `p_w = p_v`, `π_w = π_v`, equal flags}; one exact draw per cell is a
certificate, and rank is lower semicontinuous on the ear moduli at fixed flags (irreducible), so
the lines of a **generic ear span `Λ²K⁴` at every flag pair of these five orbit types**; the two
single-incidence orbits (`p_v ∈ π_w` only, and its mirror) contain the both-incident orbit in
their closure, so semicontinuity on the total space (flags × ear) covers them too — all seven
`PGL₄`-orbits of flag pairs (S16(iv)'s ambient; the count `10, 9, 9, 8, 7, 7, 5` is the recovery
note's, re-derived: a flag has 5 parameters, the diagonal `PGL₄` has 15, the generic stabiliser
of a flag pair has 5 = the gauge group `S(ϕ)` of S1). (a) The IH gives an attaining,
adjacent-distinct panel realization `x′` of `H′` over `K`; its normals at `w, v` are planes
through `p_w, p_v` containing the neighbours' points, so `(p_w, π_w, p_v, π_v)` is a flag pair of
some orbit type. Add an ear over `K` at these flags with its `m + 1` lines spanning `Λ²` and its
points distinct from their neighbours (nonempty open in the `K`-linear ear moduli, so it has a
`K`-point). The result is a panel realization of `G` (`N_G[w] = N_{H′}[w] ∪ {x₁} ⊆ π_w`) with
adjacent points distinct, and by S16(iii)(a)–(b) — both pointwise identities: the deficiency
count and the gluing identity `finrank_span_rigidityRows_vertexTwoCut_eq`, with the cycle trick
at `w ~ v` — `rank(G) = rank(H′) + 5(m + 1) = 6(|V(G)| − 1) − def₃(G)`. That is
`HasDistinctPencilRealization K 3 G`. (b) The antecedent gives `x₋`, nondegenerate and attaining
for `G₋ = H′ ∪ ear_{m−1}`, over `K`. Discard its ear, keep `x′ := x₋|_{H′}` (all planes
included), and add a new ear as in (a). Nondegeneracy of `G` at the new point: conjunct (3) at
every hub is the *same* condition as in `G₋` (ear vertices are non-hubs, so `closedHubNbhd` is
unchanged at `w, v` and their neighbours); conjunct (4) at the non-hubs of `H′` is unchanged and
at the ear vertices is generic; (1)–(2) as in (a). Rank: with `m − 1 ≥ 5`, `rank(G₋) = rank(H′ at
x′) + 5m` and `def₃(G₋) = f′ + (m − 1) − 5` by S16(iii) applied to `G₋`, so `G₋` attaining gives
`rank(H′ at x′) = 6(|V(H′)| − 1) − f′`; then `rank(G) = rank(H′ at x′) + 5(m + 1) = target(G)`
as in (a). That is `HasGenericPencilRealization K 3 G`. ∎
*Reading.* The IH is not used in (b) and the antecedent not in (a); at `m ≥ 6` each kernel
follows from **one** of its two smaller-graph hypotheses. O7 (irreducibility of `X̄(H′)`,
`X̄(G.splitOff)`) is load-bearing only for `m ≤ 4` on both arms and for `m = 5` on `hK`'s arm
(where `G₋ = H′ ∪ ear₄` has five ear lines and the `δ′`-dependent gluing of S14(iii) enters).
This settles the scope question the recovery note lists as re-litigated five times: the
"`m ≥ 5` requires only descent and nondegeneracy" reading was right for `hbareSplit` and one
step short for `hK` (the closed-hub-neighbourhood conjunct at a chain end of `G`-degree 3 is
*not* implied by the IH witness of `H′`, where that end is a non-hub — hence the antecedent).

**(vi) What this does to S16(iv)'s stratum list.** The plane-first base has no point
coordinates, so S16(iv)'s stratum (a′) — `π_{z₁} = π_{z₂}` *and* `p, p_{z₁}, p_{z₂}` collinear —
is not a base stratum at all: over `{π_{z₁} = π_{z₂}}` (codimension 3 in `B`) the fibre of the
hub `z` is the whole `P(π_{z₁})` whether or not the points are collinear, and the jump is
`Σ_y (s_y − rk_y)` over the hyperedges containing both, i.e. `1` if `z₁ ≁ z₂` (only `E_z`) and
`2` if `z₁ ~ z₂` — the recovery note's "(a′) is an overcount" (found twice there) is confirmed,
and the jump-2 loci of the base are exactly *three equal planes on one hyperedge* (codimension
6) and the adjacent parallel pair (codimension 3, jump 2, the tight case of Lemma P). The
strata (a), (b), (d) of S16(iv) become: (a)/(d) a parallel pair, (b) — `p_{z₁}, p_{z₂} ∈ π_{z₁} ∩
π_{z₂}` — is a *fibre* condition and is no stratum of `B`; nothing needs counting for it. The
S16(iv) reduction "codim > jump" stands; only its stratum bookkeeping is superseded by (★).

**(vii) Verdict.** (i)–(ii) *proven-informally*; (iii) *proven-informally* (Lemmas P and L), with
`planefirst.py` as the control (slack `≥ 0` at 132 rows, tight at the predicted shapes); (v)
*proven-informally* with an exhibited certificate (`earspan.py`, nine new cells); (vi) a
correction of S16(iv)'s prose, no claim changes. Open: **O7d** (iv), the connected mixed
patterns, for Case 1; and, for Case 2 (`hbareSplit`'s domain, `m ≤ 4` only now), the
irreducibility of the image of `X̄ → B` — the locus where every hyperedge of size `≥ 4` is
concurrent — before (★) can even be stated there. **What would change this:** a connected mixed
pattern on some habitat `(G, Z)` with `cost ≤ J` (a violation the commissioned checker could
exhibit); a flag orbit at which the `m + 1` lines of a generic `ear_{m ≥ 5}` fail to span `Λ²`
(none among the seven); or a `HasDistinctPencilRealization` witness of a habitat `H′` at `m ≤ 4`
isolated from `X̄°(H′)`.

## S18 — Review notes (2026-09-23, `/review-attack` after session 7; the reviewer's checks, not the attack's — verify before building on them)

Tree at `e1cd14f3`. The kernels match brief §3.1 (`Escape.lean`, `pencilPair_of_splitOff_of_habitat`, re-read);
`Escape.lean` last changed at `5c8ceb81` (item 5), before the checked sha `084ee4ff`. Verdict to the PI: **continue
on R2 in its plane-first form**; four corrections, applied on the PI's word the same day (brief §§2, 3.5, 4, 6, 7, 8;
`state.md`; this entry).

**(i) The consumer's domain includes the trichotomy's cases (i)–(ii).** Brief §3.5 read case (ii) — the chain closing
at a single hub `w` — as "owned by the cut-vertex case of the induction, not by these kernels". The consumer has no
such arm. `TwoEdgeConnected` (`Deficiency.lean`) is "every nonempty proper vertex set is crossed by `≥ 2` edges" and
admits cut vertices; the reduction's cut arm (`Arms.lean`, `pencil_reduction`'s `hcut_arm`, discharged by
`hasDistinctPencilRealization_of_not_twoEdgeConnected`) fires only on `¬ TwoEdgeConnected`; `hsplit` takes
`TwoEdgeConnected`; and `pencilPair_of_splitOff_of_habitat` applies `hK`/`hbareSplit` at whatever safe degree-2 vertex
`exists_adjacent_degree_two_pair_of_noRigid_of_degree_two` returns. Two 7-cycles sharing a hub `w` (simple,
2-edge-connected, no proper rigid subgraph — a 7-cycle has `def₃ = 1`, a path `def₃ =` its length) is in the domain and
is case (ii); a cycle on `≥ 5` vertices is case (i). Both must be proved inside the kernels. *Pointwise discharge
(sketch; O10):* case (i) directly — a generic skew `n`-gon's edge lines are independent for `n ≤ 6` and span `Λ²` for
`n ≥ 6` (S14(iv)), consecutive triples are non-collinear, so `C_n` has a `K`-point of `HasGenericPencilRealization`
(target `5n` at `n ≥ 6`, `6(n − 1)` below). Case (ii), `G = H″ ∪_w C_{m+1}` with `m + 1 ≥ 7` (girth, `lem:pencil-girth-of-hub`):
`hbareSplit` from the IH's Distinct witness of `H″ := G − {u₁, …, u_m}` plus a generic cycle through the flag
`(p_w, π_w)` — `earspan.py`'s `coinc-both` cell *is* a cycle through one flag, so its lines span; `hK` from the
antecedent's witness of `G₋ = H″ ∪_w C_m` (`m ≥ 6`): drop the cycle, add a fresh one — S17(v)(b) verbatim with `v = w`
(conjunct (3) at `w` is the antecedent's, since `w` is a hub in `G₋` as in `G`). Both need **cut-vertex additivity**:
`rank(G) = rank(H″) + rank(C)` (the motion spaces glue along `w`; each restricts onto `K⁶` at `w` through the trivial
motions, so `dim M(G) = dim M(H″) + dim M(C) − 6`) and `def₃(G) = def₃(H″) + def₃(C)` (brief §3.5(d), "[proved]" in
the corpus; **no Lean surface** — `Deficiency.lean` has the cut-*edge* law `deficiency_eq_of_cutEdges_ncard_le_one`
only). This is the brief's third consumer paraphrase; reviews 1–2 and the 2026-09-17 CHECKED pass diffed the §3.1
quote and the §3.2 glosses, not §2/§3.5's decomposition of the domain (incident line 2026-09-23).

**(ii) The certificates are characteristic-0 evidence.** Both kernels are over `[Infinite K]` with no characteristic
(brief §2, option C), so `K = F̄₂`, `F₂(t)`, … are in scope. S16(iii)(c) and S17(v) rest on exact ℚ-ranks of integer
Plücker vectors: a ℚ-certificate with `6 × 6` minor `D` proves the spanning in characteristic 0 and at every `p ∤ D`.
`earspan_modp.py` (new driver; the same draws, denominators cleared, ranks over `F_p`, `p ∈ {2, 3, 5, 7, 11, 13}`):
ℚ-rank 6 at 20/20 in all thirteen cells, but `F₂`-rank 6 at only **2–11 of 20** and `F₃`-rank 6 at **4–16 of 20** per
cell (`F₁₃`: 14–20 of 20). So the certificates do not travel by themselves — brief §2's "no characteristic" currently
rests on characteristic-0 evidence for the pointwise arms — but every cell has an `F₂`- and an `F₃`-certificate among
its 20 draws, and the closure argument of S17(v) makes **one certificate at equal flags per prime** sufficient for all
seven orbits (equal flags lie in every orbit's closure; a reduced draw's flags may land in a more degenerate orbit than
the cell's name, which only helps). **O11:** for each prime `p` dividing the chosen ℚ-certificate's minor, exhibit an
`F_p`-draw at rank 6 in the equal-flags cell — or a symbolic minor with a unit coefficient (for the *unconstrained*
skew hexagon `p₁..p₄ = e₁..e₄`, `p₅ = Σ aᵢeᵢ`, `p₆ = Σ bᵢeᵢ`, the `6 × 6` Plücker minor reduces to
`−a₁a₂b₃b₄ + a₁a₄b₂b₃ − a₂a₄b₁b₃ + a₂a₃b₁b₄`, unit coefficients, nonzero in every characteristic; the ear's
end-plane constraints need the same computation). The same cap applies to `starcheck.py`: its Jacobian ranks are
over ℚ (mod `2⁶¹ − 1`, a lower bound), and its 28 "unrealisable over ℚ" patterns are labelled Fano planes, realisable
in characteristic 2 — a control, so no obligation, but the cap travels with the PASS.

**(iii) (★) is proved on subgraphs of `G` and was consumed for `G₋` too.** Lemmas P and L (S17(iii)) use the habitat
count on `Γ_A ⊆ H′ ⊊ G` and girth `≥ 7`; O7d's "consumed because" named `X̄(G.splitOff)` alongside `X̄(H′)`.
`G₋ = G.splitOff` is not a subgraph of `G`: its girth can be 6, and it can contain a proper rigid subgraph — a 7-cycle
of `G` through the chain shortens to a 6-cycle (`def₃(C₆) = 0`, proper when `|V(G₋)| > 6`). So (★) is claimed for
`H′` only, and `X̄(G₋)` is derived: `X̄(G₋) → X̄(H′)` has fibre `P(π_w) × (P³)^{m−3} × P(π_v)` for `m ≥ 3` (the two end
ear points in the end planes, the rest free) — irreducible of constant dimension — and, at `m = 2`, `P(π_w ∩ π_v)`,
which jumps from `P¹` to `P²` over `{π_w = π_v}`. That locus is the parallel pair `{w, v}` in `H′`'s own plane-first
base, cost `3`, jump `J_{w,v} = #{y : E_y ∋ w, v} = 0` at `m = 2` (`dist_{H′}(w, v) ≥ 4`), so it has codimension `3`
in the irreducible `X̄(H′)`; Krull excludes a component of `X̄(G₋)` over it exactly as in S17(i). One paragraph;
folded into O7d's statement.

**(iv) A narrowing to verify: `hK` at `m = 5` is pointwise from the antecedent when `δ′ ≥ 1`.** The S16(iii)(a) count
run at `m = 4` (the ear of `G₋`) gives `def₃(H′ ∪ ear₄) = f′ − min(δ′, 1)`: `j ≥ 1` ear-only parts contribute
`6j − 5c ≤ j − 5 ≤ −1`; `j = 0` with `w, v` in different parts `≤ −5`; `j = 0` with `w, v` together `≤ g′ − f′ = −δ′`
— no adjacency assumption. So at `δ′ ≥ 1`, `target(G₋) = target(H′) + 25`, while the gluing identity gives
`rank(G₋) ≤ rank(H′ at x₋) + 25` (`w ≁ v`: side 2 the path `ear₄`, rank `25`, `dim(ρ̄′ + ρ̄₂) ≤ 6`; `w ~ v`: side 2
the 6-cycle, rank `≤ 30`, `ρ̄′, ρ̄₂ ⊆ ⟨L_{wv}⟩`). The antecedent attaining therefore forces `H′` to attain at
`x₋|_{H′}`, with `w, v` hubs in `G₋` as in `G` so conjunct (3) is the antecedent's; then S17(v)(b)'s ear swap gives
`hK` (a fresh `ear₅` spans, `def₃(G) = f′` by S16(iii)(a)). At `δ′ = 0` the count gives `target(G₋) = target(H′) + 24`
and the antecedent allows `a′ = 1` (`ρ′ = 1`, `a′_w = 0`, `ρ̄′ ⊄ ρ̄₂` — the `(0, 5)` cell of S14(v)'s gap), so only
`δ′ = 0` would stay on O7 at `m = 5`. Reviewer's derivation, unverified by driver; `splitoff.py` at `--ears 5` would
control the bookkeeping.

**(v) Signals and the rest.** `check.py --history`: the count ran **3 → 1 → 2** over sessions 5–7 (the state file's
"2 → 1 → 2" was wrong); the break moved at sessions 6 and 7. The 1 → 2 rise is Case 2 made explicit, not a rename;
O7c → (★) is a genuine reduction (O7c's statement is consumed by nothing now). S17(v)(a)–(b) and S16(iii)(a)
re-derived: they hold, with the cap of (ii). No premature kill: Route B's kill reason is Case-2 specific and
plane-first supersedes it. Session 7 proper landed nothing (twelve output-cap cuts; incident line 2026-09-23); its
recovery aids were deleted after this review on the PI's word, the PI holding a backup — S17 is the durable record.
With (i)–(ii) the count is **4** (O7d, O7e, O10, O11): two consumed requirements the count had omitted, not new
difficulty. **What would change this review's verdict:** a connected mixed pattern with `cost ≤ J` (O7d); a prime at
which no `ear₅` at equal flags spans (none for `p ≤ 13`); a case-(ii) graph on which cut-vertex additivity of `def₃`
fails (it should not — the corpus proof is a partition count).

## S19 — Theorem: (★) holds in Case 1 — O7d closes; the sequential-codimension form of (★) is a theorem on every habitat side (session 8, 2026-09-23)

Tree at `08d47c72` (no Lean file the kernels name has changed since `ac3fbef6`; consumer re-diffed
against every definition body, including the trichotomy's exhaustiveness over the domain — a
non-hub neighbour of the split vertex has degree exactly `2` under `TwoEdgeConnected`, so the
maximal degree-2 chain through it is the whole graph, closes at one hub, or joins two distinct
hubs). Driver `starcomb.py` (new), caps in `drivers/README.md`. This section proves S17(iv)'s
residue in full: **(★) `codim_B {J ≥ j} ≥ j + 1` for all `j ≥ 1` holds in Case 1 on every habitat
side**, by a global charging argument over all rank patterns at once — no case split on the
shape of the mixed pattern. The proof uses exactly: girth `≥ 7`, the habitat count on subgraphs
of `H′` (S16(ii)), Case 1 (each marked vertex has `≤ 2` marked neighbours), and unmarked degree `≤ 2`.

**(i) Setting and the sequential codimension.** `H′ ⊊ G`, `Z = hubs(G) = hubs(H′) ∪ {w, v}`,
`Γ := H′[Z]` the hub graph (max degree `≤ 2` in Case 1: paths and cycles of length `≥ 7`);
unmarked vertices have degree `≤ 2`, so the only unmarked hyperedges of size `2` are the
*connectors* (unmarked `y` with `N(y) = {a, b} ⊆ Z`). A *rank pattern* `P = (𝒞, ℒ)` is a set
partition `𝒞` of `Z` into classes (equal normals) and a set `ℒ` of *lines*, each a set of `≥ 3`
classes (distinct collinear normals), two lines sharing `≤ 1` class. `J` depends only on the
pattern: for `y ∈ Z` with `N_Γ(y) = {a, b}`, drop `2` if `[a] = [y] = [b]`, drop `1` if exactly two
of the three classes coincide **or** the three are distinct and on a line (`y` is *flat*), else
`0`; for `y ∈ Z` with one marked neighbour `a`, drop `1` iff `[a] = [y]`; for a connector, `1`
iff `[a] = [b]`. Writing `e(A)` for the Γ-edges inside a class `A` and `Y_A` for the vertices
outside `A` (marked or connectors) with both neighbours in `A`,

> `J = Σ_A J_A + F`,  `J_A = 2e(A) + |Y_A|`,  `F = #{flat vertices}` (S17(iii)'s decomposition).

The *sequential codimension* of `P` is `cost(P) := 3(|Z| − q) + LC(P)`, `q = |𝒞|`, where
`LC(P) := max` over placement orders of the classes of `Σ_C min(2d_C, 3)`, `d_C` the number of
lines through `C` already *determined* (two earlier classes) when `C` is placed. `cost(P) ≤
codim_B S_P` for the exact stratum `S_P` of `P`: `S_P` lies in the locus where distinct classes
are distinct points and distinct lines distinct geometric lines, which fibres sequentially with
fibre dimension `3`, `1` (one determined line) or `0` (two distinct determined lines meet in `≤ 1`
point), and every component of `{J ≥ j}` is the closure of some `S_P` with `J(P) ≥ j`. Dropping
lines from `ℒ`, or classes from a line, is a *relaxation*: it can only enlarge the locus, so
`cost(P′) ≤ codim S_P` for every such `P′` too — the proof below spends this freedom. **Theorem.**
*For every pattern with `J ≥ 1`, `cost(P) ≥ J + 1`. Hence (★) holds in Case 1.*

**(ii) Step 1 — the class surplus (sharpening Lemma P).** For a nontrivial class `A`, `m := |A|
≥ 2`, put `σ_A := 3(m − 1) − J_A` and `F_A := #{flat members of A}`. The habitat count on
`Γ_A := (A ∪ Y_A, E(A) ∪ E(A, Y_A))` — every `y ∈ Y_A` has exactly two neighbours in `A`, by Case 1
for marked `y` and by definition for connectors — reads `5(e(A) + 2|Y_A|) ≤ 6(m + |Y_A| − 1)`, i.e.
`|Y_A| ≤ 1.5(m − 1) − 1.25 e(A)`, so `σ_A ≥ 1.5(m − 1) − 0.75 e(A)`. A member on an internal
edge is not flat (its triple sees `A` twice), and in a graph of maximum degree `2` the `e(A)`
internal edges cover `≥ e(A)` members, so `F_A ≤ m − e(A)`. Hence
`σ_A − F_A ≥ 0.5m − 1.5 + 0.25e(A)`, which is `≥ 0.5`, hence `≥ 1`, for `m ≥ 4`. Small classes by
hand, with girth: `m = 3`, `e = 0`: three pairwise common neighbours would close a 6-cycle, so
`|Y_A| ≤ 2`, `σ ≥ 4 > 3 ≥ F_A`; `e = 1`: `|Y_A| ≤ 1`, `σ ≥ 3`, `F_A ≤ 1`; `e = 2`: `Y_A = ∅`, `σ = 2`,
`F_A = 0`. `m = 2` adjacent: `Y_A = ∅` (triangle), `σ = 1`, `F_A = 0`. `m = 2` non-adjacent:
`|Y_A| ≤ 1` (4-cycle); `σ − F_A ≥ 1` unless `|Y_A| = 1` **and** both members are flat. Call that
one shape a **bad pair**. So

> `S := Σ_{A nontrivial} (σ_A − F_A) ≥ #{nontrivial classes that are not bad pairs} ≥ 0`, and
> `cost − J = S + LC − F_sing`, `F_sing := #{flat vertices whose class is a singleton}`.

**(iii) Step 2 — reduce the lines; the per-line surplus.** Relax: drop every line carrying no
flat vertex and, on each remaining line `ℓ`, keep only the classes `{[y], [a], [b]}` of the flat
`y` on it (its *reduced* class set `R_ℓ`, `t_ℓ := |R_ℓ| ≥ 3`). Two facts: a flat vertex is flat on
exactly one line (its three classes determine it), and a flat *singleton* `{y}` lies on exactly
one reduced line and is never a neighbour class on another — if `y ~ y′` with `y′` flat on
`ℓ′ ≠ ℓ_y`, then `{y}, {y′}` lie on both, two classes shared. Write `f_ℓ` for the flat singleton
classes on `ℓ`, `U_ℓ` for the other classes of `R_ℓ`, `u_ℓ := |U_ℓ|`, and
`surplus_ℓ := 2(t_ℓ − 2) − f_ℓ = f_ℓ + 2u_ℓ − 4`. Then `surplus_ℓ ≥ 0`, and `surplus_ℓ = 0` only
for a line of **type (3)**: `f_ℓ = 2`, `u_ℓ = 1`, `R_ℓ = {A, {y₁}, {y₂}}` with `a — y₁ — y₂ — a′` in
`Γ`, `a ≠ a′ ∈ A`. *Proof.* If `f_ℓ = 0`, `surplus = 2(t_ℓ − 2) ≥ 2`. Otherwise let `W` be the flat
singletons of `ℓ`; `Γ[W]` has maximum degree `2`. A cycle component has `≥ 7` vertices, so
`f ≥ 7` and `surplus ≥ 3`. Else `Γ[W]` is a forest of paths, each `W`-vertex has two Γ-neighbours,
so path ends have neighbours in `∪U_ℓ` and `u ≥ 1`; `u ≥ 2` gives `surplus ≥ f ≥ 1`. For `u = 1`,
`U = {A}`: an isolated `W`-vertex would have both neighbours in `A` and not be flat, so every path
has `≥ 2` vertices, `f ≥ 2π` for `π ≥ 1` components, `surplus = f − 2 ≥ 0`, with equality iff
`π = 1`, `f = 2`; the ends `a, a′ ∈ A` are distinct (a triangle otherwise). ∎ On a type-(3) line
`A` is nontrivial and **not bad**: `a, a′` are at distance `3`, so a common neighbour would close
a 5-cycle, `Y_A = ∅` for `|A| = 2`, and `σ_A − F_A ≥ 1` in every case of Step 1.

**(iv) Step 3 — the loss.** Place all `U`-classes first (any order), then the flat singletons.
For any order `Σ_C d_C = Σ_ℓ (t_ℓ − 2)`, so `LC ≥ Σ_ℓ 2(t_ℓ − 2) − loss`, `loss := Σ_{d_C ≥ 2}
(2d_C − 3)`. Flat singletons have `d ≤ 1`. A lossy `U`-class `C` is, on each of its `d_C`
determined lines, at least the third `U`-class placed, so those lines have `u_ℓ ≥ 3` and
`Σ_{C lossy} d_C ≤ Σ_{u_ℓ ≥ 3} (u_ℓ − 2)`. Therefore
`Σ_{u_ℓ ≥ 3} surplus_ℓ − loss ≥ Σ_{u_ℓ ≥ 3} f_ℓ + 2Σ_{u_ℓ ≥ 3}(u_ℓ − 2) − Σ_{lossy}(2d_C − 3) ≥ 3·#lossy`,
and, whether or not any loss occurs, this bracket is `≥ 2` as soon as some line has `u_ℓ ≥ 3`
(no loss: each such line alone has `surplus ≥ 2u − 4 ≥ 2`). With `F_sing = Σ_ℓ f_ℓ`:

> `LC − F_sing ≥ Σ_{u_ℓ ≤ 2} surplus_ℓ + 2·[∃ ℓ : u_ℓ ≥ 3]`.

**(v) Step 4 — conclusion.** `cost − J ≥ S + Σ_{u_ℓ ≤ 2} surplus_ℓ + 2·[∃ ℓ : u_ℓ ≥ 3]`, every
term `≥ 0`. Suppose the right side is `0` with `J ≥ 1`. No line has `u ≥ 3`; every remaining
line is type (3); `S = 0`. If there are no lines, `F = 0` and `J ≥ 1` forces a nontrivial class
with `J_A ≥ 1`; it has `F_A = 0`, so it is not bad and `S ≥ 1` — contradiction. If there is a
line, it is type (3), whose class `A` is nontrivial and not bad — `S ≥ 1`, contradiction. ∎
The two tight shapes of Lemmas P and L are recovered as the only equality cases at `J = 1, 2`
(an adjacent parallel pair: `S = 1`, no lines; a flat singleton path `a — z — b`: `surplus = 1`).

**(vi) Control — `starcomb.py`.** The driver enumerates *every* rank pattern (set partition
`×` partial linear space, as `starcheck.py`) on `starcheck.py`'s nine graphs and on `60` random
habitat sides (seed `20260923`; hub skeletons of maximum degree `≤ 2` with edges subdivided into
paths of length `1..5`, pendant paths, up to two extra marked degree-2 vertices modelling `w, v`;
each side verified for girth `≥ 7`, Case 1, unmarked degree `≤ 2`, and the habitat count on
**every** vertex subset, computed exactly through the 2-core's chains), computes `LC` by an exact
subset DP over all placement orders, and checks the **four links** of the proof separately —
Step 1's `σ_A − F_A ≥ [not bad]` and the `|Y_A|` bound, Step 2's `surplus_ℓ ≥ 0` with the
equality cases exactly the type-(3) lines, Step 3's loss inequality, Step 4's final bound — plus
the headline `cost ≥ J + 1` on the full line set and the two structural facts of (iii).
**Figure:** `112 261` patterns, `64 325` with `J ≥ 1`, every link holds on every pattern; minimum
of `cost − J − 1` is `0` (full and reduced), attained at `197` patterns of the full form — the
Lemma P/L extremal shapes and their disjoint unions — `831` type-(3) reduced lines and `447` bad
pairs exercised; `8.8` s. Seeds `1`, `2` with `80` sides each: `73 969` and `55 831` patterns with
`J ≥ 1`, PASS. Caps: `|Z| ≤ 7`, `|V| ≤ 24`, the generator's shapes (README). The `cost` the
driver checks is the sequential codimension, a lower bound on the geometric one; `starcheck.py`'s
Jacobian bound is the independent geometric control (PASS, S17).

**(vii) What this does to the route.** (a) **O7d is closed**: `X̄(H′)` is irreducible whenever
`H′` is in Case 1, by S17(i) and the Theorem; `X̄(G₋)` follows by S18(iii). (b) **`hK`'s arm
needs nothing more of O7.** On `hK`'s arm `G` is feasible (derived, S16(v)), which is exactly
Case 1 for `H′` (`Z = hubs(G)`, and a chain vertex adds no hub to any closed hub neighbourhood);
so at `m ≤ 5` the IH's witness and the antecedent's lie on the main component and S14(iii) applies
at the generic point, with descent O9 (S16(vi)); at `m ≥ 6` S17(v)(b) is pointwise. (c) **On
`hbareSplit`'s arm `H′` is always Case 2.** `¬ PencilNondegFeasible K G` gives a vertex `y` with
`|closedHubNbhd_G y| ≥ 4`; `y` is not a chain vertex (those see `≤ 2` hubs), and its closed hub
neighbourhood is the same in `H′`. So the brief's "O7d at `m ≤ 4` on both arms" was Case 1 on one
arm only; what `hbareSplit` needs at `m ≤ 4` is entirely **O7e**, restated: irreducibility of
`X̄(H′)` when some marked vertex has `≥ 3` marked neighbours — the image of `X̄ → B` is the
concurrency locus of the big hyperedges, and both its irreducibility and a (★)-type bound over it
are open. (d) The count is `3`: O7e, O10, O11. **What would change this:** a pattern with
`cost ≤ J` (none among `64 325 + 73 969 + 55 831` on `229` sides); a gap in the relaxation
argument of (i) — the one place the proof touches geometry; or a habitat side violating the
count `5e(K) ≤ 6(v(K) − 1)` on a subgraph (S16(ii)), which every step leans on.
