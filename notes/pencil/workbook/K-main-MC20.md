## §(K-main) — Step MC20 — the coverage theorem's certificate leaves, proved by hand over every field

#### Step MC20 — the coverage theorem's certificate leaves, proved by hand over every field

*Worked 2026-09-24 by a read-only agent (the third 2026-09-24 session's Track I), prompted by the
(MC-26) erratum. **Second-read 2026-09-25** by a fresh reader, who re-derived (MC-134)–(MC-141) and
re-ran every driver. No refutation and no gap. The repairs, each marked where it sits:
- (MC-134)'s table justification was false in listed order in three rows, though the ranks were right;
- its `k ≥ 6` insertion collided adjacent points in characteristic `p ∣ J`;
- (MC-141) drew its "exactly mod (MC-33)(i)" conclusion while disclaiming an audit of the argument
  leaves for characteristic. The reader did that audit, (MC-166), and found no dependence, so the
  conclusion stands.

The reader also traced (MC-89)'s tree for completeness. Every computation it consumes is replaced;
the one uncredited *argument* leaf is (MC-47)(i)'s span identity, inside (MC-45)'s orbit-(iv)
branch, now credited. It added (MC-167), replays of the landed drivers' own streams, and (MC-168),
independent certificates in characteristics 2, 3 and 5 (`w4/charcheck.py`, `w4/thetareplay.py`,
`w4/lamreplay.py`, `w4/rowcheck.py`, `w4/treegrep.py`, `m2/earbad_p{2,3,5}.m2`). Hygiene:
`certhand.py`'s "Klein quadric = Q1 + Q2" line prints OK from a check that cannot fail. Drivers
`w4/certhand.py`, `w4/certguard.py`, `w4/orbitaudit.py`, `w4/certsearch.py` (new).*

**Verdict.**
- (MC-89) had four certificate leaves: `earstep.py --chains` (MC-19), `--thetas 5` (MC-21)(b),
  `--lamcap` ((MC-25), and (MC-45) at `r = 1`, via (MC-26)), and `earante.py --orbits` (MC-46).
  (MC-19)(b) at `k = 1` had neither a proof nor a driver row.
- **Each now has a hand proof valid over every infinite field.** Chain spans come from explicit
  configurations with `±1` maximal minors (MC-134). A transversal lemma gives `⋂Λ_k` at `k ≤ 3`
  (MC-135), and re-proves the (MC-26) erratum in two lines. A collision lemma gives `⋂Λ₄ = 0` in
  every orbit (MC-136). (MC-46)'s orbit table is done by hand (MC-138). (MC-21)(b) needs no
  per-graph computation (MC-139).
- **Driver audit** (MC-140):
  - `--lamcap` is wrong in the one cell already known;
  - `--thetas 5` never certifies `q ∈ U`, and a guarded re-run gives 30/30;
  - `--orbits` is silent in characteristic 2 at one stratum;
  - the rest are sound.
- **So (MC-89) rests only on arguments and on Jackson–Jordán at named graphs** (MC-141). Beyond
  characteristic 0, the qualifier is exactly "modulo (MC-33)(i)". This discharges the second
  reader's repair 2 to (MC-89).

**Notation.**

As in Step MC10 and Step MC13. The ear points are `p_a, x₁, …, x_k, p_b`, with `x₁ ∈ π_a`,
`x_k ∈ π_b` and the middle points free (`k = 1`: `x ∈ m = π_a ∩ π_b`). `Λ_k(x)` is the span of the
`k + 1` hinge lines, and `n = p_a p_b`. `⟨·,·⟩` is the Klein pairing on `Λ²K⁴`:
`c ∧ c′ = ⟨c, c′⟩ e₀₁₂₃`. For lines, `⟨x∧y, z∧w⟩ = det(x, y, z, w)`, and it vanishes iff the lines
meet. The pairing is nondegenerate over every field. `V^⊥` is the Klein-orthogonal complement, and
`π̂` is the 3-dimensional subspace of `K⁴` over the plane `π`. For subspaces `A, B ⊆ K⁴`,
`A ∧ B := span{a ∧ b}`.

The **orbit frames**, following (MC-92), with `p_a = e₀` and `p_b = e₃` throughout. PGL₄ acts
transitively on each orbit; the proof is at the end of (MC-138).

| orbit | `π_a` | `π_b` | `m = π_a ∩ π_b` |
|---|---|---|---|
| (i) | `⟨e₀,e₁,e₂⟩` | `⟨e₁,e₂,e₃⟩` | `⟨e₁,e₂⟩` |
| (ii) | `⟨e₀,e₂,e₃⟩ ∋ p_b` | `⟨e₁,e₂,e₃⟩` | `⟨e₂,e₃⟩` |
| (iii) | `⟨e₀,e₁,e₃⟩` | `⟨e₀,e₂,e₃⟩` | `n = ⟨e₀,e₃⟩` |
| (iv) | `⟨e₀,e₁,e₃⟩` | `= π_a` | — |

**How one exhibited value becomes the generic value.** Every placement space in question is
irreducible: a product of planes, lines and copies of `P³` (for `ρ`-conditions, its cone of
representative vectors).
- *Spans.* Rank is lower semicontinuous. So one exhibited configuration of rank `R` gives generic
  rank `≥ R`. When `R` is the trivial maximum, the generic rank is `R`. If some maximal minor of
  the exhibited integer configuration is `±1`, the same holds over every field.
- *Intersections.* "`c ∈ Λ(x)` for `x` in a dense set" is what failure of `(P_k)` at `r = 1`
  gives. It is used below only through identities valid at every point of that dense set, or
  through a polynomial in a curve parameter vanishing at infinitely many points. No finite family
  of draws is intersected.


**Part I — the dependency tree of (MC-89).**

Read from (MC-89)'s proof, (MC-79)(v)'s list of usable chains, and the owning claims.

| step of (MC-89) | claims it consumes | leaf kind |
|---|---|---|
| 1. CUT / BRIDGE | (MC-52), (MC-53), (MC-55)(ii) | argument |
| 2. BASE `C_n` | (MC-21)(a) ← (MC-16) (closed chain), (MC-17), **(MC-19)(a)** | argument + **certificate** `--chains` CH-1 → (MC-134) |
| 3. FLAT | (MC-5)(ii) ← (MC-4) | argument + JJ at `G` |
| 4. CONTRACT, maximal `def₂`-rigid core | (MC-75)(iii) → (MC-59)(d) ← (MC-59)(b), (c1)–(c3); FLAT at `H`; (MC-39) ← (MC-34)–(MC-38) | argument + JJ at `H`, `G/H` |
| 5a. THETA | **(MC-21)(b)**: `p₃ ≥ 6` by (MC-21)(a) + (MC-20); `p₃ ≤ 5` by 30 exhibited points | **certificate** `--thetas 5` → (MC-139) |
| 5b. 𝒮 | (MC-76), (MC-80) ← (MC-77), (MC-78), (MC-79)(i)–(iv) | argument |
| — chain `k ≥ 5` | (MC-20) ← (MC-18)(a), (MC-16), (MC-17), **(MC-19)(b)** `k ≥ 5` | **cert.** CH-2a/2b → (MC-134) |
| — chain `k = 4` | (MC-24), (MC-25) ← (MC-22), (MC-19)(b) `k = 2, 4`, **`⋂Λ₄ = 0`, four orbits** | **cert.** `--lamcap` → (MC-136) |
| — chain `k = 3` | (MC-45) ← (MC-22) twice, (MC-19)(b) `k = 2, 3`; `r = 1`: **`⋂Λ₃ = 0`, four orbits** (via (MC-26)); `r = 2`: splitting degeneration, and (MC-47)(i)'s span identity (orbit (iv)); `r ≥ 3`: (MC-26)'s link | **cert.** `--lamcap` → (MC-135); rest argument |
| — chain `k = 2`, `a ≁ b`, `δ₂ ≥ 2` | (MC-46) ← **orbit table + semi-invariance**, (MC-26)'s link (`r ≥ 4`), (MC-18)(b), **(MC-19)(b) `k = 1`**, (MC-22); `dim U ≥ 2` by (MC-48)(ii)'s argument | **cert.** `--orbits` → (MC-138); JJ at `G′ + ab` |
| — chain `k = 2`, `δ = 0` | (MC-54) ← (MC-19)(b), (MC-18)(a), (MC-16) | argument (+ (MC-134)) |
| — chain `k = 1`, `δ = 0` | (MC-54) ← (MC-18)(b), (MC-19)(b) `k = 1`; `dim U ≥ 2` | argument + JJ at `G′ + ab` |
| — chain `k = 1`, `δ ≥ 5` | SPLITOFF (MC-31) ← (MC-28), (MC-29), (MC-30)(iv) | argument + JJ at `G″ = G′ + ab` |
| — additive core | (MC-87) → (MC-71) ← (MC-68)(d), (MC-69)(b) ← (MC-69)(a), (MC-67); (MC-39) | argument + JJ at `H`, `G/H` |
| 6. coverage ⟹ attainment | (MC-56), (MC-55)(i), (MC-2) | argument |

Remarks on the tree:
- **(MC-19)(b) at `k = 1`** (`λ = 2` in orbits (i), (ii), (iv); `λ = 1` in (iii)) has no row in
  `--chains` and no proof in (MC-19)'s text. It is recorded only as the `λ` printed by
  `--lamcap` and `earspan.py` at `k = 1`. Its hand proof is in (MC-134).
- **(MC-19)(c)** (closed ears) is **not** in the tree. 𝒮 is 2-connected, CUT handles cut
  vertices, and BASE needs only the cycle. It is proved anyway in (MC-134).
- **(MC-26) at `k = 2`, `r = 1`** is used by (MC-85) and by (MC-88)'s corollary, neither of which
  (MC-89) uses. (MC-46)'s own count covers `r = 1` ("`B₂(1) = ∅`"). The cell is proved anyway in
  (MC-135), agreeing with (MC-92).
- **(MC-69)(a)** is an argument leaf. The (MC-89) author did not re-derive it; the second reader
  of (MC-89) did (commit `b0bc1341`), and `kerm0.py` (287 assertions) is the one computational
  cross-check.
- **`m2/earbad.m2`** is an independent symbolic re-check of (MC-46)'s classification (B2), not a
  leaf of its proof. Its (B3) supports (MC-47)(ii), which (MC-89) does not use.
- **No other computation hides in the tree.** `x0arms.py` and `coverstruct.py` assert proved
  identities at witnesses. The JJ "exhibitions" of Steps MC14/MC15 are replaced by the citation
  in (MC-89).


**Part II — the hand proofs.**

> **(MC-134)** `[PROVED]` *(the chain spans (MC-19), over every field)* **(a)** A generic closed polygon
> with `n` edges has hinge span `min(n, 6)`. **(b)** Take any flag pair with `p_a ≠ p_b`. A generic
> open `k`-ear placement has `λ = min(k + 1, 6)` for `k ≥ 2`. At `k = 1`, `λ = 2` in orbits (i),
> (ii), (iv) and `λ = 1` in (iii). **(c)** A generic closed `k`-ear placement (`k ≥ 2`) has
> `λ = min(k + 1, 6)`.

*Proof.* By the principle above, one configuration per case with a `±1` maximal minor suffices.
Write `f := e₀ + e₁ + e₂`.

**Frames.**
- *(b), `π_a ≠ π_b`.* Choose `x₁ ∈ π_a` and `x_k ∈ π_b` with `p_a, x₁, x_k, p_b` not coplanar;
  such a choice exists in each orbit. Put `σ := ⟨p_a, x₁, p_b⟩`, with `x₁ ∉ n`; a generic
  `x_k ∈ π_b` is off `σ` as soon as `σ ≠ π_b`:
  - (i): `σ ≠ π_b`, because `p_a ∉ π_b`;
  - (iii), and (ii) with `p_b ∈ π_a`: `σ = π_a ≠ π_b`;
  - (ii) with `p_a ∈ π_b`: take `x₁ ∉ π_b`, so `σ ≠ π_b`.

  Four non-coplanar points have no three collinear. PGL₄ sends them to `e₀, e₁, e₂, e₃`, and the
  middle points stay free.
- *(b), `π_a = π_b = π`.* `p_a, x₁, x_k, p_b` are four points of `π`, no three collinear. They go
  to `e₀, e₁, e₂, f` in `{X₃ = 0}`.
- *(c).* `p_a, x₁, x_k` are three non-collinear points of `π_a`. They go to `e₀, e₁, e₂`.

Configurations (Plücker order `01,02,03,12,13,23`). Each row lists the resulting line vectors,
in chain order:

| case | points | line vectors |
|---|---|---|
| (a) `n = 3` | `e₀, e₁, e₂` | `e₀₁, e₁₂, e₀₂` |
| (a) `n = 4` | `e₀, e₁, e₂, e₃` | `e₀₁, e₁₂, e₂₃, e₀₃` |
| (a) `n = 5` | `e₀, e₁, e₂, e₃, e₁+e₃` | `e₀₁, e₁₂, e₂₃, e₁₃, e₀₁+e₀₃` |
| (a) `n = 6` | `e₀, e₁, e₂, e₃, e₁+e₃, e₀+e₂` | `e₀₁, e₁₂, e₂₃, e₁₃, −e₀₁+e₁₂−e₀₃−e₂₃, e₀₂` |
| (b) `k = 2`, `π_a ≠ π_b` | `e₀, e₁, e₂, e₃` | `e₀₁, e₁₂, e₂₃` |
| (b) `k = 3` | `e₀, e₁, e₁+e₃, e₂, e₃` | `e₀₁, e₁₃, e₁₂−e₂₃, e₂₃` |
| (b) `k = 4` | `e₀, e₁, e₃, e₀, e₂, e₃` | `e₀₁, e₁₃, e₀₃, e₀₂, e₂₃` |
| (b) `k = 5` | `e₀, e₁, e₃, e₀, e₁+e₂, e₂, e₃` | `e₀₁, e₁₃, e₀₃, e₀₁+e₀₂, e₁₂, e₂₃` |
| (b) `k = 2`, `π_a = π_b` | `e₀, e₁, e₂, f` | `e₀₁, e₁₂, e₀₂+e₁₂` |
| (b) `k = 3` | `e₀, e₁, e₃, e₂, f` | `e₀₁, e₁₃, e₂₃, e₀₂+e₁₂` |
| (b) `k = 4` | `e₀, e₁, e₃, e₀, e₂, f` | `e₀₁, e₁₃, e₀₃, e₀₂, e₀₂+e₁₂` |
| (b) `k = 5` | `e₀, e₁, e₃, e₂+e₃, e₀, e₂, f` | `e₀₁, e₁₃, e₂₃, e₀₂+e₀₃, e₀₂, e₀₂+e₁₂` |
| (c) `k = 2` | `e₀, e₁, e₂` (closed) | `e₀₁, e₁₂, e₀₂` |
| (c) `k = 3` | `e₀, e₁, e₃, e₂` | `e₀₁, e₁₃, e₂₃, e₀₂` |
| (c) `k = 4` | `e₀, e₁, e₃, e₁+e₂, e₂` | `e₀₁, e₁₃, e₁₃+e₂₃, e₁₂, e₀₂` |
| (c) `k = 5` | `e₀, e₁, e₁+e₂, e₃, e₀+e₃, e₂` | `e₀₁, e₁₂, e₁₃+e₂₃, e₀₃, e₀₂−e₂₃, e₀₂` |

(Signs are dropped where a vector is a basis vector up to sign.) In each row, in a suitable order,
every vector brings in a coordinate the earlier ones lack, so the rank is the row length, with a
`±1` minor. The chain order already works except in three rows, where one basis vector moves ahead
of the vector it occurs in: `e₂₃` in (b) `k = 3`, `π_a ≠ π_b`; `e₀₂` in (b) `k = 5`, `π_a = π_b`;
`e₀₂` in (c) `k = 5`. *(Repaired at the second reading, 2026-09-25, `rowcheck.py`: as first
written, the listed-order claim was false in those three rows.)*
`certhand.py` (MC-134) asserts each rank and finds a `±1` maximal minor. A middle point may coincide with
a terminal point (`k = 4, 5`); that is a legitimate point of the free factor `P³`, and adjacent
points are distinct.

- *`n ≥ 7`, `k ≥ 6`.* Insert the extra points on an existing hinge line between two middle points
  of the `n = 6` or `k = 5` configuration: for (b) with `π_a ≠ π_b`, on `e₃e₀`, the points
  `e₀ + t_j e₃` with `t_j ∈ K` distinct and nonzero; with `π_a = π_b`, on `e₃(e₂ + e₃)`. The new
  lines are multiples of an old one, so the span stays `K⁶`. (`t_j = j` would put two adjacent
  points together in characteristic `p ∣ J`; the span would not change. *Repaired at the second
  reading, 2026-09-25*; the same choice serves (a).)
- *`k = 1`.* `λ = 2` iff `x ∉ n`.
  - Orbit (i): `m ∩ n ⊆ n ∩ π_b = {p_b}` (as `p_a ∉ π_b`), and `p_b ∉ m` (as `p_b ∉ π_a ⊇ m`).
    So `m ∩ n = ∅`.
  - Orbit (ii): `m ∩ n = {p_b}`, and `x ∈ m ∖ {p_b}`.
  - Orbit (iv): `x ∈ π ∖ n`.
  - Orbit (iii): `m = n`, so `λ = 1`. ∎

> **(MC-135)** `[PROVED]` *(the transversal lemma, and the intersections at `k ≤ 3`)*
> **(i)** For every `k`-ear placement with `k ∈ {2, 3}`, the line `x₁x_k` meets every hinge line,
> so `x₁ ∧ x_k ∈ Λ_k(x)^⊥`. In orbit (iv) at `k = 3`, let `z := (p_a x₁) ∩ (x₃ p_b)`, a point of
> `π`. Then also `x₂ ∧ z ∈ Λ₃(x)^⊥`.
> **(ii)** Let `c ∈ Λ²K⁴`, and let `c ∈ Λ_k(x)` for all `x` in a dense subset of the placement
> space. Then `c = 0` for `k = 3` in all four orbits and for `k = 2` in orbits (i)–(iii). For
> `k = 2` in orbit (iv), `c ∈ Λ²π`. For `k = 1`, `c = 0` in orbits (i) and (iv), and `c ∈ ⟨m⟩`
> in orbit (ii). All of these are equalities: `⋂Λ₂ = Λ²π` in orbit (iv), and `⋂Λ₁ = ⟨m⟩` in
> orbit (ii) ((MC-97); `⟨m⟩ ⊆ Λ₁(x)` for every `x`). In orbit (iii) at `k = 1`, `Λ₁ = ⟨n⟩` is
> constant.

*Proof.* **(i)** `x₁x_k` meets `p_a x₁` and `x₁x₂` at `x₁`. It meets `x_{k−1}x_k` and `x_k p_b` at
`x_k`. For `k = 2` it is the middle line itself; for `k = 3` those four are all the lines. In
orbit (iv), `x₂z` meets `p_a x₁` and `x₃ p_b` at `z`, and `x₁x₂`, `x₂x₃` at `x₂`.

**(ii)**
- **`k = 3`, orbits (i)–(iii).** By (i), `⟨c, x₁ ∧ x₃⟩ = 0` on a dense set of placements. The form
  `(x₁, x₃) ↦ ⟨c, x₁ ∧ x₃⟩` is bilinear on `π̂_a × π̂_b`, so it vanishes identically, and
  `c ⊥ π̂_a ∧ π̂_b`. When `π_a ≠ π_b`, write `π̂_a = m̂ ⊕ ⟨α⟩` and `π̂_b = m̂ ⊕ ⟨β⟩` with
  `m̂ = ⟨f₁, f₂⟩`. Then `π̂_a ∧ π̂_b ∋ f₁∧f₂, α∧f₁, α∧f₂, f₁∧β, f₂∧β, α∧β`, a basis of `Λ²K⁴`. So
  `c = 0`.
- **`k = 3`, orbit (iv).** The same argument with `x₂ ∧ z` gives `⟨c, x₂ ∧ z⟩ = 0` on a dense set.
  Every `z ∈ π ∖ n` arises (take `x₁ ∈ p_a z`, `x₃ ∈ p_b z`), and `x₂ ∈ P³` is free. So
  `c ⊥ K⁴ ∧ π̂ = Λ²K⁴`, and `c = 0`.
- **`k = 2`.** The same argument with `x₁ ∧ x₂` gives `c ⊥ π̂_a ∧ π̂_b`. That is `c = 0` in orbits
  (i)–(iii), and `c ∈ (Λ²π)^⊥ = Λ²π` in orbit (iv). There `Λ₂ = Λ²π` at every placement of
  generic span ((MC-47)(i); the span drops to `⟨n⟩` when `x₁, x₂ ∈ n`), which gives equality.
- **`k = 1`.** `Λ₁(x) = ⟨p_a∧x, x∧p_b⟩`, and every line through `x` meets both lines, so
  `star(x) ⊆ Λ₁(x)^⊥`. Over a dense set of `x ∈ m`, this gives `c ⊥ m̂ ∧ K⁴`, the lines meeting
  `m`, so `c ∈ (m̂ ∧ K⁴)^⊥ = ⟨m⟩`.
  - In orbit (i), the lines of the plane `⟨p_a, x, p_b⟩` also meet both lines. As `x` runs over
    `m`, that plane runs over the planes through `n`, so `c ⊥ n̂ ∧ K⁴` and `c ∈ ⟨n⟩`. Since
    `⟨m⟩ ∩ ⟨n⟩ = 0`, `c = 0`.
  - In orbit (iv), `x` runs over `π`, so `c ⊥ π̂ ∧ K⁴ = Λ²K⁴`, and `c = 0`.
  - In orbit (ii), `p_b ∈ m`, so `x ∧ p_b ∝ m` and `m ∈ Λ₁(x)` for every `x`. ∎

`certhand.py` (MC-135) asserts the orthogonalities at explicit placements in each orbit. It exhibits a
`±1` determinant among the generators of `π̂_a ∧ π̂_b` (orbits (i)–(iii)) and of `K⁴ ∧ π̂`
(orbit (iv)). It also recomputes the `k = 1` values from three explicit points.

> **(MC-136)** `[PROVED]` *(the collision lemma: `⋂Λ₄ = 0` in all four orbits)* Let `c ∈ Λ₄(x)` for all
> `x` in a dense open subset of the 4-ear placements. Then `c = 0`.

*Proof.* Fix a generic 3-placement `y = (y₁, y₂, y₃)`, which has `λ₃ = 4` by (MC-134), and
`u ∈ K⁴`.

*First collision* (used in orbits (i)–(iii)).
- For `t ≠ 0`, `x(t) := (y₁, y₁ + tu, y₂, y₃)` is a 4-placement: `x₁ = y₁ ∈ π_a`, the two middle
  points are free, and `x₄ = y₃ ∈ π_b`.
- Since `y₁ ∧ (y₁ + tu) = t·y₁ ∧ u`, `Λ₄(x(t))` is the row space of
  `R(t) := [p_a∧y₁; y₁∧u; (y₁+tu)∧y₂; y₂∧y₃; y₃∧p_b]`, which is polynomial in `t`.
- `(y₁, u, y₂, y₃, t) ↦ x(t)` is an isomorphism for each fixed `t ≠ 0`. So for generic
  `(y, u)`, `x(t)` lies in the given dense open set for all but finitely many `t`.
- There `det[R(t); c] = 0`. This is a polynomial in `t` with infinitely many zeros, hence zero at
  `t = 0`.
- Suppose `rank R(0) = 5`. Then `c ∈ rowspace R(0) = Λ₃(y) + ⟨y₁∧u⟩`. The line `y₁y₃` meets all
  five rows of `R(0)`, at `y₁` or at `y₃`. So `⟨c, y₁ ∧ y₃⟩ = 0` for generic `(y₁, y₃)`. As in
  (MC-135), `c ⊥ π̂_a ∧ π̂_b = Λ²K⁴`, so `c = 0`.

*Why `rank R(0) = 5`.* We need `y₁ ∧ u ∉ Λ₃(y)` for generic `u`, that is, `star(y₁) ⊄ Λ₃(y)`.
- In orbits (i)–(iii) the lines `p_a y₁` and `y₃ p_b` are skew for generic `y`:
  - in (i), they would meet on `m`, and their traces on `m` differ;
  - in (ii) and (iii), `y₃ p_b` meets `π_a` only at `p_b`, and `p_b ∉ p_a y₁`.
- So a unique transversal `t₂` through `y₂` meets both. It meets `y₁y₂` and `y₂y₃` at `y₂`, so
  `t₂ ∈ Λ₃(y)^⊥`.
- If `star(y₁) ⊆ Λ₃(y)`, then `t₂` would meet every line through `y₁`, so `t₂ ∋ y₁`. Then
  `y₁y₂` would meet `y₃p_b`, which makes `y₁, y₂, y₃, p_b` coplanar, false generically.

*Second collision* (orbit (iv)). Take `x(t) := (y₁, y₂ + tu, y₂, y₃)`, colliding the two middle
points.
- Here `(y₂ + tu) ∧ y₂ = t·u ∧ y₂`, so
  `R(0) = [p_a y₁; y₁ y₂; u∧y₂; y₂ y₃; y₃ p_b]`.
- It has rank 5 by the same reasoning. `y₁ ∧ y₃ ∈ Λ₃^⊥` by (MC-135)(i), and `y₁y₃ ∌ y₂`, so
  `star(y₂) ⊄ Λ₃`.
- The line `y₂z` of (MC-135)(i) meets all five rows (at `z` or at `y₂`). So `⟨c, y₂ ∧ z⟩ = 0`
  generically, and `c = 0` as in (MC-135) orbit (iv). ∎

`certhand.py` (MC-136) exhibits one point `(y, u)` per orbit where the genericity used here holds:
`λ₃ = 4`, `rank R(0) = 5`, and the transversal is orthogonal to every row. Two first-choice
points were themselves degenerate: `y₁, y₂, y₃, p_b` coplanar in orbit (ii), and `u` in the
plane `⟨y₁, y₂, y₃⟩` in orbit (iv). The asserts caught both, which is the guard `--lamcap`
lacked. The points were changed.

> **(MC-137)** `[PROVED]` *(what (MC-135), (MC-136) give the landed claims)*
> **(a)** (MC-25)'s "`⋂Λ₄ = 0` in all four orbits", hence `(P₄)` for every `ρ`.
> **(b)** The `r = 1` case of (MC-45), in all four orbits.
> **(c)** (MC-26)'s `r = 1` sentence, corrected and proved: at `r = 1`, `(P_k)` holds for every
> `ρ`, except:
> - orbit (iv) at `k = 2`, where `(P₂)` fails exactly for `ρ ⊆ Λ²π`;
> - orbit (ii) at `k = 1`, where `(P₁)` fails exactly for `ρ = ⟨m⟩` ((MC-97));
> - orbit (iii) at `k = 1`, which lies outside (MC-22) (`λ = 1`).

*Proof.* At `r = 1`, `(P_k)` asks `ρ ∩ Λ_k(x) = 0` at the generic placement. If it fails, a
nonzero `c ∈ ρ` lies in `Λ_k(x)` on a dense open set. Apply (MC-135) or (MC-136).
- For (a) at `r ≥ 1`: `Λ₄` is a hyperplane, and `(P₄)` fails iff `ρ ⊆ Λ₄(x)` generically. Take
  any nonzero `c ∈ ρ`. ∎

> **(MC-138)** `[PROVED]` *((MC-46)'s orbit-dimension table, the open orbit, and the semi-invariance,
> over every field)*
> **Orbit (i).** `S = {diag(λ, A, μ)}` with `A ∈ GL(⟨e₁,e₂⟩)`, modulo scalars, so `dim S = 5`.
> `S` has the open orbit `{(αe₀ + u, v + βe₃) : αβ ≠ 0, u ∧ v ≠ 0}` on 2-ear placements, the
> orbit of `x⁰ = (e₀+e₁, e₂+e₃)`.
> **Orbit (ii).** `S = {g : e₀ ↦ λe₀, e₁ ↦ αe₁+βe₂+γe₃, e₂ ↦ νe₂+ξe₃, e₃ ↦ μe₃}` modulo scalars,
> so `dim S = 6`. `S` has the open orbit of `x⁰ = (e₀+e₂, e₁)`: `x₁ ∉ m ∪ n`, `x₂ ∉ m`.
> **The table**, for `y = [l₀L₀ + l₁L₁ + l₂L₂] ∈ P(Λ₂(x⁰))` and `d_y := dim S·y`, is exactly
> (MC-46)'s:
> - orbit (i): `d_y = 4` where `l₁ ≠ 0`; `3` on `l₁ = 0`; `1` at `L₀` and `L₂`;
> - orbit (ii): `d_y ≥ 5` where `l₀l₁l₂ ≠ 0`; `≥ 4` where `l₀l₂ = 0 ≠ l₁`; `≥ 3` on `l₁ = 0 ≠ l₀l₂`; `≥ 1`
>   at `L₀`, `L₂`.
>
> In orbit (i) the values are exact. In orbit (ii) they are lower bounds, and lower bounds are all
> (MC-46)'s count uses (fibre dimension `= dim S − d_y` plus the incidence term). The containments
> the count uses also hold: `S·y ⊆ P(N)` on `l₁ = 0`, `S·L₀ ⊆ P(Pen_a)` and `S·L₂ ⊆ P(Pen_b)`. And
> `Q₁`, `Q₂` are semi-invariants of one character.

*Proof, orbit (i).* `S` fixes `⟨e₀⟩` and `⟨e₃⟩`, and preserves `π̂_a`, `π̂_b` and so `m̂ = ⟨e₁,e₂⟩`.
Those conditions define `diag(λ, A, μ)`.
- *Open orbit.* `g x⁰ = (λe₀ + Ae₁, Ae₂ + μe₃)`. Given `(αe₀ + u, v + βe₃)` with `αβ ≠ 0` and
  `u ∧ v ≠ 0`, take `λ = α`, `Ae₁ = u`, `Ae₂ = v`, `μ = β`.
- *Chain lines.* `L₀ = e₀₁`, `L₁ = e₀₂ + e₀₃ + e₁₂ + e₁₃`, `L₂ = e₂₃`.
- *Decomposition.* Write `c = a·e₀₃ + b·e₁₂ + e₀∧u + w∧e₃` with `u, w ∈ m̂`. Then
  `g·c = (λμa, det A·b, λAu, μAw)`. The point `y` has `a = b = l₁`, `u = l₀e₁ + l₁e₂` and
  `w = l₁e₁ + l₂e₂`.
- *`l₁ ≠ 0`.* `g·y = κy` forces `κ = λμ = det A`, `Au = μu` and `Aw = λw`.
  - If `u ∧ w ≠ 0`, `A` is determined by `(λ, μ)`, with `det A = λμ` automatically.
  - If `w = τu`, then `λ = μ` and `A = λI + N` with `Nu = 0`, one parameter `s`.

  Either way the stabiliser has dimension 2 in GL₄, 1 in `S`, so `d_y = 4`.
- *`l₁ = 0`, `l₀l₂ ≠ 0`.* `y = (0, 0, l₀e₁, l₂e₂)`. The stabiliser is `A` diagonal with `λ, μ, κ`
  free, dimension 2 in `S`, so `d_y = 3`. `S·y = {(0, 0, u′, w′) : u′∧w′ ≠ 0}` is open in
  `P(e₀∧m̂ ⊕ m̂∧e₃) = P(N)`.
- *`L₀ = e₀₁`.* `S·L₀ = P(e₀∧m̂) = P(Pen_a)`, of dimension 1. `L₂` is symmetric.
- *Semi-invariants.* `Q₁ := ab = c₀₃c₁₂` and `Q₂ := det[u|w] = c₀₁c₂₃ − c₀₂c₁₃` both scale by
  `λμ·det A` under `g`. On `P(Λ₂(x⁰))`, `Q₁(y) = l₁²` and `Q₂(y) = l₀l₂ − l₁²`. So `I(y)` is
  non-constant, with conic level sets, and `S·y` misses `{Q₁ = 0}` when `l₁ ≠ 0`. These are the
  facts (MC-46)'s orbit-(i) generic stratum uses.

*Proof, orbit (ii).* `S` fixes `⟨e₀⟩` and `⟨e₃⟩`, and preserves `π̂_a = ⟨e₀,e₂,e₃⟩`,
`π̂_b = ⟨e₁,e₂,e₃⟩` and `m̂ = ⟨e₂,e₃⟩`: 7 parameters.
- *Open orbit.* `g x⁰ = (λe₀ + νe₂ + ξe₃, αe₁ + βe₂ + γe₃)`, which reaches every
  `(e₀ + se₂ + te₃, x₂)` with `s ≠ 0` and `x₂ ∉ m`.
- *Chain lines.* `L₀ = e₀₂`, `L₁ = e₀₁ − e₁₂`, `L₂ = e₁₃`.
- *Tangent vectors.* A lower bound for `d_y` in every characteristic is
  `rank{y, Xy : X ∈ Lie S} − 1`: the orbit has dimension at least the rank of its orbit map's
  differential. With `E_ij : e_j ↦ e_i` acting as derivations on
  `y = l₀e₀₂ + l₁(e₀₁ − e₁₂) + l₂e₁₃`:
  - `E₀₀y = l₁e₀₁ + l₀e₀₂`;
  - `E₁₁y = l₁e₀₁ − l₁e₁₂ + l₂e₁₃`;
  - `E₂₁y = l₁e₀₂ + l₂e₂₃`;
  - `E₃₁y = l₁e₀₃ + l₁e₂₃`;
  - `E₂₂y = l₀e₀₂ − l₁e₁₂`;
  - `E₃₂y = l₀e₀₃ − l₁e₁₃`;
  - `E₃₃y = l₂e₁₃`.
- *`l₀l₁l₂ ≠ 0`.* The six vectors `E₀₀y, E₂₁y, E₃₂y, E₂₂y, E₃₃y, E₃₁y` have determinant
  `−l₀l₁⁴l₂`: pivots `e₁₃ (l₂), e₀₃ (l₀), e₂₃ (l₁), e₀₂ (l₁), e₁₂ (−l₁), e₀₁ (l₁)`. So `d_y ≥ 5`.
- *`l₂ = 0 ≠ l₀l₁`.* `E₂₁y, E₀₀y, E₁₁y, E₃₂y, E₃₁y` on the columns `02, 01, 12, 13, 23` are
  triangular with diagonal `±l₁`. So `d_y ≥ 4`.
- *`l₀ = 0 ≠ l₁`.* `E₀₀y, E₂₂y, E₃₂y, E₂₁y, E₃₁y` on the columns `01, 12, 13, 02, 03` are
  triangular with diagonal `±l₁`. So `d_y ≥ 4`. This includes `L₁`.
- *`l₁ = 0 ≠ l₀l₂`.* `E₀₀y = l₀e₀₂`, `E₃₂y = l₀e₀₃`, `E₁₁y = l₂e₁₃`, `E₂₁y = l₂e₂₃`, so
  `d_y ≥ 3`, and `y ∈ N = ⟨e₀₂, e₀₃, e₁₃, e₂₃⟩`, which `S` preserves.
- *`L₀`, `L₂`.* Two vectors each: `e₀₂, e₀₃` and `e₁₃, e₂₃`. ∎

*The frames are general.*
- *Orbit (i).* Take `e₀ = p_a`, `e₃ = p_b` and `e₁, e₂` spanning `m`. They are independent, since
  `p_a, p_b ∉ m` and `p_b ∉ π_a`.
- *Orbit (ii).* Take `e₃ = p_b`, `e₂ ∈ m ∖ p_b`, `e₀ = p_a` and `e₁ ∈ π_b ∖ m`.
- *Orbits (iii), (iv).* Take `e₀ = p_a`, `e₃ = p_b` and `e₁ ∈ π_a ∖ n`. For (iii),
  `e₂ ∈ π_b ∖ n`; for (iv), `e₂ ∉ π`.

`certhand.py` (MC-138) certifies every stratum's lower bound by a monomial minor with coefficient `±1`,
with `y` itself among the tangent vectors. It checks the open orbits, and the semi-invariance as a
polynomial identity in the group parameters.

> **(MC-139)** `[PROVED]` *((MC-21)(b) without the 30 certificates)* Every simple θ-graph
> `θ(p₁, p₂, p₃)` attains on `X₀`. The proof uses (MC-21)(a), (MC-20), (MC-25), (MC-45), (MC-54)
> and (MC-5)(iii), with their leaves (MC-18)(a), (MC-22), (MC-24), (MC-134) and (MC-137)(a), (b),
> and no per-graph computation.

*Proof.* Strong induction on `|V|`. Order `p₁ ≤ p₂ ≤ p₃`, so `p₃ ≥ p₂ ≥ 2` (simple). Let `G′`
be the cycle `C_s`, `s = p₁ + p₂ ≥ 3`, with `a, b` at distance `p₁` on it, and attach the
`p₃`-path as an open ear with `k = p₃ − 1 ≥ 1` interior vertices. `X₀(C_s)` attains by (MC-21)(a).
- *`k ≥ 5`.* (MC-20).
- *`k = 4` or `3`.* (MC-25) or (MC-45). Both hold in every flag orbit, so `a ∼ b` (`p₁ = 1`) is
  allowed. Their antecedent is `X₀(G′ + ear₂) = X₀(θ(p₁, p₂, 3))`. That graph is simple and has
  `s + 2 < s + k` vertices, so it attains by induction. Their `r = 1` leaves are (MC-137)(a), (b).
- *`k = 2`.* Then `p₁ ≤ p₂ ≤ 3`, so `s ≤ 6`, `def₃(C_s) = max(0, s − 6) = 0`, and `δ ∈ [0, 0]`.
  (MC-54) applies, needing only (MC-19)(b) and (MC-18)(a).
- *`k = 1`.* The graph is `θ(1,2,2) = K₄ − e` or `θ(2,2,2) = K_{2,3}`.
  - In `K₄ − e`, a hub's closed neighbourhood is all of `V`.
  - In `K_{2,3}`, the two hubs' interpolants agree at the three degree-2 vertices, which are
    non-collinear at an admissible `q` in a dense open set.

  Either way `L(q) = Aff(q)`, so `ℓ₀ = 3`, and (MC-5)(iii) gives attainment. ∎

This also removes THETA as a separate kind of step: it is BASE plus EAR. `certguard.py --thetas 5`
prints each of the 30 small graphs' case, and checks `δ = 0` at `k = 2` and `dim L = 3` at
`k = 1`.


**Part III — the certificate drivers audited.**

> **(MC-140)** *(verdicts; the bug class is "a random draw whose degeneracy would bias the statistic
> toward the claim")*

| driver | what it certifies | verdict | evidence |
|---|---|---|---|
| `earstep.py --chains` | (MC-19): 16 rows (CH-1 closed polygons `n = 3..6`; CH-2a, CH-2b open ears and CH-3 closed ears, `k = 2..5`) | **sound** | Each row is one configuration, and full rank is a lower bound equal to the trivial maximum. A degenerate draw could only print FAIL. Frames are valid normalizations. Exact ℚ; the prime coverage of its random middle points is unspecified. Superseded by (MC-134). |
| `earstep.py --thetas 5` | (MC-21)(b), 30 θ-graphs | **sound-but-unguarded** | The mod-`2⁶¹−1` rank is a valid lower bound. But `maincomp.probe` never certifies `q ∈ U`: `dim L(q)` is not compared with `ℓ₀`. So the attaining point is a pencil configuration not certified to lie on `X₀` ((MC-2)'s remark on jump strata). `certguard.py --thetas 5` certifies `q ∈ U` by `dim L(q) = 3 + def₂` and computes exact ℚ ranks: **30/30 attain**. Superseded by (MC-139). A replay of the driver's own stream (`thetareplay.py`, the second reading) finds `dim L(q) = 3 + def₂` at all 30 accepted draws, so the landed 30/30 were certificates as they stand; what was missing is the assert. |
| `earstep.py --lamcap` | (MC-25), (MC-26): `⋂Λ_k` over 12 unguarded draws | **wrong in one cell**: orbit (ii), `k = 1` prints `0`, the truth is `⟨m⟩` | The intersection is unguarded; its docstring's "an intersection of 0 is a proof" is false without a span guard. `certguard.py --replay`: span-deficient draws at (ii) `k = 1, 2, 3` (1 of 12 each) and (iv) `k = 1` (1 of 12). Only (ii) `k = 1` gives a false value. `certguard.py --lamcap` (24 accepted draws, deficient ones rejected and counted) gives every cell the hand value of (MC-135)/(MC-136). Agrees with (MC-97). Over its span-generic draws only, the driver's own stream gives the hand value in all 16 cells (`lamreplay.py`, the second reading); the wrong print comes only from the one deficient draw at (ii) `k = 1`. The guarded re-run first landed as `lamguard.py` (Step MC17). |
| `earante.py --orbits` | (MC-46)'s table; transitivity; semi-invariance | **sound over ℚ; silent in characteristic 2 at one stratum** | Exact symbolic minors. But the generators include `E₀₀, …, E₃₃`, whose sum acts on `Λ²` by `2` and stands in for the cone direction `y`. `orbitaudit.py`: for orbit (i)'s generic stratum `l₀l₁ ≠ 0`, the driver's certifying minor has coefficient `−2`, and every certifying monomial minor there has `|coefficient| = 2`. Its "none of size `s+1`" half is a Lie-algebra bound, an orbit-dimension bound only in characteristic 0; the count does not use it. The semi-invariance is checked at 5 random group elements, a check rather than a proof. (MC-138) proves all three in every characteristic. |
| `earante.py --frames` | (MC-43)/(MC-46)/(MC-47) families | **sound as a check** | "good" is certified: a placement with `λ = j+1` and the least `dim(ρ ∩ Λ)`. "BAD" means not seen good in `T = 4` draws, a measurement. It agrees with the proved inclusions and is not an input to (MC-89). The workbook's "the families bad" is stronger than the driver shows; the badness is proved by (MC-43), (MC-46), (MC-47). |
| `m2/earbad.m2` | (MC-45) `r = 2` inclusion; (MC-46) classification; (MC-47)(ii) | **sound** (characteristic 0) | Placement coordinates are indeterminates, so "`ρ ∩ Λ ≠ 0` at every placement" is an exact linear condition. There is no randomness. Valid where the generic `λ = j + 1`, which holds in every case it uses. Not a leaf of (MC-89). Ported to `ZZ/2`, `ZZ/3`, `ZZ/5` by changing only the coefficient field (`m2/earbad_p{2,3,5}.m2`), (B0)–(B4) pass unchanged (the second reading). |
| `earspan.py` | `λ` per orbit, `k ≤ 4`; `⋂Λ₄` | **sound** | The `⋂Λ₄` loop asserts `λ = 5` at every draw, so a deficient draw would crash, not bias. |


**Part IV — what (MC-89) now rests on.**

> **(MC-141)** `[PROVED-MOD]` *((MC-33); the leaves of (MC-89), after (MC-134)–(MC-139); a statement about the
> tree, conditional on the argument leaves as landed; second-read 2026-09-25, which also audited
> those leaves for characteristic, (MC-166))*
> (MC-89) rests on:
> - **arguments:** every claim in Part I's table, with (MC-19), (MC-21)(b), (MC-25)'s and
>   (MC-45)'s `r = 1` cells, and (MC-46)'s table now proved by (MC-134)–(MC-139), and the argument
>   leaves those claims cite (among them (MC-13)(a), (b), the union lemma in (MC-14)'s proof,
>   (MC-26)'s two links and (MC-47)(i)'s span identity);
> - **JJ** at the simple graphs:
>   - `G` itself at FLAT (`def₂ = def₃`);
>   - `H = G[W]` and `G/H` at both kinds of CONTRACT;
>   - `G′ + ab` at usable chains needing `dim U ≥ 2` (`k = 2` with `δ ≥ 1` and `a ≁ b`; `k = 1`
>     with `δ = 0`);
>   - `G″ = G′ + ab` at SPLITOFF.
>
>   Every one except FLAT's `G` has fewer vertices than `G`.
> - **no computational certificate.** The former certificate leaves hold over every infinite
>   field. The argument leaves use of `K` only that it is an infinite field ((MC-166), the second
>   reader's audit). So beyond characteristic 0 the qualifier is exactly "mod (MC-33)(i)".
>   *(Repaired at the second reading: as first written, this bullet drew that conclusion while
>   saying the argument leaves "were not audited for characteristic".)*

> **(MC-166)** `[INFORMAL]` *(gap: a reading-level audit of where the field enters, not a fresh
> re-derivation of steps already second-read; the second reader's, 2026-09-25)* Across every
> argument leaf of (MC-89)'s tree, `K` enters only in three ways:
> - nonzero elements are inverted (the plane coefficient in (MC-1), pivots, (MC-30)(ii)'s
>   denominator, the rescalings by `t ≠ 0`);
> - `K` is infinite (open sets have `K`-points; a nonzero one-variable polynomial has finitely many
>   roots: (MC-2), (MC-30), (MC-36), (MC-136));
> - rank and kernel dimension are semicontinuous, and Grassmannian limits are taken.
>
> No integer is divided by: the integer arithmetic of (MC-17), (MC-29), (MC-48)(i), (MC-75)–(MC-80)
> and (MC-87) is on graph counts, not in `K`. No differential is used as an upper bound, and
> `c ∧ c = 0` is never used as the line test (it fails in characteristic 2). (MC-45)'s and (MC-46)'s
> quadric arguments hold in every characteristic. The only characteristic-dependent input is
> Jackson–Jordán, (MC-33)(i).
>
> *Scope:* Part I's table with (MC-1)–(MC-5), (MC-13)(a), (b), (MC-14)'s union lemma, (MC-16)–(MC-18),
> (MC-20)–(MC-22), (MC-24), (MC-26)'s links, (MC-28)–(MC-31), (MC-34)–(MC-39), (MC-45), (MC-46), (MC-47)(i)'s
> span identity, (MC-48)(ii)'s count, (MC-52)–(MC-56), (MC-59), (MC-62), (MC-63), (MC-67)–(MC-71),
> (MC-75)–(MC-80) and (MC-87).

> **(MC-167)** `[CONSTRUCTED]` *(`thetareplay.py`, `lamreplay.py`; replays of the landed drivers'
> own random streams, importing them unchanged)*
> - **(a)** All 30 draws that `earstep.py --thetas 5` accepted have `dim L(q) = 3 + def₂`, so they
>   lie in `U`.
> - **(b)** Over its span-generic draws only, the landed `--lamcap` stream gives the hand value in
>   all 16 cells. Four draws drop out, one each at (ii) `k = 1, 2, 3` and (iv) `k = 1`. The wrong `0`
>   printed at (ii) `k = 1` comes only from the deficient draw.
>
> `PYTHONHASHSEED=0 python3 notes/scripts/w4/thetareplay.py` (< 1 s); `… lamreplay.py` (< 1 s).

> **(MC-168)** `[CONSTRUCTED]` *(`charcheck.py`, seeded and exact over finite fields;
> `m2/earbad_p{2,3,5}.m2`)* Independent certificates in positive characteristic:
> - **(a)** The 16 (MC-134) configurations, and the insertion to `k = 6..9`, have the claimed rank
>   over GF(2), GF(3), GF(5), GF(7) and GF(2⁸).
> - **(b)** The guarded `⋂Λ_k` equals the hand value in all 16 cells: over GF(2) at every placement
>   for `k ≤ 4`; over GF(3) and GF(5) at every placement for `k ≤ 2` and 20 000 seeded draws for
>   `k = 3, 4`; over GF(2⁸) at 20 000 seeded draws. With the hand lower bounds asserted these are
>   upper-bound certificates over `K̄`, so certificates in characteristics 2, 3 and 5.
> - **(c)** (MC-138)'s tangent bounds hold at every point of every stratum over GF(2), GF(3), GF(5).
> - **(d)** (MC-46)'s classification is checked at every GF(2)-rational `ρ` with `r ≤ 3` (63 / 651 /
>   1 395), every GF(3)-rational `ρ` with `r ≤ 2` (364 / 11 011), and 1 500 seeded GF(3)-rational `ρ`
>   with `r = 3`. The families are bad everywhere, and every other `ρ` is certified good.
> - **(e)** (MC-45)'s `(P₂) ⟹ (P₃)` at `r = 2` holds at every GF(2)-rational `ρ`, in all four orbits.
> - **(f)** `earbad.m2`'s (B0)–(B4) pass over `ZZ/2`, `ZZ/3` and `ZZ/5`, trusting M2's `radical` over
>   finite fields.
>
> `PYTHONHASHSEED=0 python3 notes/scripts/w4/charcheck.py` (~35 s; 123 OK, 0 FAIL);
> `M2 --script notes/scripts/m2/earbad_p{2,3,5}.m2` (~1.3 s each).

**What remains.** The second readings of (MC-80), (MC-87)–(MC-89), (MC-68), (MC-69)(a) and (MC-71)
have landed (`b0bc1341`), and Step MC20's own on 2026-09-25. Swapping the certificate citations in (MC-19), (MC-21)(b), (MC-25),
(MC-45) and (MC-46) for (MC-134)–(MC-139) is done here by a pointer at each claim, not by a rewrite.
Guarding `earstep.py --lamcap`, adding a `q ∈ U` check to `--thetas`, and flagging `--orbits`'
characteristic-2 blind spot are harness debt: those drivers' figures must not move, so the fixes
belong in a deliberate driver-edit commit. The debt is recorded in `notes/scripts/README.md`
*Harness debt* (the 2026-09-25 item).

**Drivers** (all at `PYTHONHASHSEED=0` from the repository root; exact, deterministic):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/certhand.py` | (MC-134)–(MC-138) asserted: 16 configurations with rank and a `±1` minor; the transversal orthogonalities; one collision point per orbit; (MC-46)'s strata by `±1` monomial minors; ALL OK | < 1 s |
| `python3 notes/scripts/w4/certguard.py --lamcap` / `--replay` / `--thetas 5` | guarded `⋂Λ_k` equal to the hand value in all 16 cells; `--lamcap`'s own stream and its deficient draws; 30/30 θ-graphs attain at a `q` certified in `U` | < 5 s / < 2 s / ~2 s |
| `python3 notes/scripts/w4/orbitaudit.py` | `--orbits`' certifying coefficients: `−2` at orbit (i)'s generic stratum | < 5 s |
| `python3 notes/scripts/w4/certsearch.py` | the search over 0/1 points that found (MC-134)'s configurations (re-asserted by `certhand.py`) | ~10 s |


