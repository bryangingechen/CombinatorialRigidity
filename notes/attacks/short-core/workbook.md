# SHORT-CORE workbook

Proved results of the SHORT-CORE attack, numbered S1, S2, … and cited by number (`HARNESS.md`
*Attack track*). Appending is right here; a result found wrong is struck through with a pointer to
the result that corrects it. The notation is the brief's (`brief.md` §2–§3).

**Standing notation.** `d = 4`, `V = K⁵`, `D = dim Λ²V = 10`. The wedge pairs `Λ²V × Λ³V → Λ⁵V ≅ K`
perfectly. For a subspace `U ⊆ Λ²V`, `U° ⊆ Λ³V` is its annihilator, and `dim U° = 10 − dim U`.
`R := ρ°`. For an ear datum `y`, `J(y)` is the span of `G''`'s ear joins
`p_a∧y₁, y₁∧y₃, y₃∧y₄, …, y_k∧p_b`, so `W(y) = ρ + J(y)` and `W(y)° = R ∩ J(y)°`. Further notation:
`S(y) = star(y₁) + star(y₃)`, `T(y) = y₁∧y₃∧V`, `κ = dim(Π_a ∩ Π_b) ∈ {1, 2, 3}`, and
`f = def[10](G[V₁])`.

---

## S1 — the annihilator form of SHORT-CORE (session 1, 2026-10-29)

**Statement.** For independent `y₁, y₃`: (i) `S(y)° = T(y)`, of dimension 3. (ii) `W ⊇ S(y)` iff
`W° ⊆ T(y)`, and `W = Λ²V` iff `W° = 0`. So SHORT-CORE fails at `y` iff
`0 ≠ R ∩ J(y)° ⊆ T(y)`. (iii) `dim(R ∩ T(y)) = 3 − dim π_y(ρ)`, where
`π_y : Λ²V → Λ²(V/⟨y₁,y₃⟩)` is the brief's quotient.

**Proof.** (i) `y₁∧y₃∧z ∧ y₁∧v = 0` and `y₁∧y₃∧z ∧ y₃∧v = 0`, so `T ⊆ S°`. `dim S = 4 + 4 − 1 = 7`
(the stars meet in `K·y₁∧y₃`), so `dim S° = 3`. And `z ↦ y₁∧y₃∧z` is injective on
`V/⟨y₁,y₃⟩`, so `dim T = 3`. (ii) Annihilators reverse inclusion, and `(ρ + J)° = ρ° ∩ J°`.
(iii) `R ∩ T = (ρ + S)°`, and `dim(ρ + S) = 7 + dim π_y(ρ)` because `ker π_y = S`. ∎

**Remark (where `R` comes from).** `ω ∈ R` iff the row vector that is `−ω` at `a`, `ω` at `b` and 0
elsewhere annihilates every motion of `G[V₁]`, that is, iff it lies in the row space of `G[V₁]`.
This is the only handle on the actual `ρ` the route has so far.

## S2 — the every-`ρ` insertion hypothesis is false at `d = 4` (session 1)

**Statement.** Let `k = 3`, `Π_a = Π_b = Π` (that is, `la = lb`), and `ρ = Π∧V := span{u∧v : u ∈ Π}`.
Then `dim ρ = 9`, and at every ear datum (`y₁, y₃ ∈ Π`) `W = ρ` contains both stars. For every
placement `x₂`, every join of `G`'s ear lies in `ρ`, so `dim(ρ + Λ_G) = 9 < min(dim W + 1, 10)`.
So the `P⁴` transcription of `of_openEar_splitOff`'s `hins` (every base datum `(q, z, la, lb)`, every
subspace `ρ`) is false, and in the cell `κ = 3, k = 3` a proof must use that `ρ` is the actual
relative-screw space.

**Proof.** `Π∧V` is the kernel of `Λ²V → Λ²(V/Π) ≅ K`, so it has dimension 9. `p_a, p_b, y₁, y₃ ∈ Π`,
so `p_a∧y₁, y₁∧y₃, y₃∧p_b ∈ ρ`, and `star(y₁), star(y₃) ⊆ Π∧V`. `G`'s joins `p_a∧y₁, y₁∧x₂, x₂∧y₃,
y₃∧p_b` each have an end in `Π`. In `P³` the same `ρ` is `Λ²K⁴`, because `K⁴/Π` is a line, so `P³`
has no such obstruction. ∎

## S3 — a danger cell has `a` and `b` far apart in `G[V₁]` (session 1)

**Statement.** At a danger cell, every a–b path in `G[V₁]` has length at least `7 − k`, and `a` and
`b` lie in one component of `G[V₁]`. In particular `a ≁ b`, and for `k ≤ 4`, `a` and `b` have no
common neighbour in `V₁`.

**Proof.** A motion `S` of `G[V₁]` has `S(u) − S(v) ∈ span C(e)` at each link `e = uv`
(`infinitesimalMotions`, `RigidityMatrix/Basic.lean`). Telescoping along a path
`a = v₀ − ⋯ − v_ℓ = b` puts `S(b) − S(a)` in the span of its `ℓ` hinges, so `dim ρ ≤ ℓ`. `W` is `ρ`
plus `k` joins, so `7 ≤ dim W ≤ dim ρ + k ≤ ℓ + k`. If `a` and `b` lie in different components,
then `ρ = Λ²V` (a motion may be anything on one component and 0 on the other), so `dim W = 10` and
the cell is not a danger cell. ∎

So brief §5 O2's axis "`a` and `b` adjacent or not" collapses: adjacency is never a danger cell
(`dim W ≤ k + 1 ≤ 6`, where the insertion applies).

## S4 — the cell `κ = 2`, `k = 3`: SHORT-CORE holds for every `ρ` (session 1)

**Statement.** Let `k = 3` and `dim(Π_a ∩ Π_b) = 2`, and let `ρ ⊆ Λ²V` be any subspace. At general
`y₁ ∈ Π_a`, `y₃ ∈ Π_b`, SHORT-CORE holds: `W(y) ⊇ S(y)` implies `W(y) = Λ²V`.

**Proof.** Suppose not. By S1, for `y` in a dense set:
(F1) `R ∩ T(y) ≠ 0`, and (F2) `R ∩ J(y)° ⊆ T(y)`.
Let `H = Π_a + Π_b`, of dimension 4, and fix `e ∉ H`, so `Λ³V = Λ³H ⊕ (Λ²H)∧e`. Write
`p : Λ³V → Λ²H` for the second coordinate.

1. *`R ∩ Λ³H = 0`.* `p_a, p_b, y₁, y₃ ∈ H`, so `J(y) ⊆ Λ²H`, and `Λ³H ∧ Λ²H ⊆ Λ⁵H = 0`. So
   `Λ³H ⊆ J(y)°`, and by (F2) `R ∩ Λ³H ⊆ T(y)` for a dense set of `y`. Two general data `y, y'` have
   `y₁, y₃, y₁', y₃'` independent in `H`, and a nonzero 3-vector divisible by both `y₁∧y₃` and
   `y₁'∧y₃'` would be a plane through four independent points. So `T(y) ∩ T(y') = 0`.
2. *`p(R) = Λ²H`, so `R` is a graph.* By (F1) pick `0 ≠ y₁∧y₃∧z ∈ R`. By step 1, `z ∉ H + ⟨y₁,y₃⟩`,
   so `p(y₁∧y₃∧z)` is a nonzero multiple of `y₁∧y₃`. So `p(R)` contains `y₁∧y₃` for a dense set of
   `(y₁,y₃) ∈ Π_a × Π_b`. Their span is `Π_a∧Π_b`: with `L = Π_a ∩ Π_b`, `H = L ⊕ Kα ⊕ Kβ`,
   `Π_a = L ⊕ Kα` and `Π_b = L ⊕ Kβ`, it contains `Λ²L, L∧α, L∧β, α∧β`, which is all of `Λ²H` (6
   dimensions). So `p(R) = Λ²H`, and with step 1, `p|_R` is an isomorphism:
   `R = {η∧e + φ(η) : η ∈ Λ²H}` for a linear `φ : Λ²H → Λ³H`.
3. *`φ(η) = η∧h₀`.* For `y₁∧y₃∧z ∈ R` as in step 2, normalize `z = e + h`. Then
   `φ(y₁∧y₃) = y₁∧y₃∧h ∈ (y₁∧y₃)∧H`. Every line of `PH ≅ P³` meets the planes `PΠ_a` and `PΠ_b`, so
   every decomposable `c ∈ Λ²H` is some `y₁∧y₃`. The condition `φ(c)∧u = φ(c)∧v = 0` for `c = u∧v`
   is closed, so it holds at every decomposable `c`. Put `ψ(u,v,x) := φ(u∧v)∧x ∈ Λ⁴H ≅ K`. It is
   trilinear and alternating in `(u,v)`, and `ψ(u,v,u) = ψ(u,v,v) = 0`, so it is alternating. An
   alternating 3-form on the 4-space `H` is `x∧y∧z ↦ x∧y∧z∧h₁` for a unique `h₁` (the pairing
   `Λ³H × H → Λ⁴H` is perfect), so `φ(η) = η∧h₀` for some `h₀ ∈ H`. Hence `R = (Λ²H)∧e'` with
   `e' = e + h₀ ∉ H`.
4. *(F2) fails.* `η∧e' ∧ j = (η∧j)∧e'` vanishes iff `η∧j = 0` in `Λ⁴H`. So
   `R ∩ J(y)° ≅ {η ∈ Λ²H : η∧j = 0 ∀ j ∈ J(y)}`, of dimension `≥ 6 − 3 = 3`. But
   `R ∩ T(y) = K·y₁∧y₃∧e'`, because `η∧e' = y₁∧y₃∧z` forces `η ∈ K·y₁∧y₃` (apply `p`). So
   `R ∩ J(y)° ⊄ T(y)`, against (F2). ∎

(Here `ρ = R° = star(e')`: the obstruction candidate in this cell is the star of a point off `H`,
and its `W` has dimension 7 without being `S(y)`.)

## S5 — the cell `κ = 3`, `k = 3`: failure is exactly `ρ + Λ²Π = Π∧V` (session 1)

**Statement.** Let `k = 3` and `Π_a = Π_b = Π`, with `p_a ≠ p_b` projectively. At general
`y₁, y₃ ∈ Π`, `J(y) = Λ²Π`, so `W = ρ + Λ²Π` does not depend on `y`. SHORT-CORE fails iff
`ρ ⊆ Π∧V` and `ρ + Λ²Π = Π∧V`, which forces `dim ρ ≥ 6`; it then fails at every ear datum.

**Proof.** In the plane `PΠ`, the lines `p_a y₁`, `y₁ y₃` and `y₃ p_b` are dependent in `Λ²Π ≅ K³` iff
they are concurrent, which for general `y₁, y₃` they are not. So `J(y) = Λ²Π` and `W = ρ + Λ²Π =: W₀`.
If `W₀ ⊇ S(y)` on a dense set, then by closure `W₀ ⊇ star(y)` for every `y ∈ Π`, so
`W₀ ⊇ Π∧V`, which has codimension 1. So failure means `W₀ = Π∧V`. Conversely `W₀ = Π∧V` contains
every `S(y)`. `dim ρ ≥ 9 − 3`. ∎

S2's `ρ` is the largest case. Excluding S5 needs the actual `ρ`. If `G[V₁]` has an a–b path with every
point in `Π`, then `ρ ⊆ Λ²Π`, `dim ρ ≤ 3`, and S5 cannot hold.

## S6 — the tangent lemma, and the cells `k = 3`, `κ ≤ 2` for every `ρ` (session 1)

**Lemma (tangent).** Let `R ⊆ Λ³V` be a subspace, `n ≥ 1`, and let `y ↦ M(y)`, `Ω(y)` be
polynomial families of linear maps `Kⁿ → Λ³V/R` and `Kⁿ → Λ³V`, with `M(y) = Ω(y) mod R`. Let `m` be
the least value of `dim ker M(y)`, and let `U₁ = {y : dim ker M(y) = m}`, the non-vanishing set of a
nonzero minor. Let `γ` be a polynomial curve with `γ(0) = y₀ ∈ U₁`, and let `ξ₀ ∈ ker M(y₀)`. Then
some `ξ(t) ∈ K[[t]]ⁿ` with `ξ(0) = ξ₀` has `M(γ(t))ξ(t) = 0`, and the `t`-coefficient of
`Ω(γ(t))ξ(t)` lies in `R`.
*Proof.* Over `K((t))`, `M(γ(t))` has rank at most `n − m`, because `K` is infinite and every
specialization has rank at most `n − m`; it has rank exactly `n − m` at `t = 0`. In Smith form over
the DVR `K[[t]]`, every nonzero invariant factor is then a unit, so the kernel is a free direct
summand of rank `m` reducing onto `ker M(y₀)`. `Ω(γ(t))ξ(t) ∈ R ⊗ K[[t]]`, so each coefficient lies
in `R`. ∎

**Statement (`k = 3`).** Let `k = 3`, let `ρ` be any subspace, and let `p_a ∈ Π_a`, `p_b ∈ Π_b` be
independent. Take `M(y)z = y₁∧y₃∧z mod R` (`n = 5`). At every ear datum `y ∈ U₁` with
`p_a, y₁, y₃, p_b` independent, `W(y) ⊇ S(y)` implies `W(y) = Λ²V`. Such `y` exist, so the
implication holds off a nonzero polynomial, iff `κ ≤ 2`.

**Proof.** Suppose `W ⊇ S` and `W ≠ Λ²V`. Then `0 ≠ R ∩ J° ⊆ T` (S1). At `k = 3`, `J ⊆ S`, so
`T ⊆ J°`, and `R ∩ T = R ∩ J° ≠ 0`. So some `z₀ ∉ ⟨y₁,y₃⟩` has `y₁∧y₃∧z₀ ∈ R`, that is, `z₀ ∈ ker M(y₀)`.
- *Curve A*, `(y₁ + t p_a, y₃)`, which stays in `Π_a × Π_b`. The lemma gives
  `δ_A = p_a∧y₃∧z₀ + y₁∧y₃∧z' ∈ R`. Each of `p_a∧y₁`, `y₁∧y₃`, `y₃∧p_b` shares a vector with
  `p_a∧y₃∧z₀` (`p_a`, `y₃`, `y₃`), and `y₁∧y₃∧z' ∈ T ⊆ J°`. So `δ_A ∈ R ∩ J° ⊆ T`, hence
  `p_a∧y₃∧z₀ ∈ T`. Wedging with `y₁` gives `p_a∧y₃∧z₀∧y₁ = 0`, so `z₀ ∈ ⟨p_a, y₁, y₃⟩`.
- *Curve B*, `(y₁, y₃ + t p_b)`. Likewise `δ_B = y₁∧p_b∧z₀ + y₁∧y₃∧z''` is in `R ∩ J°`, because
  `y₁∧p_b∧z₀` shares `y₁, y₁, p_b` with the three joins. Wedging with `y₃` gives
  `z₀ ∈ ⟨y₁, y₃, p_b⟩`.
With the four independent, `⟨p_a,y₁,y₃⟩ ∩ ⟨y₁,y₃,p_b⟩ = ⟨y₁,y₃⟩`, a contradiction.

*Existence.* If `κ = 3`, all four lie in `Π`. If `κ ≤ 2`: `⟨p_a, y₁⟩ ∩ Π_b ⊆ L := Π_a ∩ Π_b`.
- ~~When `κ = 2`, a plane `⟨p_a, y₁⟩` of `Π_a` meets `L` in a line `⟨v⟩`, with `v = p_a` if `p_a ∈ L`.~~
  Gap found by the session-1 review: this choice allows `⟨p_a, y₁⟩ = L` and `v ∥ p_b`.
  Corrected in S12.
- When `κ = 1`, pick `y₁ ∉ ⟨p_a⟩ + Π_b`. This is possible because `Π_a + Π_b = V`. Then
  `⟨p_a, y₁⟩ ∩ Π_b ⊆ ⟨p_a⟩`.

Either way `⟨p_a, y₁⟩ ∩ Π_b ⊆ ⟨v⟩` for one vector `v`. Take `y₃ ∈ Π_b ∖ ⟨v, p_b⟩`, possible since
`dim Π_b = 3`. Then `⟨y₃, p_b⟩ ∩ ⟨p_a, y₁⟩ ⊆ ⟨y₃, p_b⟩ ∩ ⟨v⟩ = 0`. ∎

So S4 is a second proof of the cell `κ = 2`. At `κ = 3` the same two curves give only
`z₀ ∈ Π + ⟨y₁,y₃⟩ = Π`, that is, `R ∩ T(y) ⊆ K·Λ³Π`, which is S2's and S5's obstruction.

## S7 — the cell `k = 4`, every `κ`, every `ρ` (session 1)

**Statement.** Let `k = 4`, with ear data `y₁ ∈ Π_a`, `y₃` free and `y₄ ∈ Π_b`, and let `ρ` be any
subspace. Take `M(y)(s,t) = y₁∧y₃∧(s y₄ + t p_b) mod R`. At every `y ∈ U₁` with `p_a, y₁, y₃, y₄`
independent and `y₁, y₃, y₄, p_b` independent, `W ⊇ S` implies `W = Λ²V`. Such `y` exist for every
`κ` (given `p_a, p_b ≠ 0`).

**Proof.** The joins are `p_a∧y₁, y₁∧y₃, y₃∧y₄, y₄∧p_b`, and only the last shares no vector with
`y₁∧y₃`. So `T ∩ J° = y₁∧y₃∧⟨y₄, p_b⟩`, using the independence of `y₁, y₃, y₄, p_b`. Suppose
`0 ≠ R ∩ J° ⊆ T`. Then some `0 ≠ z₀ ∈ ⟨y₄, p_b⟩` has `y₁∧y₃∧z₀ ∈ R`, so `z₀ ∈ ker M(y₀)`. The lifts
`z(t)` stay in `⟨y₄, p_b⟩`, since neither curve moves `y₄`.
- *Curve A*, `(y₁ + t p_a, y₃, y₄)`. `δ_A = p_a∧y₃∧z₀ + y₁∧y₃∧z'`. The first term shares `p_a`,
  `y₃`, `y₃` with the first three joins and dies on `y₄∧p_b`, since `z₀ ∈ ⟨y₄, p_b⟩`. The second term
  lies in `T ∩ J°`, since `z' ∈ ⟨y₄, p_b⟩`. So `δ_A ∈ R ∩ J° ⊆ T`, and wedging with `y₁` gives
  `z₀ ∈ ⟨p_a, y₁, y₃⟩`.
- *Curve B*, `(y₁, y₃ + t y₄, y₄)`, which keeps `y₃ ∧ y₄` fixed.
  `δ_B = y₁∧y₄∧z₀ + y₁∧y₃∧z''`. The first term shares `y₁, y₁, y₄, y₄` with the four joins. So
  `δ_B ∈ T`, and wedging with `y₃` gives `z₀ ∈ ⟨y₁, y₃, y₄⟩`.
Then `z₀ ∈ ⟨y₄, p_b⟩ ∩ ⟨y₁, y₃, y₄⟩ = ⟨y₄⟩`, so `y₄ ∈ ⟨p_a, y₁, y₃⟩`, against the first
independence.

*Existence.* Take `y₁ ∈ Π_a ∖ (⟨p_a⟩ ∪ ⟨p_b⟩)` and `y₄ ∈ Π_b ∖ (⟨p_a, y₁⟩ ∪ ⟨y₁, p_b⟩)`, possible
since `Π_b` is not a union of two planes. Then take `y₃` off the two 3-spaces `⟨p_a, y₁, y₄⟩` and
`⟨y₁, y₄, p_b⟩`. ∎

## S8 — the cell `k = 5`, every `κ`, every `ρ` (session 1)

**Statement.** Let `k = 5`, with ear data `y₁ ∈ Π_a`, `y₃, y₄` free and `y₅ ∈ Π_b`, and let `ρ` be
any subspace. At every `y` with `y₁, y₃, y₄, y₅, p_b` a basis and with `y₁∧y₃∧y₅ ∉ R` unless
`y₁∧y₃∧y₅ ∈ R` identically, `W ⊇ S` implies `W = Λ²V`. Such `y` exist for every `κ`.

**Proof.** Only `y₄∧y₅` and `y₅∧p_b` share no vector with `y₁∧y₃`, so
`T ∩ J° = y₁∧y₃∧(⟨y₁,y₃,y₄,y₅⟩ ∩ ⟨y₁,y₃,y₅,p_b⟩) = K·y₁∧y₃∧y₅`. Suppose `0 ≠ R ∩ J° ⊆ T`. Then
`y₁∧y₃∧y₅ ∈ R` at this `y`, hence identically, by the choice of `y`. Put `y₃ + t y₄` in place of `y₃`
and subtract: `y₁∧y₄∧y₅ ∈ R`. It shares a vector with each of the five joins (`y₁, y₁, y₄, y₄, y₅`),
so it lies in `R ∩ J° ⊆ T`. Wedging with `y₃` gives `y₁∧y₄∧y₅∧y₃ = 0`, against the basis. For
existence, take `y₁ ∈ Π_a` and `y₅ ∈ Π_b` with `y₁, y₅, p_b` independent, then complete with `y₃, y₄`.
The second condition is a non-vanishing condition or empty. ∎

**Consequence.** With S1, SHORT-CORE holds off a nonzero polynomial in the ear data for every
subspace `ρ` and every base datum with `p_a ∦ p_b` in all cells except `k = 3`, `κ = 3` (S5). There,
failure is `ρ + Λ²Π = Π∧V`. At `k = 4, 5`, the `P³` factoring's every-`ρ` interface (`hins`) is
therefore sound at `d = 4`; only `k = 3` needs O1's amendment.

## S9 — `κ` is read off the `P²` point-join framework of `G[V₁]` (session 1)

**Setting.** This uses the `P⁴` configuration as the brief §1–§2 describes it:
`b_v = (q_v, z¹_v, z²_v, 1)`, with every closed neighbourhood's points spanning at most 3
dimensions. Write `E = ker(V → K³)` for the 2-dimensional span of the height directions, and
`q̂_v = (q_v, 1) ∈ K³`. The *`P²` framework* of `G[V₁]` has motions `λ : V₁ → (K³)^*` with
`λ_u − λ_v ∈ K·(q̂_u × q̂_v)` at each link. With `(K³)^* ≅ Λ²K³` this is the point-join framework of
the picture.

**Statement.** Suppose `a` and `b` each have at least two neighbours in `V₁`. At a general picture `q`:
(i) `L(q) = L₁(q) × L₁(q)`, where `L₁(q)` is the single-height space (the `P³` lifting space);
(ii) `λ ↦ (λ_v(q̂_v))_v` maps the `P²` motions onto `L₁(q)`, and the plane of `a` is `λ_a`;
(iii) at general `z ∈ L(q)`, `κ = 3 − min(2, dim ρ⁽²⁾)`, where `ρ⁽²⁾ = {λ_a − λ_b}` is the `P²`
relative motion space of `a, b`. In particular `κ = 3` iff `a` and `b` are relatively rigid in the `P²`
framework.

**Proof.** (i) A closed neighbourhood with non-collinear pictures (true at general `q` when it has 3
or more members) spans at most 3 dimensions iff its span is a graph over `K³`, that is, iff each height
is a linear function of `q̂` on it. The two heights are independent conditions. (ii) For `z ∈ L₁(q)`
and a body `u` of degree at least 2, let `λ_u` be the functional with `z_v = λ_u(q̂_v)` on `N[u]`.
For `u ~ v`, `λ_u − λ_v` vanishes at `q̂_u` and `q̂_v`, so it is a multiple of `q̂_u × q̂_v`. At a
degree-1 body `u` with neighbour `w`, any `λ_w + s·(q̂_u × q̂_w)` works, because `z_u = λ_w(q̂_u)`.
Conversely, `z_v := λ_v(q̂_v)` satisfies `z_v = λ_u(q̂_v)` for `u ~ v`. (iii)
`Π_a ∩ Π_b ≅ ker(la − lb : K³ → E)`, and `la − lb = (λ¹_a − λ¹_b, λ²_a − λ²_b)` for the two `P²`
motions `λ¹, λ²` of the two heights, which are general. ∎

*Where `a` has a single neighbour in `V₁`,* `Π_a` is chosen by the base data, in the Lean from the
ear datum `s₁` of `exists_earBase_splitOff`, and can be chosen with `κ ≤ 2` (an O1/O4 matter).

## S10 — at `κ = 3`, every relative screw is vertical: `ρ ⊆ E∧V` (session 1)

**Statement.** If `a` and `b` are relatively rigid in the `P²` framework (S9: `κ = 3`), then
`ρ ⊆ E∧V = ker(Λ²V → Λ²(V/E))`, a 7-dimensional subspace. Dually, `R ⊇ Λ²E ∧ V`.

**Proof.** `P : V → V/E ≅ K³` sends `b_v ↦ q̂_v`, so `Λ²P` sends hinges to `P²` hinges. So `Λ²P ∘ S`
is a `P²` motion for every motion `S` of `G[V₁]`. Then `Λ²P(S(b) − S(a)) = 0` by relative rigidity. ∎

## S11 — the cell `κ = 3`, `k = 3`: failure is exactly `ρ = Π∧E` (session 1)

**Statement.** In the cell `κ = 3, k = 3`, with `a, b` as in S9:
(i) `V = Π ⊕ E`, and SHORT-CORE fails iff `ρ = Π∧E`, which has dimension 6. Then
`R = Λ³Π ⊕ (Π∧Λ²E)`.
(ii) `dim W = dim ρ + 3`, so a danger cell has `dim ρ ∈ {4, 5, 6}`, and failure is the case
`dim ρ = 6`.
(iii) Let `H = {v ∈ V₁ : λ_v = λ_a for every P² motion λ}`. Every point of `H` lies in `Π`. If `G[H]`
holds an a–b path, then `ρ = 0` and the cell is not a danger cell.

**Proof.** (i) `Π` is the graph of `la` over `K³`, so `Π ∩ E = 0`. Then
`Λ²V = Λ²Π ⊕ Π∧E ⊕ Λ²E`, with `Π∧V = Λ²Π ⊕ Π∧E` and `E∧V = Π∧E ⊕ Λ²E`. By S5, failure is
`ρ ⊆ Π∧V` and `ρ + Λ²Π = Π∧V`. By S10, `ρ ⊆ Π∧E`, so failure is `ρ = Π∧E`. The annihilator is
read off the matching decomposition of `Λ³V`. (ii) `ρ ∩ Λ²Π ⊆ E∧V ∩ Λ²Π = 0`, and `J = Λ²Π` (S5).
(iii) For `v ∈ H`, `z_v = λ_v(q̂_v) = la(q̂_v)`, so `b_v ∈ Π`. An a–b path in `G[H]` has every hinge in
`Λ²Π`, so `ρ ⊆ Λ²Π ∩ E∧V = 0` (S3's telescoping). ∎

**What is left in this cell.** Rule out `ρ = Π∧E` when `a` and `b` are `P²`-relatively rigid but
not joined inside `G[H]`. If `P²` rigid classes are connected (true for the generic body-hinge count
matroid with `D = 3`, whose rigid components are rigid induced subgraphs), (iii) closes the cell.
The `P²` framework here is a pin-collinear body-and-pin framework: the pin of `uv` is where the polars
of `q_u` and `q_v` meet. Whether that genericity transfer is available, and with which citation, is
open; the candidate, to be verified before it is used, is B. Jackson and T. Jordán, pin-collinear
body-and-pin frameworks, Discrete Comput. Geom. (2008).

## S12 — the independent reading of S6–S8, and S6's corrected existence step (session 1)

**Review.** A fresh `general-purpose` reader checked S1, the tangent lemma, every `J°` membership and
`T ∩ J°` computation, the logic and the existence claims of S6–S8, and listed the joins itself. It
found no break in any implication. The `d = 3` control reproduces the `P³` every-`ρ` statement. At
`d = 4`, `κ = 3`, `k = 3`, the argument correctly leaves `ρ = Π∧V` unexcluded. It also found:
(a) a gap in S6's existence step at `κ = 2`, corrected below;
(b) a nit: `U₁` is the union of the non-vanishing sets of the `(n − m)`-minors, so it contains the
non-vanishing set of one nonzero minor, which is all the argument uses;
(c) the quantifiers are "for each `ρ` and base datum, a nonzero polynomial in the ear data". A
consumer that needs genericity jointly over base and ear data assembles it (O4).

Its adversarial search builds `ρ` from structured blocks (stars, `Λ²` of the planes and of
`L = Π_a ∩ Π_b`, `Π_a∧Π_b`, `Π∧V`, `L∧V`, `L∧E` and random subspaces of these). The command is
`python3 notes/attacks/short-core/drivers/adversarial_rho.py 1 15`, committed. Out of 90 draws per
`(κ, k)` cell, it found failures only at `κ = 3, k = 3` (26 of 90, as S2 and S5 predict) and none in the
other eight cells. That is one draw per `ρ`, so it is evidence about the sampler's support.

**S6, existence at `κ = 2`, corrected.** Let `L = Π_a ∩ Π_b`, of dimension 2, and take
`y₁ ∈ Π_a ∖ (L ∪ ⟨p_a, p_b⟩)`, which exists because a 3-space is not a union of two proper subspaces.
Then `⟨p_a, y₁⟩ ≠ L` meets `L` in a line `⟨v⟩`. And `v ∦ p_b`: otherwise `p_b ∈ ⟨p_a, y₁⟩`, so
`y₁ ∈ ⟨p_a, p_b⟩`. Take `y₃ ∈ Π_b ∖ ⟨v, p_b⟩`. Then
`⟨y₃, p_b⟩ ∩ ⟨p_a, y₁⟩ ⊆ Π_b ∩ ⟨p_a, y₁⟩ ⊆ L ∩ ⟨p_a, y₁⟩ = ⟨v⟩`, and `v ∉ ⟨y₃, p_b⟩`: otherwise
`v = αy₃ + βp_b` with `α ≠ 0`, so `y₃ ∈ ⟨v, p_b⟩`. So `p_a, y₁, y₃, p_b` are independent. The `κ = 1`
step stands, as the review confirmed. ∎
