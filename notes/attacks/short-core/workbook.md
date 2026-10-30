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

## S13 — session 2's consumer diff: no mismatch (session 2, 2026-10-30)

Read against the tree at `3b6dd7e9`, from the declaration bodies in
`Molecular/Molecule/Pencil/MainComponent/Short.lean` (the brief's path omits `Molecular/`). The
hypotheses of `Graph.X0Attains.of_openEar_three` (line 929) are, one for one, brief §1's list:
`[Infinite K] [Finite α] [Finite β]`, `hG`, `hcover`, `hinj`, `hxV₁`, `ha`, `hb`, `hab`,
`hpath : ∀ i : Fin 4`, `hsep`, `h₁`, `h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K`, with
conclusion `G.X0Attains K`; `of_openEar_four` (line 782) is the same at `Fin 5`. `Graph.IsX0Graph`
(`Cut.lean:118`) is simple, connected and degree at least 2; `Graph.X0Attains` (`Carrier.lean:342`)
is brief §1's reading. `of_openEar_splitOff` (line 588) still takes `hins` at every base datum and
every `ρ`, as the brief's O1 says. The base data (`exists_earBase_splitOff`, line 382) take `la`, `lb`
from a height `zs ∈ L_{G''}(q')` on the closed neighbourhoods `N_{G''}[a] ∋ x 0`, `N_{G''}[b]`, chosen off
`R₁ ∘ restrict` and `R₂` only. The `Pᵈ` consumer does not exist yet, so the diff is of the model.

## S14 — in the `P²` framework, relative rigidity puts `a` and `b` in one connected rigid set (session 2)

**Setting.** `F` is a finite simple graph on `V₁`, with `a ≠ b` in `V₁` not adjacent, and `F' = F + ab`.
A *`P²` framework* of `F` gives each edge `uv` a hinge `h_uv ∈ Λ²K³`, and its motions are the maps
`S : V₁ → Λ²K³` with `S(u) − S(v) ∈ K·h_uv` on each edge. `Z(·)` is the motion space. `def` is the
deficiency at `D = 3`: `def(F) = max_P [3(|P| − 1) − 2·d_F(P)]` over the partitions `P` of `V₁`, where
`d_F(P)` counts the edges crossing `P`. This is Lean's `F.deficiency 2`, by the body of
`Graph.partitionDef` (`Deficiency.lean:206`, `bodyBarDim 2 = 3`). Write `val_F(P)` for the bracket.

**Statement.** Suppose every hinge of `F'` is nonzero, `dim Z(F') = 3 + def(F')`, and `S(a) = S(b)` for
every `S ∈ Z(F)`. Then there is an `X ⊆ V₁` with `a, b ∈ X` such that `F[X]` is connected and every
motion of `F` is constant on `X`.

**Proof.**
0. *Constant-on-parts motions.* For a partition `P` of `V₁` and a graph `F₀ ∈ {F, F'}` with nonzero
   hinges, the motions of `F₀` constant on each part form a space of dimension at least
   `3|P| − 2·d_{F₀}(P) = 3 + val_{F₀}(P)`. There are three unknowns per part, an edge inside a part
   imposes nothing, and a crossing edge imposes the two conditions `S_X − S_Y ∈ K·h`. So
   `dim Z(F₀) ≥ 3 + def(F₀)`, by an optimal `P`.
1. `Z(F') = Z(F)`. `Z(F') = {S ∈ Z(F) : S(a) − S(b) ∈ K·h_ab}`, and `S(a) − S(b) = 0` on `Z(F)`.
2. `def(F') ≥ def(F)`. By 0 and 1, `3 + def(F) ≤ dim Z(F) = dim Z(F') = 3 + def(F')`.
3. *Every `F'`-optimal partition has `a` and `b` in one part.* `val_{F'}(P) = val_F(P) − 2·[P
   separates a, b]`. A separating `P` has `val_{F'}(P) ≤ def(F) − 2 < def(F')`.
4. *Motions are constant on the parts.* Fix an `F'`-optimal `P`, and let `X` be its part holding `a`
   and `b`. By 0, the motions of `F'` constant on the parts of `P` have dimension at least
   `3 + def(F') = dim Z(F')`, so they are all of `Z(F')`, which is `Z(F)` by 1.
5. *`F[X]` is connected.* Let `F[X]` have components `C₁, …, C_m` with `m ≥ 2`. Splitting `X` into them
   gives a partition `P*`. The only edge of `F'` that newly crosses is `ab`, if `a` and `b` fall in
   different components. So `val_{F'}(P*) ≥ val_{F'}(P) + 3(m − 1) − 2 > def(F')`, a contradiction. ∎

`a ≁ b` is used only to make `F'` simple, which the rank input below asks. Step 3 is
`Graph.deficiencyMerged` (`Deficiency.lean:3576`) in words. The hypothesis `dim Z(F') = 3 + def(F')` is
the generic `P²` rank. In the project it is `PanelHingeFramework.finrank_span_rigidityRows_of_isGenericNormals`
(`GenericLift/PanelGeneric.lean`) at `n = 2`, with rank and nullity. That theorem is Katoh and Tanigawa's
Theorem 5.6 at `d = 2` (`rankHypothesis_of_theorem_55_gen`), made generic. At grade 1 the panel hinge
`panelSupportExtensor n_u n_v = complementIso (n_u ∧ n_v)` (`PanelLayer.lean:202`) is the image of
`n_u ∧ n_v` under a fixed isomorphism `Λ²K³ ≅ Λ¹K³`. So `ofNormals (k := 1)` at normals `q̂` has the
motions of the `P²` point-join framework `h_uv = q̂_u ∧ q̂_v`, carried by that isomorphism.

## S15 — a general picture is generic for the `P²` rank (session 2)

**Statement.** Let `F'` be a finite simple graph with at least one body. Some nonzero polynomial `P` in
the picture `q : V(F') × Fin 2 → K` has the following property. At every `q` off its zero set, the `P²`
point-join framework with hinges `q̂_u ∧ q̂_v`, `q̂_v = (q_v, 1)`, has nonzero hinges and
`dim Z(F') = 3 + def(F')`.

**Proof.** `PanelHingeFramework.exists_isGenericNormals_abundance` (`PanelGeneric.lean:171`) gives a
nonzero abundance polynomial `A` in the normals `n : V × Fin 3 → K`, whose non-roots are generic. The
citation was corrected by S24; it first read `exists_isGenericNormals`, which gives no polynomial. Pick `n` off `A · ∏_v n_{v,2}`, possible since
`K` is infinite. At `n`, `finrank_span_rigidityRows_of_isGenericNormals` (`n = 2`) gives rank
`3(|V| − 1) − def(F')`. Put `q̂_v = n_v / n_{v,2}`. Each panel hinge is multiplied by the unit
`(n_{u,2} n_{v,2})⁻¹` (`normalsJoin_smul_left` and its right form), so the spans of the hinges are
unchanged, and so is the motion space. So the picture `q⁰_v = (n_{v,0}, n_{v,1})/n_{v,2}` attains the
rank. The rank is at least `r` exactly where some `r`-minor of rows polynomial in `q` does not vanish.
That minor is nonzero at `q⁰`, so it is a nonzero polynomial. Multiply it by `∏_{uv ∈ E}(q_{u,0} − q_{v,0})`
for nonzero hinges. Off the product, the rank is at least the target, and it is at most the target by
the bound with nonzero hinges (S14 step 0, which is `screwDim_add_deficiency_le_finrank_infinitesimalMotions`). ∎

This is the step `exists_mvPolynomial_le_finrank_ofNormals_bind` performs at grade 2 for the ear data.
The scaling is what moves the generic normals into the affine chart `n_{v,2} = 1`, where pictures live.

## S16 — the cell `κ = 3`, `k = 3` is not a danger cell at general base data (session 2)

**Statement.** Let `a` and `b` each have at least two neighbours in `V₁`. Let the picture `q` be general:
closed neighbourhoods in `V₁` with three or more members have non-collinear pictures, distinct points
on edges, and `q` off S15's polynomial for `F' = G[V₁] + ab` when `a ≁ b`. Let the base heights
`z = (z¹, z²) ∈ L(q) = L₁(q)²` (S9 (i)) have `z¹` off the kernel of the linear map
`L₁(q) → (K³)*`, `z¹ ↦ λ_a − λ_b`, whenever that map is nonzero. If `κ = 3`, then `ρ ⊆ Λ²Π`, so
`dim W ≤ 3` at `k = 3`, and the cell is not a danger cell.

**Proof.**
1. *`κ = 3` forces `P²` relative rigidity.* Write `z ↦ λ` for S9 (ii)'s correspondence. With at least
   two neighbours, `λ_a` is the plane through the lifted closed neighbourhood of `a`, because
   `λ_a − λ_v` vanishes at `q̂_v` for each neighbour `v`. So `λ_a` is determined by `z` and is linear in
   it. The image of `z¹ ↦ λ_a − λ_b` is `ρ⁽²⁾`, since every `P²` motion comes from some `z¹`. `κ = 3`
   means `la = lb`, so `λ¹_a = λ¹_b`, and by the choice of `z¹`, `ρ⁽²⁾ = 0`.
2. *`a ~ b`.* The edge gives `ρ ⊆ K·b_a∧b_b` (S3's telescoping), and `b_b ∈ Π` since `b ∈ N[a]`.
3. *`a ≁ b`.* S14 applies to the `P²` framework of `F = G[V₁]` at `q`, with S15 for `F'`. It gives an
   `X ∋ a, b` with `G[X]` connected and every `P²` motion constant on `X`. So `X ⊆ H`, the rigid class
   of S11 (iii), whose points lie in `Π` (`b_v = (q̂_v, Λ_a q̂_v)`). An a–b path in `G[X]` has every
   hinge in `Λ²Π`, so `ρ ⊆ Λ²Π`, by S3's telescoping.
4. At `k = 3` and `κ = 3`, `J(y) ⊆ Λ²Π` (S5), so `W = ρ + J ⊆ Λ²Π`, of dimension 3 < 7. ∎

**Consequence.** With S4, S6–S8 and S12, SHORT-CORE holds at every danger cell, at general ear data,
for base data general in S16's sense. This uses the actual `ρ` only at `κ = 3`, `k = 3`, and there only
through S16. S10 and S11 (i)–(ii) are no longer needed: S16 bounds `ρ` directly. What remains is to
fold S16's conditions on the base data into the `P⁴` interface (O1d, O4), and the single-neighbour case.
In that case `la` is chosen by the base data, and at a general choice `la ≠ lb` (session-1 S9, last
paragraph), so `κ ≤ 2`.

## S17 — exact control for S14, S16 and S9 (iii) (session 2)

`python3 notes/attacks/short-core/drivers/p2_path.py --seed N --trials 60`, `N = 1, 2, 3`, all
`OK` (exit 0). **Population.** The draws are connected simple graphs on 5–8 bodies: a random
spanning tree plus 1 to `n` or `n/2 + 1` extra edges, or a triangle strip with a flexible pendant
cycle. Pictures are integer, in `[−40, 40]²`, and the heights are random combinations of a basis of
`L₁(q)`, computed from its definition. There is one draw per graph, 179 graphs in all.
**Results.**
- Every graph met `dim Z(F) = 3 + def(F)` at its draw, which certifies its generic `P²` rank.
- **S14.** There were 932 non-adjacent `P²`-relatively-rigid pairs. At every one, `F + ab` met S14's
  hypothesis at the draw. Every one passed: `def(F') ≥ def(F)`; every `F'`-optimal partition has
  `a`, `b` in one part `X`, with `F[X]` connected and `X ⊆ H`; and `a`, `b` lie in one component of
  `F[H]`. In 237 of them, `H ≠ V`.
- **S9 (iii).** There were 2602 pairs, each end with two or more neighbours. At every one,
  `κ = 3 − min(2, dim ρ⁽²⁾)`.
- **S16.** There were 2189 pairs with `κ = 3`, every one guarded. At each, `ρ ⊆ Λ²Π_a`; in fact
  `ρ = 0`, as S10 with S16 forces. In 674 of them, `F` is not `P²`-rigid.
- **Control.** Of the 413 pairs with `κ ≤ 2`, 24 have `ρ ⊄ Λ²Π_a`, so the containment test can fail.
The deficiency is by enumerating set partitions, independent of `strata.py`'s DP. Each figure is one
draw per graph, so it is evidence about this sampler's support. S14 and S16 are the proofs.
`blindaxes.py --imports --population` lists only the partition generator. By reading, the fences are:
- `C = 40`, the picture range;
- `n ∈ [5, 8]`;
- the extra edges;
- the strip family on every fourth trial;
- the height coefficients, in `[−9, 9] ∖ {0}`.
The draws vary the graph, the picture and the heights, the variables of S14 and S16.

## S18 — control on T3's cells: no danger cell has `κ = 3` (session 2)

`python3 notes/attacks/short-core/drivers/t3_kappa.py --seed 1` (exit 0). The script redraws stage 1
of `strata.py`'s `short_cell` at each of T3's 72 danger cells at `d = 4`, the ones `short_danger` fixes
independently of the seed. It reports `κ = dim(Π_a ∩ Π_b)` and the number of neighbours of `a` and
of `b` in `V₁`. **Result:**
- `κ = 1` at 67 cells and `κ = 2` at 5. No cell has `κ = 3`, as S16 predicts.
- At `k = 3, 4, 5`, all 36 cells have `κ = 1`. The five `κ = 2` cells are at `k = 7, 8`, where
  `a` and `b` may be adjacent: two `th3` cells at arc length 1, two `same` cells and one `neck` cell.
- `a` and `b` have two or three neighbours in `V₁` at every cell. T3 holds no single-neighbour case.

`κ` is upper semicontinuous with `dim Π_a = dim Π_b = 3`, so each draw certifies `κ ≤` its value at
general base data of that cell. The cells are a capped search (`SHORT_PER = 2` per family, `d` and
`k`; Strata Result 24), not a census. The other fences are `strata.py`'s: `SHORT_TRIES`, `SHORT_NMAX`,
and `COORD = 1000` for the coordinates. `blindaxes.py` resolves no population inside the driver itself.

## S19 — the reduction's inputs at `D = 10`: two by reading, the insertion by hand (session 2)

(a) **The ear rank formula.** `BodyHingeFramework.finrank_span_rigidityRows_ear_eq` (`Ear.lean:296`)
is stated for `BodyHingeFramework K d` at every grade `d`. Its hypotheses are the ear's shape and
nonzero ear hinges (`hC`). At grade 3, `ScrewSpace K 3 = Λ³K⁵` has dimension 10, and the formula reads
`rank G = rank G[V₁] + 9(k + 1) + dim(ρ + Λ) − 10` for an ear with `k` interior bodies.

(b) **The deficiency bounds.** `Graph.splitOff_deficiency_le_of_eq_left` (`SplitOffDeficiency.lean:181`)
and `Graph.deficiency_induce_add_le_of_ear` (`Ear.lean:429`) are stated at every `n` with
`1 ≤ bodyBarDim n`, and `bodyBarDim 4 = 10`.

(c) **The insertion, in `Λ²V` for any `V = K^{N+1}`, `D = dim Λ²V`, `K` infinite.**
- *(I1, gain.)* Let `R ⊆ Λ²V` and `y, y', u ∈ V`, and suppose `y∧u ∉ W := R + K·y∧y'`. Then some `t ≠ 0`
  has `dim(R + span{y∧(y + tu), (y + tu)∧y'}) ≥ dim W + 1`.
  *Proof.* For `t ≠ 0`, write `N_t` for this span. It holds `y∧u = t⁻¹·y∧(y + tu)` and
  `(y + tu)∧y' = y∧y' + t·u∧y'`.
  - If `y∧y' ∈ R`, then `W = R` and `N_t ⊇ R + K·y∧u`, which has dimension `dim W + 1`.
  - Otherwise `dim W = dim R + 1`, and `y∧y' ∉ R + K·y∧u`. (If `y∧y' = r + c·y∧u` with `r ∈ R`, then
    `c ≠ 0`, and `y∧u ∈ W`.) A vector off a subspace stays off it along a line at some nonzero
    parameter, which is `exists_ne_zero_add_smul_notMem`, a statement in any module. So some `t ≠ 0` has
    `(y + tu)∧y' ∉ R + K·y∧u`, and then `dim N_t ≥ dim R + 2 = dim W + 1`. ∎
- *(I2, star.)* Let `y₁, y₃` be affine (last coordinate 1), and `W = R + K·y₁∧y₃`. Suppose that
  `star(y₁) + star(y₃) ⊆ W` implies `W = Λ²V`. Then some affine `x₂` has
  `dim(R + span{y₁∧x₂, x₂∧y₃}) ≥ min(dim W + 1, D)`.
  *Proof.*
  - If `W` holds both stars, then `W = Λ²V`. Take `x₂ = y₁`; the span is `W`, of dimension `D`.
  - If `star(y₁) ⊄ W`: `V = K·y₁ ⊕ {u_N = 0}` and `y₁∧y₁ = 0`, so `star(y₁)` is spanned by the
    `y₁∧u` with `u_N = 0`. Some such `u` has `y₁∧u ∉ W`. I1 with `(y, y') = (y₁, y₃)` gives `t ≠ 0`,
    and `x₂ = y₁ + tu` is affine.
  - If `star(y₃) ⊄ W`: the same with `(y, y') = (y₃, y₁)`. `W` and the new span are symmetric in the
    two ends, because `y₃∧y₁ = −y₁∧y₃`. ∎

This is the proof of `exists_insertion_gain` and `exists_insertion_of_star_sup_star` (`Lines.lean:488`
and after), with `finrank_screwSpace_two = 6` replaced by `D`. Nothing else in them reads the
dimension. At `d = 4`, `D = 10`, and the step uses I2 with `R = ρ +` the joins of `G''`'s ear other
than `y₁∧y₃`, as `exists_insertion_three` and `-four` do.

## S20 — the `P⁴` factoring at `k = 3, 4, 5`, by hand (session 2; O1d)

**Statement.** Take `G`, `V₁`, the open ear `a − x₁ − ⋯ − x_k − b` with `k ∈ {3, 4, 5}`, and `G''`
(`x₂` suppressed), as in brief §1, with `G[V₁]` and `G''` attaining in `P⁴`. Suppose the base data
`(q, z, la, lb, ρ)` are those of the `P⁴` reading of `Graph.exists_earBase_splitOff`, with two more
properties:
- (P) `p_a` and `p_b` are independent;
- (B) `la ≠ lb`, or `ρ ⊆ Λ²Π_a` (`Π_a = graph la`).
Then `G` attains in `P⁴`. So `of_openEar_splitOff`'s `hins` transcribes to `d = 4` once it is restricted
to base data with (P) and (B). S21 supplies them.

**Proof.** Follow `of_openEar_splitOff` (`Short.lean:588–766`) with `D = 10`.
1. *Ear data of `G''`.* Three polynomials: `G''` at target (nonzero at the base data's `s₁`), the
   admissible pictures, and `Qx` (step 3). Take a common non-root `sy`.
2. *`dim W`.* The ear rank formula at `G''` (S19 (a); `k − 1` interior bodies and `k` joins) reads
   `rank G'' = rank G[V₁] + 9k + dim W − 10`. With `rank G'' ≥ 10(|V₁| + k − 2) − def(G'')` and
   `rank G[V₁] = 10(|V₁| − 1) − f`, it gives `dim W ≥ k + f − def(G'')`.
3. *`Qx` and the insertion.* I2 (S19 (c)) gives an affine `x₂` with
   `dim(ρ + Λ_G) ≥ min(dim W + 1, 10)`, wherever `W ⊇ S(y)` implies `W = Λ²V`. That implication holds
   off a nonzero polynomial in the ear datum `y`, in four cases:
   - `k = 4`: S7, for every `ρ` and `κ`;
   - `k = 5`: S8, likewise;
   - `k = 3` with `la ≠ lb` (so `κ ≤ 2`): S6, with S12's existence, which uses (P);
   - `k = 3` with `la = lb` and `ρ ⊆ Λ²Π_a`: `y₁, y₃ ∈ Π_a`, so `W ⊆ Λ²Π_a` has dimension at most 3, less
     than `dim S(y) = 7` once `y₁, y₃` are independent. The premise fails off a nonzero 2-minor of `(y₁, y₃)`.
   The ear points are affine-linear in the ear data `s`, and affine points are Zariski-dense in `Π_a`,
   `Π_b` and `V`, so each condition is a nonzero polynomial `Qx` in `s`.
4. *Counts.* `dim(ρ + Λ_G) ≥ min(k + 1 + f − def(G''), 10) ≥ min(k + 1 + f − def(G), 10) = n₀ :=
   k + 1 + f − def(G)`. This uses `def(G'') ≤ def(G)` and `f + k + 1 − 10 ≤ def(G)` (S19 (b)).
5. *Ear data of `G`.* The bound `dim(ρ + Λ_G) ≥ n₀` holds at `sy` with `x₂` at its body, so it holds
   off a nonzero polynomial. Take a common non-root `s₀` with the main-picture polynomial of `G`. The
   ear rank formula at `G` gives `rank G = rank G[V₁] + 9(k + 1) + dim(ρ + Λ_G) − 10 ≥
   10(|V₁| + k − 1) − def(G)`, the target. ∎

Against `P³`, three things change: 6 becomes 10, the insertion is I2 in `Λ²K⁵`, and `hins` takes (P)
and (B). At `k = 4, 5` it needs neither (S7, S8). At `k = 3`, S2 shows that the hypothesis is needed.
The formal ports (the `P⁴` carrier, `earConfig`, the polynomial lemmas at grade 3) are PD-STATE's and
PD-STEPS', not this attack's.

## S21 — the base data can be chosen with (P) and (B) (session 2; O4)

**Statement.** The `P⁴` reading of `Graph.exists_earBase_splitOff` can also deliver (P) and (B).

**Proof.** The `P³` lemma picks `q'` off `P₁ P₂ Pm`, then picks `zs ∈ L_{G''}(q')` as a common non-root
of `R₁ ∘ restrict` and `R₂`, and reads `la, lb` off `zs`. Make two additions.
- *On `q'`, extra factors.* `q_{a,0} − q_{b,0}`, which gives (P), since `p_a, p_b` are affine. The
  3×3 picture determinants of triples in the closed neighbourhoods of `a` and `b`, in `G[V₁]` and in
  `G''`. And, when `a ≁ b`, S15's polynomial for `G[V₁] + ab`.
- *On `zs`, a linear form `ℓ`.* `la` solves `z_v = la·q̂_v` on three non-collinear members of
  `N_{G''}[a]`, so it is linear in `zs`, and likewise `lb`. Let `ℓ` be a coordinate of `la − lb` that is
  nonzero somewhere on `L_{G''}(q')`, if there is one. `L_{G''}(q')` is a vector space over the infinite
  `K`, so the three have a common non-root.

If `ℓ` exists, then `la ≠ lb` at `zs`. Otherwise `la = lb` on all of `L_{G''}(q')`, and two cases remain.
- *`a` has a single neighbour `w` in `V₁`* (or `b`, symmetrically). Then `z_{x₁}` is free in
  `L_{G''}(q')`. Every closed neighbourhood holding `x₁` has three members: `N_{G''}[a] = {a, w, x₁}`,
  `N_{G''}[x₁] = {a, x₁, x₃}` and `N_{G''}[x₃]`, where `x₃` is the next ear body of `G''` at every `k`
  and has degree 2. Three points
  with non-collinear pictures always lift into a 3-space (S9 (i)). So `la(q̂_{x₁}) = z_{x₁}` varies,
  while `lb` does not read `z_{x₁}`, because `x₁ ∉ N_{G''}[b]`. So this case does not arise.
- *Both have two or more neighbours in `V₁`.* Then `la − lb = (λ¹_a − λ¹_b, λ²_a − λ²_b)` reads only
  `z|_{V₁}`. The restriction `L_{G''}(q') → L_{G[V₁]}(q') = L₁(q')²` is onto: it is
  `Graph.earExtend_mem_liftingSpace`, used coordinatewise. So `z¹ ↦ λ_a − λ_b` vanishes on `L₁(q')`,
  and `ρ⁽²⁾ = 0` (S16 step 1). S16 steps 2–3 then give `ρ ⊆ Λ²Π_a` at every height. ∎

**Consequence.** With S14–S21, SHORT-CORE and the `P⁴` step it serves hold at `k = 3, 4, 5` by hand.
The statement proved is the brief's §3 at base data general in S21's sense, a nonempty Zariski-open
condition that the step's own choice of base data meets. It is not proved at every base datum where
`G[V₁]` and `G''` attain.

## S22 — every `d`, `k = 3`: S6's two curves force divisibility by `p_a ∧ p_b` (session 2)

**Setting.** `V = K^{d+1}`, `d ≥ 4`. The wedge pairs `Λ²V × Λ^{d−1}V → Λ^{d+1}V` perfectly. Let
`Q = V/⟨y₁, y₃⟩`, and write `ω̄` for an image in `Λ^• Q`. Then `S(y)° = T(y) = y₁∧y₃∧Λ^{d−3}V`, the
`ω` with `ω∧y₁ = ω∧y₃ = 0`, of dimension `C(d − 1, 2)`. S1 holds verbatim. Put
`M(y)ζ = y₁∧y₃∧ζ mod R` on `Λ^{d−3}V`, and let `U₁` be as in S6.

**Statement.** Let `k = 3`, let `ρ` be any subspace, and let `y ∈ U₁` with `p_a, y₁, y₃, p_b` independent.
If `W(y) ⊇ S(y)` and `W(y) ≠ Λ²V`, then `ker M(y) ≠ 0` modulo `⟨y₁,y₃⟩∧Λ^{d−4}V`. Every `ζ` in the kernel
has `ζ̄ ∈ p̄_a∧p̄_b∧Λ^{d−5}Q`. At `d = 4` this is `ζ̄ = 0`, which is S6.

**Proof.** As in S6, `J ⊆ S`, so `R ∩ T = R ∩ J° ≠ 0`, and the kernel is nonzero. Curve A,
`(y₁ + t p_a, y₃)`, gives `δ_A = p_a∧y₃∧ζ + y₁∧y₃∧ζ' ∈ R`. Its first term shares `p_a, y₃, y₃` with the
three joins, and its second lies in `T ⊆ J°`. So `δ_A ∈ T`, and `δ_A ∧ y₁ = ±y₁∧y₃∧p_a∧ζ = 0`. That is,
`p̄_a∧ζ̄ = 0` in `Λ^{d−2}Q`. `p̄_a ≠ 0`, and the Koszul complex of a nonzero vector is exact, so
`ζ̄ ∈ p̄_a∧Λ^{d−4}Q`. Curve B gives `ζ̄ ∈ p̄_b∧Λ^{d−4}Q` in the same way. With `p̄_a, p̄_b` independent,
`ζ̄ ∈ p̄_a∧p̄_b∧Λ^{d−5}Q`. ∎

**What it leaves at `d = 5`.** Here `ker M(y) ⊆ K·p̄_a∧p̄_b`, so `y₁∧y₃∧p_a∧p_b ∈ R`. A third curve
`(y₁ + t u, y₃)`, with `u ∈ Π_a` general, has first term `u∧y₃∧p_a∧p_b`, which shares a vector with
each of the three joins. It gives `u∧y₃∧p_a∧p_b∧y₁ = 0`. That is false when `Π_a ∩ ⟨y₃, p_b⟩ = 0`, which
a general `y₃ ∈ Π_b` meets when `κ = 0`, or when `κ = 1` with `p_b ∉ Π_a` (a sketch, not checked
beyond this paragraph). *Not yet written as a result:* the case `κ = 2` at `d = 5`,
and `k ≥ 4` at `d ≥ 5`. `κ = 3` closes at every `d` by S14–S16 read at `d − 2` heights: `ρ⁽²⁾ = 0` again
gives `ρ ⊆ Λ²Π`, and `dim Λ²Π = 3 < 2d − 1`.

## S23 — control for the secondary target: `κ` on T3's 126 cells at `d = 5` (session 2)

`python3 notes/attacks/short-core/drivers/t3_kappa.py --seed 1 --dims 5` (exit 0; it fails only on a
`κ = 3` cell at `d = 4`). `κ = 0` at 115 cells, `κ = 1` at 5 and `κ = 2` at 6. In SHORT's range at
`d = 5`, `3 ≤ k ≤ C(4, 2) + 2 = 8`, all 72 cells have `κ = 0`, and every `κ ≥ 1` cell has `k ≥ 9`. As in
S18, each draw certifies `κ ≤` its value at general base data of that cell. The cells are a capped
search, not a census. So S22's third curve, which needs `κ = 0` or `κ = 1` with `p_b ∉ Π_a`, covers
every `d = 5`, `k = 3` cell T3 holds.

## S24 — the independent reading of S14–S16 (session 2)

**Review.** A fresh `general-purpose` reader checked S14, S15 and S16 by hand against the definition
bodies (`partitionDef`, `bodyBarDim`, `infinitesimalMotions` and the hinge row blocks,
`panelSupportExtensor`, `IsGenericNormals`). It ran no numerics. **Verdict: all three CONFIRMED.**
- **S14.** Every step holds. Step 0 needs only the crossing hinges nonzero. Step 3's change `−2·[P
  separates a, b]` is `partitionDef` at `n = 2`. Step 5 holds even when `ab` is the only edge joining
  two components of `F[X]`.
- **S15.** The mathematics holds.
  - *Citation slip, corrected in S15.* The polynomial comes from `exists_isGenericNormals_abundance`.
  - *The minor step* is `PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`
    (`GenericityDevice.lean:765`), at every grade, pulled back along `q ↦ (q, 1)`.
  - *Scaling.* `infinitesimalMotions` reads only `K ∙ supportExtensor e`, so scaling a normal leaves
    the rows literally unchanged.
- **S16.** Every step holds.
  - Degree-1 bodies of `G[V₁]` can only be `a` or `b`, by `hsep` and minimum degree 2, and a pendant
    body is never in `H` anyway.
  - A disconnected `G[V₁]` gives `κ ≤ 2`.
  - `P⁴` motions enter only through S3's telescoping. S10 is not used.

**Formalization costs it named (not gaps).**
- `hspan : V(G) = Set.univ` forces the `P²` framework of `G[V₁] + ab` onto the subtype `↥V₁`, with
  the deficiency carried along (`partitionDef_map`).
- The new edge `ab` needs a label outside `E(G[V₁])`; an ear label can be reused.
- `exists_mvPolynomial_le_finrank_ofNormals_bind` is stated at `k := 2` only, so it needs a `k := 1`
  sibling.
