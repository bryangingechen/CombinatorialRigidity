## §(K-main) — Step MC13 — the short ear step with the antecedent (a second reading of (MC-27))

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

> **(MC-45)** `[PROVED]` *(`k = 3`, every orbit; its `r = 1` use of (MC-26) has a hand proof, (MC-135))* For every `ρ` and every flag pair with
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

> **(MC-46)** `[PROVED]` *(`k = 2`, orbits (i) and (ii); the orbit table by hand over every field: (MC-138))* Let the flag pair be in orbit (i) or (ii),
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
- orbit (ii): `d_y = 5` where `l₀l₁l₂ ≠ 0`; `4` where `l₀l₂ = 0 ≠ l₁`; `3` on `l₁ = 0 ≠ l₀l₂`; `1` at `L₀`
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
> **(i)** `[PROVED]` In orbit (iv), `Λ₂ = Λ²π` at every 2-ear placement of generic span (the span drops to `⟨n⟩` when `x₁, x₂ ∈ n`; *second
reading, 2026-09-25*). So
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

> **(MC-50)** `[INFORMAL]` *(gap: the first-order limit plane is a sketch; second reader owed.
> 2026-09-24: the gap is closed by (MC-108), and the reduction is the theorem (MC-110), Step MC18)*
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
>
> *(2026-09-24, Steps MC17 and MC18, modulo Jackson–Jordán and not yet second-read:
> - (a) closes for `a ≁ b` ((MC-88), (MC-93), (MC-114));
> - `k = 2` with `a ∼ b` closes ((MC-95));
> - `k = 1` with `dim U = 1` closes ((MC-113));
> - (c) closes at `δ ≤ 2` ((MC-100)–(MC-102), (MC-112)).
>
> The one open cell is (MC-117): `k = 1`, `δ₂ = 3`, `δ ∈ {3, 4}`, where the chord criterion fails.
> `k = 1` with `a ∼ b` is out of the ear route's reach and never needed ((MC-96)).)*

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

