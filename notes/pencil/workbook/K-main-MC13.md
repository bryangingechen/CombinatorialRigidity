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

> **(MC-45)** `[PROVED]` *(`k = 3`, every orbit; its `r = 1` use of (MC-26) has a hand proof, (MC-135); the step's proof superseded on (MC-89)'s route 2026-09-27 by (MC-181), below — still proved, no longer consumed)* For every `ρ` and every flag pair with
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

**The `k = 3, 4` ear steps by insertion (2026-09-27, found by formalization).** *Added by the
Phase-40 SHORT design recon (opus), `notes/Phase40-design.md` §3 STEPS (SHORT). On (MC-89)'s route
the `k = 4` step went through the 2-ear gadget (MC-24) and the collision lemma (MC-136), in four
orbits, and the `k = 3` step through (MC-45)'s `r = 1, 2, ≥ 3` split, with (MC-26), (MC-135) and the
(α)/(β) classification. Both are re-proved here by one move: remove the ear's second interior body,
then put it back along a curve. The antecedent is `G` with that body suppressed. The count is taken
against it directly, with no `δ`, no exact (MC-17), and no (MC-22), (MC-24) or (MC-44).
(MC-179)–(MC-182) are one writer's and **not yet second-read**; a fresh second reading is commissioned
(`notes/pencil/adjudications.md`, 2026-09-27, decision 1). They are hand proofs; no driver. Notation
as above, in Step MC10 and in Step MC20. `⟨·,·⟩` is the Klein pairing, and `star(p) := {p ∧ v : v ∈ K⁴}`
is the space of lines through `p`. The interior bodies are `x₁, …, x_k`, with `x₀ := a` and
`x_{k+1} := b`.*

> **(MC-179)** `[PROVED]` *(four line lemmas; found by formalization, SHORT recon 2026-09-27; not yet
> second-read)* Let `K` be a field.
> **(a)** *(the tetrahedron)* If `p₀, p₁, p₂, p₃ ∈ K⁴` are linearly independent, the six joins
> `p_i ∧ p_j`, `i < j`, are a basis of `Λ²K⁴`.
> **(b)** *(two stars)* If `y, y′ ∈ K⁴` are linearly independent, then
> `star(y) + star(y′) = (y ∧ y′)^⊥`, of dimension 5.
> **(c)** *(the bilinear lemma; (MC-135)(ii)'s `k = 2` step, restated)* Let `π, π′` be planes, and
> let `c ∈ Λ²K⁴` satisfy `⟨c, u ∧ v⟩ = 0` for every `u ∈ π̂` and every `v ∈ π̂′`. If `π ≠ π′`, then
> `c = 0`. If `π = π′`, then `c ∈ Λ²π`.
> **(d)** *(the insertion lemma)* Let `K` be infinite. Let `ρ ⊆ Λ²K⁴` be a subspace, `F ⊂ Λ²K⁴` a
> finite set, `y, y′, u ∈ K⁴`, and `W := ρ + span F + ⟨y ∧ y′⟩`. Then for all but finitely many `t ∈ K`,
> `dim(ρ + span F + ⟨y ∧ (y + tu), (y + tu) ∧ y′⟩) ≥ dim(W + ⟨y ∧ u⟩)`. So the left side is at least
> `dim W`, and at least `dim W + 1` when `y ∧ u ∉ W`.

*Proof.* **(a)** Pair a vanishing combination `Σ c_{ij} p_i ∧ p_j = 0` with the opposite edge
`p_k ∧ p_l`. Here `⟨p_i ∧ p_j, p_k ∧ p_l⟩ = det(p_i, p_j, p_k, p_l)`. It is `±det(p₀, p₁, p₂, p₃) ≠ 0`
when `{i, j, k, l} = {0, 1, 2, 3}`, and `0` when the two pairs share an index. So `c_{ij} = 0`, and six
independent vectors are a basis.

**(b)** Extend `y, y′` to a basis `y, y′, e, e′`.
- `star(y) + star(y′)` contains `y∧y′`, `y∧e`, `y∧e′`, `y′∧e`, `y′∧e′`, five of the six basis vectors of
  (a). So its dimension is at least 5.
- Every line through `y` or `y′` meets the line `yy′`. So `star(y) + star(y′) ⊆ (y ∧ y′)^⊥`.
- That space has dimension 5, since the pairing is nondegenerate and `y ∧ y′ ≠ 0`.

**(c)** This is (MC-135)(ii)'s argument at `k = 2`, with its `k = 3` basis.
- `π ≠ π′`: write `π̂ = m̂ ⊕ ⟨α⟩` and `π̂′ = m̂ ⊕ ⟨β⟩`, with `m̂ = ⟨f₁, f₂⟩ = π̂ ∩ π̂′`. Then `f₁, f₂, α, β` is
  a basis of `K⁴`. So by (a) the six vectors `f₁∧f₂, α∧f₁, α∧f₂, f₁∧β, f₂∧β, α∧β`, all of the form
  `u ∧ v` with `u ∈ π̂` and `v ∈ π̂′`, are a basis. Hence `c ⊥ Λ²K⁴`, and `c = 0`.
- `π = π′`: `c ∈ (Λ²π)^⊥`. Any two lines of `π` meet, so `Λ²π ⊆ (Λ²π)^⊥`, and both have dimension 3.
  So `c ∈ Λ²π`.

**(d)** For `t ≠ 0`, `y ∧ (y + tu) = t·(y ∧ u)` and `(y + tu) ∧ y′ = y ∧ y′ + t·(u ∧ y′)`. So the
space in question is `S(t) := ρ + span F + ⟨y ∧ u, y ∧ y′ + t·(u ∧ y′)⟩`, and `S(0) = W + ⟨y ∧ u⟩`.
- Choose a basis of `S(0)` from a basis of `ρ + span F`, together with `y ∧ y′` and `y ∧ u`.
- In it, replace `y ∧ y′`, if present, by `y ∧ y′ + t·(u ∧ y′)`. The resulting family is affine in `t`,
  lies in `S(t)` for `t ≠ 0`, and is independent at `t = 0`.
- A maximal minor of its coordinate matrix is a polynomial in `t`, nonzero at `t = 0`. Off its finitely
  many roots, and off `t = 0`, the family is independent in `S(t)`. ∎

(d) is (MC-45)'s splitting degeneration: at `t = 0` the reinserted body collides with `y`. The two new
hinges become `y ∧ u` (after dividing by `t`) and the antecedent's hinge `y ∧ y′`. What is new below is
the count against the antecedent, and one line argument in place of the classification.

> **(MC-182)** `[PROVED]` *(suppressing a degree-2 body does not raise the deficiency; any finite graph,
> both `D`; found by formalization, SHORT recon 2026-09-27; not yet second-read)* Let `x` be a vertex of
> `G` whose only edges are `e_u = xu` and `e_w = xw`, with `u ≠ w` and `u, w ≠ x`. Let `G″` be `G` with
> `x` suppressed: delete `x`, and relink the freed label `e_u` to join `u` and `w`. Then
> **`def_D(G″) ≤ def_D(G)`**.

*Proof.* Extend a partition of `V(G″)` to `V(G)` by putting `x` in `u`'s part. The number of parts is
unchanged, and `e_u = xu` is internal. `e_w = xw` crosses exactly when `u` and `w` lie in different
parts, that is, exactly when the relinked `e_u = uw` crosses in `G″`. Every other edge keeps its ends and
its status. So the value is unchanged. ∎

This is Katoh–Tanigawa's partition extension for splitting off (KT 2011, Lemma 4.3(i); landed as
`splitOff_deficiency_le`, where the new label is fresh), with the freed label reused. It is also
(MC-175)(i)'s argument. In Lean, `G″ = G.splitOff x u w e_u`, the construction of (MC-176)'s `G₁`.

> **(MC-180)** `[PROVED]` *(the `k = 4` open-ear step by insertion; every orbit, `a ∼ b` allowed, no
> Jackson–Jordán; replaces (MC-24)/(MC-25) with (MC-136) on (MC-89)'s route; found by formalization,
> SHORT recon 2026-09-27; not yet second-read)* Let `K` be infinite. Let `G = G′ + ear₄` be an open ear
> `a − x₁ − x₂ − x₃ − x₄ − b`, with `a ≠ b` possibly adjacent and `G` satisfying (H). Let `G″` be `G` with
> `x₂` suppressed ((MC-182), the label of `x₁x₂` relinked to `x₁x₃`), so
> `G″ = G′ + (a − x₁ − x₃ − x₄ − b)`. **If `X₀(G′)` and `X₀(G″)` attain, then `X₀(G)` attains.** Under the
> strong induction both hypotheses hold. `G′` and `G″` satisfy (H) and are smaller than `G`
> ((MC-55)(i)); `G″` is simple because `x₁ ≁ x₃` in `G`.

> **(MC-181)** `[PROVED]` *(the `k = 3` open-ear step by insertion; every orbit, `a ∼ b` allowed, no
> Jackson–Jordán; replaces (MC-45)'s proof of the step on (MC-89)'s route; found by formalization, SHORT
> recon 2026-09-27; not yet second-read)* Let `K` be infinite. Let `G = G′ + ear₃` be an open ear
> `a − x₁ − x₂ − x₃ − b`, with `a ≠ b` possibly adjacent and `G` satisfying (H). Let `G″` be `G` with `x₂`
> suppressed, so `G″ = G′ + (a − x₁ − x₃ − b)`. **If `X₀(G′)` and `X₀(G″)` attain, then `X₀(G)`
> attains.** The hypotheses are supplied as in (MC-180).

*Proof of (MC-180) and (MC-181).* Let `k ∈ {3, 4}`, `V₁ := V(G′)` and `f := def₃(G′)`.

**Step 0: what is counted.** At every configuration whose ear hinges are nonzero, (MC-16) in rank form
gives `rank R_G = rank R_{G′} + 5k − 1 + dim(ρ + Λ_k)`.
- (MC-177)(iii) states this with `a ≁ b`. (MC-16)'s own proof, by solving along the chain, uses no
  condition on `a, b`. Nonzero hinges make the ear's `ω` determine its bodies, and
  `rank = 6|V| − dim M`. Phase 40g formalized it at every adjacency (`lem:block-rank-ear`).
- Likewise at `G″`, with `k − 1`.

The target of `G` is `6(|V| − 1) − def₃(G)`. A configuration over `U(G)`, with nonzero ear hinges, at
which `G′` attains, therefore attains for `G` as soon as

  **(★)** `dim(ρ + Λ_k) ≥ k + 1 + f − def₃(G)`,

and then `X₀(G)` attains by (MC-2) (one point of `B` at the target rank).

**Step 1: the base data, fixed first.**
- Choose a picture `q*` in `U(G) ∩ U(G′) ∩ U(G″)`. Each is a nonempty Zariski-open subset of `K^{2V}` (the
  last two depend on fewer coordinates), and `K^{2V}` is irreducible.
- Over `q*`, restriction `L_{G″}(q*) → L_{G′}(q*)` is onto ((MC-18)(a), since `G″`'s ear has
  `k − 1 ≥ 2` interior bodies). So the heights where `G′` attains pull back to a nonempty open subset of
  `L_{G″}(q*)`. The heights where `G″` attains are another. Choose `z*` in both.
- Fix the **base data** `(q₁, z₁)`: `q*` and `z*` restricted to `V₁`. `G′` attains there. So `ρ`, `p_a`,
  `p_b`, `π_a` and `π_b` are fixed from now on.

*How `π_a` is fixed.* `q₁` is admissible for `G′`, so `q₁(N_{G′}[a])` is not collinear. By (MC-1), the
plane `π_a : z = h_a(x, y)` through the points of `N_{G′}[a]` is unique.
- In particular `a` has at least two neighbours in `V₁`. If it had only one, `N_{G′}[a]` would be two
  points. Then no picture would be admissible for `G′`, `U(G′)` would be empty, and `X₀(G′)` could not
  attain. Under the strong induction `G′` satisfies (H) anyway.
- In `G` and in `G″`, `N[a] = N_{G′}[a] ∪ {x₁}`, and the plane at `a` is already fixed by `N_{G′}[a]`. So
  every configuration of `G` or `G″` with base data `(q₁, z₁)` has `x₁ ∈ π_a`, for this `π_a`. Likewise
  `x_k ∈ π_b`.

**Step 2: the ear data, chosen second.** Hold `(q₁, z₁)` fixed. The **ear data** of `G` are the
pictures `q_{x₁}, …, q_{x_k} ∈ K²` and the heights `w₂, …, w_{k−1}` of the middle bodies. Their points
are `x₁ = (q_{x₁}, h_a(q_{x₁}), 1)`, `x_i = (q_{x_i}, w_i, 1)` for `1 < i < k`, and
`x_k = (q_{x_k}, h_b(q_{x_k}), 1)`. Over a picture `q₁ ⊕ (q_{x_i})` admissible for `G`, these are exactly
the configurations of `L_G` with base heights `z₁` ((MC-18)(a)). The ear data of `G″` are those of its
bodies `x₁, x₃, …, x_k`, in the same way.

Each ear-data space is an affine space, hence irreducible. With `ρ` fixed, every condition below is
polynomial in the ear data:
- **(E1)** `q₁ ⊕ (q_{x_i}) ∈ U(G)`. This is open in the ear pictures, and nonempty: it contains `q*`'s.
- **(E2)** every ear hinge is nonzero (adjacent pictures distinct). Open and nonempty.
- **(E3)** for `G″`: `rank R_{G″} ≥ 6(|V(G″)| − 1) − def₃(G″)`. This is a maximal minor of the rigidity
  matrix, nonzero at `z*`'s ear data, so it is open and nonempty. Those ear data are of this form:
  `z*_{x₁} = h_a(q*_{x₁})`, because `z* ∈ L_{G″}(q*)` and `π_a` is unique. A rank lower bound needs no
  main picture.

At a `G″`-placement `y` with (E2) and (E3), where `y₁ := x₁` and `y₃ := x₃`, Step 0 at `G″` and
`rank R_{G′}(q₁, z₁) = 6(|V₁| − 1) − f` give

  **(1)** `dim W ≥ k + f − def₃(G″)`, where `W := ρ + Λ_{k−1}(y)`.

**Step 3: the insertion.** Take a `G″`-placement `y` with (E2), (E3) and Step 4's extra open condition.
- Put `x₂` back at `x₂(t) := y₁ + tu` or at `x₂(t) := y₃ + tu`, with `u ∈ K³ × {0}`, and keep every other
  body as in `y`. Then `x₂(t)` is an affine point. `x₂` is a middle body of `G`, so its picture and height
  are free.
- The ear hinges are those of `y`, except that `y₁y₃` is replaced by `y₁ ∧ x₂(t)` and `x₂(t) ∧ y₃`.
- Every line through an affine point `p` is `p ∧ u` with `u` of last coordinate `0`, since
  `p ∧ v = p ∧ (v − v₃p)`.
- Apply (MC-179)(d), with `F` the other hinges of `y` and `(y, y′) = (y₁, y₃)` or `(y₃, y₁)` (using
  `x ∧ y = −y ∧ x`). For all but finitely many `t`, it gives
  `dim(ρ + Λ_k(x(t))) ≥ dim W + 1` whenever the chosen star is not in `W`, and `≥ dim W` always.

So **`dim(ρ + Λ_k(x(t))) ≥ min(dim W + 1, 6)`** as soon as

  **(G)** `W = Λ²K⁴`, or `star(y₁) ⊄ W`, or `star(y₃) ⊄ W`.

Step 4 proves (G). The condition `dim(ρ + Λ_k(x)) ≥ min(dim W + 1, 6)` is a maximal minor in the ear data
of `G`, nonzero at `x(t)`. Intersect it with (E1) and (E2) for `G`. This gives a `G`-placement `x` over
a picture of `U(G)`, with nonzero hinges, at which `G′` attains and, by (1),
`dim(ρ + Λ_k(x)) ≥ min(k + 1 + f − def₃(G″), 6)`.

**Step 4 for (MC-180), `k = 4`: the tetrahedron.** Here `y = (y₁, y₃, y₄)`, with `y₁ ∈ π_a`, `y₃` free
and `y₄ ∈ π_b`, and `Λ₃(y) = ⟨p_a y₁, y₁ y₃, y₃ y₄, y₄ p_b⟩`. The extra open condition is: **`y₁, y₃, y₄, p_b`
are linearly independent** (not coplanar).
- *Why it holds at a configuration where `G″` and `G′` both attain.* In the ear data,
  `det(y₁, y₃, y₄, p_b)` is affine in `y₃`'s free height `w₃`. Its `w₃`-coefficient is `±` the `3 × 3`
  determinant of the homogeneous pictures `(q_{x₁}, 1)`, `(q_{x₄}, 1)` and `(q_b, 1)`, with `q_b` fixed by
  the base data. That coefficient is nonzero once `q_{x₁}` is off the line through `q_{x₄}` and `q_b`, so
  it is a nonzero polynomial. The determinant is therefore a nonzero polynomial on `G″`'s ear data, and
  its non-roots meet (E2) and (E3). At such a `y`, `G′` attains (the base data) and `G″` reaches its
  target rank (E3). That is the sense of "both attain" the proof uses.
- *(G).* Suppose `star(y₁) ⊆ W` and `star(y₃) ⊆ W`. Then `W` contains `y₁y₃`, `y₁y₄`, `y₁p_b`, `y₃y₄` and
  `y₃p_b`, and `y₄p_b ∈ Λ₃(y) ⊆ W`. These are the six edges of the tetrahedron, a basis by (MC-179)(a).
  So `W = Λ²K⁴`.

This replaces (MC-136). The only placement condition is one determinant, the same in every orbit.

**Step 4 for (MC-181), `k = 3`: the bilinear lemma.** Here `y = (y₁, y₃)`, with `y₁ ∈ π_a` and
`y₃ ∈ π_b`, and `Λ₂(y) = ⟨p_a y₁, y₁ y₃, y₃ p_b⟩`. In `G″`, `y₁ ∼ y₃`, so by (E2) their pictures differ,
and `y₁, y₃` are independent. By (MC-179)(b), `star(y₁) + star(y₃) = (y₁ ∧ y₃)^⊥` has dimension 5. There
are two cases on `ρ`, which the base data fix.
- *Case B:* `⟨c, u ∧ v⟩ = 0` for every `c ∈ ρ`, `u ∈ π̂_a`, `v ∈ π̂_b`. By (MC-179)(c):
  - if `π_a ≠ π_b`, then `ρ = 0` and `W = Λ₂(y)`;
  - if `π_a = π_b = π`, then `ρ ⊆ Λ²π`, and `W ⊆ Λ²π` (`p_a, y₁, y₃, p_b ∈ π`).

  Either way `dim W ≤ 3 < 5`, so one of the two stars is not in `W`: (G). No extra condition is needed.
- *Case A:* some `c ∈ ρ`, `u₀ ∈ π̂_a` and `v₀ ∈ π̂_b` have `⟨c, u₀ ∧ v₀⟩ ≠ 0`. The extra open condition is
  **`⟨c, y₁ ∧ y₃⟩ ≠ 0`**.
  - *Why it can be met.* Write `π̂_a = {(s₁, s₂, h_a(s), s₃) : s ∈ K³}`, with `h_a` in homogeneous form,
    and `π̂_b` likewise. Then `(s, s′) ↦ ⟨c, ŷ(s) ∧ ŷ′(s′)⟩` is bilinear on `K³ × K³` and nonzero at
    `(u₀, v₀)`. The affine points (`s₃ = 1`) span `K³`, so it is nonzero at some affine pair.
  - On the affine pairs it is `⟨c, y₁ ∧ y₃⟩` as a polynomial in `(q_{x₁}, q_{x₃})`, so that polynomial is
    nonzero. Its non-roots meet (E2) and (E3). This is where the order of Steps 1–2 is used: `c` is
    chosen from `ρ` before the ear data.
  - *(G).* Now `c ∉ (y₁ ∧ y₃)^⊥ = star(y₁) + star(y₃)`. If both stars were in `W`, then `W` would contain
    that 5-dimensional space and also `c ∈ ρ ⊆ W`, so `W = Λ²K⁴`.

Case B with `π_a = π_b` is (MC-47)(i)'s situation (orbit (iv), `Λ₂ = Λ²π`). (MC-45)'s four orbits
collapse to the one question `π_a = π_b`.

**Step 5: the count.** (★) holds, since:
- `k + 1 + f − def₃(G″) ≥ k + 1 + f − def₃(G)`, because `def₃(G″) ≤ def₃(G)` (MC-182);
- `6 ≥ k + 1 + f − def₃(G)`, because `def₃(G) ≥ f + k − 5`. This is (MC-17)'s separated count: extend a
  partition of `V₁` by the ear bodies as singletons, for `k` new parts and at most `k + 1` crossing edges.
  It holds whether or not `a ∼ b` (Phase 40g, `lem:deficiency-ear`).

So `X₀(G)` attains. Nothing here uses `δ`, the exact value of (MC-17), (MC-22), (MC-24), (MC-44),
`a ≁ b`, or the orbit of the flag pair. ∎

*Consequences.* (MC-180) and (MC-181) cover the `k = 4` and `k = 3` chains of (MC-79)(v) and (MC-139),
in every orbit and with `a ∼ b` allowed. They also cover (MC-54) at `k = 3, 4`, which needs no
hypothesis on `δ` there. (MC-24), (MC-25)'s proof, (MC-136), (MC-45)'s proof of the step and (MC-26)'s
links are off (MC-89)'s route, and stay proved.

> **(MC-46)** `[PROVED]` *(`k = 2`, orbits (i) and (ii); the orbit table by hand over every field: (MC-138); superseded on (MC-89)'s route 2026-09-26 by (MC-173) and (MC-176), below — still proved, no longer consumed)* Let the flag pair be in orbit (i) or (ii),
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

**The `k = 2` cell without the orbit count (2026-09-26, found by formalization).** *Added by the
Phase-40 ORBIT recon (opus), `notes/Phase40-design.md` §4. (MC-46)'s proof counts dimensions of
incidence varieties and orbits, which has no polynomial-level form, so the cell it serves on
(MC-89)'s route (`k = 2`, `a ≁ b`, `δ₂ ≥ 2`, (MC-79)(v)) is re-proved here. (MC-173)–(MC-176)
were **second-read on 2026-09-26** by a fresh read-only reader (the PI's D1,
`notes/pencil/adjudications.md`). The reader re-derived every step, checked every citation's
hypotheses and re-ran `orbitlink.py --link`, `--witness` and `--e2e`. It found no refutation and
no gap. Its own exact cross-check of (MC-173) and (MC-175) was a throwaway probe: attempted, no
figure; script not retained. It repaired (MC-173)'s chart bullet and its `--link` evidence line here, and Step MC20's
Part I row and (MC-141). It added (MC-177) (the path brick, beside (MC-176)) and (MC-178)
((MC-175)(iii) with equality), which are one writer's. Driver `w4/orbitlink.py` (new). Notation as
above and in Step MC20; the ear points are `p_a, x₁, x₂, p_b`, and `Λ₁(y) := span(p_a∧y, y∧p_b)`
for `y ∈ m`.*

On the route the flag pair is in orbit (i) ((MC-176), Step 1), and there a sharper form of
(MC-26)'s first link does all of `(P₁) ⟹ (P₂)`. The idea is to choose the link's extra limit
direction so that it misses `ρ + Λ₁(y)`.

> **(MC-173)** `[PROVED]` *(the refined 2-ear link, orbit (i); found by formalization, ORBIT recon
> 2026-09-26; second-read 2026-09-26, chart bullet repaired)* Let `K` be an infinite field, let the flag pair
> `(p_a, π_a; p_b, π_b)` be in orbit (i), let `y ∈ m = π_a ∩ π_b`, and let `ρ ⊆ Λ²K⁴` be any
> subspace. Put `s := dim(ρ + Λ₁(y))`. Then the 2-ear placements `x = (x₁, x₂)`, `x₁ ∈ π_a`,
> `x₂ ∈ π_b`, with **`dim(ρ + Λ₂(x)) ≥ min(s + 1, 6)`** contain the nonzero locus of a nonzero
> polynomial in the placement coordinates. In the affine charts `x₁ = (q₁, h_a(q₁), 1)` and
> `x₂ = (q₂, h_b(q₂), 1)`, it is a nonzero polynomial in `(q₁, q₂) ∈ K² × K²`. Consequently, in
> orbit (i), **`(P₁) ⟹ (P₂)` for every `ρ`, at every `r`**. This contains (MC-26)'s first link and
> (MC-46)'s conclusion in orbit (i), and it describes no bad set `B₂(r)`.

*Proof.* *The frame.* In orbit (i) the lines `m` and `n = p_a p_b` are skew ((MC-169)'s proof).
Take a second point `y′ ∈ m`, `y′ ≠ y`. Then `e₀ := p_a`, `e₁ := y`, `e₂ := y′`, `e₃ := p_b` is a
basis of `K⁴`, with `π̂_a = ⟨e₀, e₁, e₂⟩` and `π̂_b = ⟨e₁, e₂, e₃⟩`. The six `e_{ij} := e_i ∧ e_j`,
`i < j`, are a basis of `Λ²K⁴`, and `Λ₁(y) = ⟨e₀₁, e₁₃⟩`.

*Two curve families*, the degenerations of (MC-26)'s link from each end. Fix `σ ≠ 1`.
- (α) `x₁(t) = y + t·u` with `u ∈ π̂_a`, and `x₂ = (1 − σ)y + σp_b`. Then
  `x₁∧x₂ = σ·y∧p_b + t·u∧x₂` and `x₂∧p_b = (1 − σ)·y∧p_b`, so
  `x₁∧x₂ − (σ/(1 − σ))·x₂∧p_b = t·u∧x₂`.
- (β) `x₁ = (1 − σ)y + σp_a` and `x₂(t) = y + t·w` with `w ∈ π̂_b`. Symmetrically,
  `x₁∧x₂ − (σ/(1 − σ))·p_a∧x₁ = t·x₁∧w`.

For all but finitely many `t` each `x(t)` is a placement with distinct consecutive points. Put
`c := u∧x₂` in (α) and `c := x₁∧w` in (β). For `t ≠ 0` the three rows `p_a∧x₁(t)`, `c`,
`x₂(t)∧p_b` come from the three hinge lines by an invertible triangular change, so they span
`Λ₂(x(t))`. At `t = 0` they are `p_a∧y`, `c`, `y∧p_b` up to nonzero scalars.
So `c` is the curve's **limit direction**, and the rows are polynomial in `t`.

*The limit directions span.* Take `σ₀ ∉ {0, 1}`, which exists since `K` is infinite. The four
curves below have these limit directions:
- (α), `u = y′`, `σ = 0`: `−e₁₂`;
- (α), `u = p_a`, `σ = σ₀`: `(1 − σ₀)e₀₁ + σ₀e₀₃`;
- (α), `u = y′`, `σ = σ₀`: `(σ₀ − 1)e₁₂ + σ₀e₂₃`;
- (β), `w = y′`, `σ = σ₀`: `(1 − σ₀)e₁₂ + σ₀e₀₂`.

Modulo `Λ₁(y)` they span `⟨e₀₂, e₀₃, e₁₂, e₂₃⟩`, which is all of `Λ²K⁴ / Λ₁(y)`.

*Conclusion.* Put `W := ρ + Λ₁(y)`. If `s ≤ 5`, then `W` is a proper subspace containing
`Λ₁(y)`, so one of the four limit directions `c` lies outside `W`. If `s = 6`, take any of the
four.
- Let `M(t)` have as rows a basis of `ρ` and the curve's three rows. Its entries are polynomial in
  `t`, and `rank M(0) = dim(W + ⟨c⟩) = min(s + 1, 6)`.
- A nonzero minor of that size at `t = 0` is a univariate polynomial nonzero at `0`. So it is
  nonzero at all but finitely many `t`. Pick such a `t ≠ 0, −1` at which `x(t)` is a placement. There
  `dim(ρ + Λ₂(x(t))) ≥ min(s + 1, 6)`.
- That rank bound is the nonvanishing of a minor of `[ρ; p_a∧x₁; x₁∧x₂; x₂∧p_b]`. The minor is
  polynomial in the placement coordinates, and it is nonzero at `x(t)`.
- For the affine charts (`π_a = {z = h_a}` and `π_b = {z = h_b}` non-vertical, as at a pencil
  configuration). Each row of the minor has degree `0` or `1` in `x₁` and in `x₂`, so the minor is
  bihomogeneous in `(x₁, x₂)`. Write `x₁ = (X, Y, αX + βY + γW, W)` for `h_a = αx + βy + γ`, and
  likewise `x₂`. Setting `W = 1` in both factors keeps distinct monomials distinct, so the minor,
  read at `x₁ = (q₁, h_a(q₁), 1)` and `x₂ = (q₂, h_b(q₂), 1)`, is a nonzero polynomial in
  `(q₁, q₂)`. When `y` is affine, as in (MC-176), the curves give a chart point directly: take `y`,
  `y′`, `p_a`, `p_b` affine; every curve point has last coordinate `1` or `1 + t`, and rescaling a
  point changes no hinge line. *(Repaired at the second reading, 2026-09-26: the bullet took `y`
  affine, which fails when `h_a − h_b` is a nonzero constant, orbit (i) with `m` at infinity. The
  statement is unchanged.)* ∎

*The consequence for `(P_k)`.* In orbit (i), `λ₁ = 2` at every `y ∈ m` (MC-169), and `λ₂ = 3`
generically (MC-19)(b). `(P₁)` says `dim(ρ ∩ Λ₁(y)) = max(0, r − 4)` at a generic `y`, that is,
`s = min(r + 2, 6)`. Then, at a generic `x`, `dim(ρ ∩ Λ₂) = r + 3 − dim(ρ + Λ₂) ≤ max(0, r − 3)`,
which is `(P₂)`. ∎

Orbit (ii) is not covered, and it never reaches the cell on the route. There `p_b ∈ m`, and the
limit directions of both families, over every `u ∈ π̂_a`, `w ∈ π̂_b` and `σ`, span with `Λ₁(y)`
only a hyperplane of `Λ²K⁴` (`orbitlink.py --link` asserts rank 5 at every frame).
`[MEASURED orbitlink.py --link]` Seeded, 1 500 trials per orbit, frames with integer entries in `−9..9`. `ρ` has `r ∈ 1..4` and is drawn inside a random
`W ⊇ Λ₁(y)`, half the time one spanned by limit directions, and `s = 2..6` all occur. *(Sampler
support named at the second reading, 2026-09-26.)*
- In orbit (i), the proof's curve reaches the bound at an exhibited `t` in every trial. Each
  exhibited `t` is a certificate for its `ρ`.
- In orbit (ii), the best of three random placements reached the bound at 1 500/1 500. That is a
  lower bound, and nothing is claimed there.

> **(MC-174)** `[PROVED]` *(the 1-ear incidence, parametrized: (MC-18)(b)'s "irreducible and
> dominates" without divisibility or irreducibility; found by formalization, ORBIT recon
> 2026-09-26; second-read 2026-09-26)* Let `K` be infinite, let `L` be a finite-dimensional
> `K`-space, and let `D : L → Aff(K²)` be linear of rank `≥ 2`; write `D(z)(q)` for the value of
> `D(z)` at `q ∈ K²`. Let `A` be a polynomial function on `L` that is nonzero somewhere, and `B` a
> nonzero polynomial on `K²`. Then there are `z ∈ L` and `q ∈ K²` with **`D(z)(q) = 0`,
> `A(z) ≠ 0` and `B(q) ≠ 0`**. At `X₀(G′)`, take `L = L_{G′}(q′)` and `D(z) = h_a − h_b`, so that
> `rank D = dim U`. Then `{(z′, q_x) : D(z′)(q_x) = 0}` is `L_{G′+ear₁}` over the pictures `q_x`
> ((MC-18)(b)). With `A` the open conditions on `z′` and `B` those on `q_x`, the incidence has a
> point over the generic point of each factor. This is the dominance that (MC-54) (at `k = 1`) and
> (MC-176) consume, one in each direction.

*Proof.*
- The constants form a line in `Aff(K²) ≅ K³`. So rank `≥ 2` gives a nonzero linear form `ℓ` on
  `L`: the `X`- or the `Y`-coefficient of `D(z)`. Two nonempty Zariski-open subsets of `L` meet,
  so pick `z₀` with `A(z₀) ≠ 0` and `ℓ(z₀) ≠ 0`. Then `D(z₀)` is nonconstant, and its zero set
  `ℓ₀` is a line.
- Rank `≥ 2` also gives `u ∈ L` with `D(u) ∉ K·D(z₀)`. An affine function that vanishes on the
  zero line of a nonconstant `f` is a multiple of `f`, so `D(u)` does not vanish on all of `ℓ₀`.
  Pick `q₀ ∈ ℓ₀` with `D(u)(q₀) ≠ 0`.
- For `(q, w) ∈ K² × L` put `Z(q, w) := D(u)(q)·w − D(w)(q)·u ∈ L`. It is polynomial in `(q, w)`,
  and `D(Z(q, w))(q) = D(u)(q)·D(w)(q) − D(w)(q)·D(u)(q) = 0`.
- `F(q, w) := A(Z(q, w))` is polynomial, and `F(q₀, w₀) = A(z₀) ≠ 0` at `w₀ := z₀ / D(u)(q₀)`,
  because `D(z₀)(q₀) = 0` gives `Z(q₀, w₀) = z₀`. So `F` and `B`, read on `K² × L`, are each
  nonzero somewhere, and they have a common non-root `(q, w)`. Take `z := Z(q, w)`. ∎

> **(MC-175)** `[PROVED]` *(three partition inequalities; any finite graph; found by
> formalization, ORBIT recon 2026-09-26; second-read 2026-09-26)* Let `G′` be a graph with
> `a ≠ b` in `V(G′)`, let `x₁, x₂ ∉ V(G′)`, and put `G₁ := G′ + (a − x₁ − b)` and
> `G := G′ + (a − x₁ − x₂ − b)`.
> **(i)** `[PROVED]` `def₃(G) ≥ def₃(G₁)`.
> **(ii)** `[PROVED]` `def₃(G) ≥ def₃(G′) − 3`.
> **(iii)** `[PROVED]` If `a ≁ b` in `G′`, then `def₂(G′ + ab) ≤ def₂(G′) − min(δ₂, 2)`, where
> `δ₂ := def₂(G′) − def₂(G′/ab)` and `def₂(G′/ab)` maximizes over partitions with `a`, `b` in one
> part. So `δ₂ ≥ 2` gives `def₂(G′ + ab) ≤ def₂(G′) − 2`.

*Proof.* Write `val_D(P) = D(|P| − 1) − (D − 1)d(P)`, with `D = 6` for `def₃` and `D = 3` for
`def₂`.
- (i) Extend a partition of `V(G₁)` by putting `x₂` in `x₁`'s part. The number of parts is
  unchanged, `x₁x₂` is internal, and `x₂b` crosses exactly when `x₁b` did. So the value is
  unchanged.
- (ii) Extend a partition of `V(G′)` by the singletons `{x₁}` and `{x₂}`. That adds two parts and
  three crossing edges, so the value changes by `2·6 − 3·5 = −3`.
- (iii) A partition separating `a` and `b` has `val_{G′+ab} = val_{G′} − 2 ≤ def₂(G′) − 2`. A
  partition that does not separate them has `val_{G′+ab} = val_{G′} ≤ def₂(G′/ab) = def₂(G′) − δ₂`.
  ∎

(iii) is the `≤` half of (MC-48)(ii)'s partition count, with `δ₂ ≥ 2` as its hypothesis in place
of (MC-48)'s (c). That half is all (MC-48)(ii)'s argument uses, and it is what (MC-79)(v)
re-derives.

> **(MC-178)** `[PROVED]` *((MC-175)(iii) with equality; any finite graph; written at the second
> reading, 2026-09-26, and so one writer's; not consumed on (MC-89)'s route, which uses only
> (MC-175)(iii)'s `≤`)* Let `G′` be a finite graph with `a ≠ b` in `V(G′)` and `a ≁ b`, and let
> `δ₂ := def₂(G′) − def₂(G′/ab)` as in (MC-175)(iii). Then
> **`def₂(G′ + ab) = def₂(G′) − min(δ₂, 2)`**. This is the equality (MC-79)(v) writes, and the
> count `max(f₂^sep − 2, g₂)` of (MC-48)(ii).

*Proof.* Let `f_sep` be the maximum of `val₃` over the partitions of `V(G′)` that separate `a` and
`b` (the singletons do, since `a ≠ b`), and put `g := def₂(G′/ab)`. Then
`def₂(G′) = max(f_sep, g)`. By (MC-175)(iii)'s proof, adding `ab` lowers a separating partition's
value by exactly `2` and leaves a non-separating one unchanged, so
`def₂(G′ + ab) = max(f_sep − 2, g)`.
- If `f_sep ≥ g`, then `def₂(G′) = f_sep` and `δ₂ = f_sep − g`, so
  `max(f_sep − 2, g) = def₂(G′) − min(2, δ₂)`.
- If `f_sep < g`, then `def₂(G′) = g` and `δ₂ = 0`, so `max(f_sep − 2, g) = g = def₂(G′) − 0`. ∎

> **(MC-176)** `[PROVED]` *(the `k = 2` open-ear step at `a ≁ b`, `δ₂ ≥ 2`, through the
> antecedent; replaces (MC-46) and (MC-138) on (MC-89)'s route; Jackson–Jordán at `G′ + ab` is
> (MC-172), a theorem over every infinite field; found by formalization, ORBIT recon 2026-09-26;
> second-read 2026-09-26)* Let `K` be infinite. Let `G = G′ + ear₂` be an open ear
> `a − x₁ − x₂ − b` with `G′` satisfying (H), `a ≁ b` in `G′`, and `δ₂ ≥ 2`. Put
> `G₁ := G′ + (a − x₁ − b)`, that is, `G` with `x₂` split off. **If `X₀(G′)` and `X₀(G₁)` attain,
> then `X₀(G)` attains.** Under the strong induction both hypotheses hold: both graphs satisfy (H)
> and are smaller than `G` ((MC-55)(i)).

*Proof.* **Step 1: flag genericity** ((MC-48)(ii)'s argument, under `δ₂ ≥ 2`). `G′ + ab` is
simple, with `|N[v]| ≥ 3` at every vertex.
- Take `q` admissible for `G′` and generic for (MC-172) at `G′ + ab`, so that
  `dim L_{G′+ab}(q) = 3 + def₂(G′ + ab)`. By (MC-175)(iii) and (MC-4)(b) at `G′`,
  `dim L_{G′+ab}(q) ≤ 1 + def₂(G′) ≤ dim L_{G′}(q) − 2`.
- The planes are fixed by `N_{G′}[·]`, so the new edge asks only `p_b ∈ π_a` and `p_a ∈ π_b`.
  Hence `L_{G′+ab}(q) = L_{G′}(q) ∩ ker φ₁ ∩ ker φ₂`, and so `φ₁`, `φ₂` are linearly independent
  on `L_{G′}(q)`.
- Both factor through `D(z) := h_a − h_b`: `φ₁ = −D(z)(q_b)` and `φ₂ = D(z)(q_a)`. So
  `rank D = dim U ≥ 2`, and off the proper Zariski-closed set `{φ₁φ₂ = 0}` the flag pair is in
  orbit (i).

**Step 2: a common point.** Fix `q` on `V(G′)` as in Step 1, and also generic for `X₀(G′)`, so
that the attaining heights contain a nonempty Zariski-open `O′ ⊆ L_{G′}(q)`. Make the extensions
of `q` at `x₁` (generic for `X₀(G₁)`) and at `x₁`, `x₂` (main pictures of `G`) contain the
nonzero locus of a nonzero polynomial in the new coordinates. Each requirement is a nonzero
polynomial condition on `q`'s coordinates. Apply (MC-174) with:
- `A := φ₁·φ₂·A′`, where `A′` cuts out `O′`; `A` is nonzero somewhere on `L_{G′}(q)`;
- `B(q_x) :=` the `G₁`-genericity polynomial, whose non-roots are admissible for `G₁`, so that
  `q_x ≠ q_a, q_b`.

This gives `(z′, q_x)` with `D(z′)(q_x) = 0`. By (MC-18)(b)'s identification,
`L_{G₁}(q, q_x) ≅ {z ∈ L_{G′}(q) : D(z)(q_x) = 0}` via `z_{x₁} = h_a(q_x)`. This vector space
contains `z′`, where `A ≠ 0`, and it contains a nonempty Zariski-open set of heights at which
`G₁` attains. Two such sets meet, so replace `z′` by a common point. Now `G′` attains at `z′`,
`G₁` attains at `(z′, h_a(q_x))`, the flag pair is in orbit (i), and `y := (q_x, h_a(q_x), 1)`
lies on `m`.

**Step 3: the count at `G₁`.** In rank form, (MC-16) reads
`rank R_{G′+ear_k} = rank R_{G′} + 5k − 1 + dim(ρ + Λ_k)` at every configuration with adjacent
points distinct. The reason is that `dim M_G = dim M_{G′} + (k + 1) − dim(ρ + Λ)`, because
`−r + dim(ρ ∩ Λ) − λ = −dim(ρ + Λ)`. This is the vertex-2-cut gluing at `{a, b}` (Phase 39's
Layer B6): the path side has rank `5(k + 1)` and relative screws `Λ_k`. At `k = 1` it gives
`rank R_{G₁} = rank R_{G′} + 4 + s`, with `s := dim(ρ + Λ₁(y))`. *(Stated once with its proof as
(MC-177), below; second reading, 2026-09-26.)*

**Step 4: the placement.** Apply (MC-173) at `(z′, y)`, with `x₁ = (q_{x₁}, h_a(q_{x₁}), 1)` and
`x₂ = (q_{x₂}, h_b(q_{x₂}), 1)` ((MC-18)(a)). The pictures `(q_{x₁}, q_{x₂})` with
`dim(ρ + Λ₂(x)) ≥ min(s + 1, 6)` contain the nonzero locus of a nonzero polynomial. Intersect it
with the main pictures of `G` over `q`. At such a point the heights
`(z′, h_a(q_{x₁}), h_b(q_{x₂}))` lie in `L_G`, and (MC-16) at `k = 2` gives
`rank R_G = rank R_{G′} + 9 + dim(ρ + Λ₂(x)) ≥ min(rank R_{G₁} + 6, rank R_{G′} + 15)`.

**Step 5: the target.** `G′` and `G₁` attain at the point, so
`rank R_{G′} = 6(|V′| − 1) − def₃(G′)` and `rank R_{G₁} = 6|V′| − def₃(G₁)`. With (MC-175)(i)
and (ii),
`rank R_G ≥ min(6(|V′| + 1) − def₃(G₁), 6(|V′| + 1) + 3 − def₃(G′)) ≥ 6(|V′| + 1) − def₃(G)`,
which is `G`'s target, since `|V(G)| = |V′| + 2`. One attaining point over a main picture forces
the generic one ((MC-2)'s semicontinuity). ∎

What (MC-176) does not use: `δ`, (MC-17), (MC-22)'s split into `(R_k)` and `(P_k)`, (MC-26),
(MC-44), (MC-46) and (MC-138). The antecedent `G₁` supplies both of (MC-22)'s conditions at once,
through `s`. By (MC-17), `s = 2 + min(δ, 4)` at the common point, and attainment of `G′` there is
used only when `s = 6`, which happens exactly when `δ ≥ 4`. `K` enters only as an infinite field:
nonzero scalars are inverted, a nonzero univariate polynomial has finitely many roots, and nonzero
polynomials have a common non-root. The one citation is (MC-172). So (MC-166)'s audit extends to
(MC-173)–(MC-176) unchanged. The formalization interface is in `notes/Phase40-design.md` §3 STEPS
(ORBIT).

`[MEASURED orbitlink.py --e2e]` Exact over ℚ, at 30 chains of subdivided `K₄`: the witness's six
below, then 24 more in the driver's order (a cap). The `(δ, r, s)` profile is `(1, 1, 3)` ×11,
`(2, 2, 4)` ×9, `(3, 3, 5)` ×9 and `(4, 4, 6)` ×1. At each chain:
- `G′`, `G₁` and `G` attain over pictures certified main (`dim L = 3 + def₂`);
- the flag pair is in orbit (i), and `s = 2 + min(δ, 4)`;
- (MC-16)'s rank identity holds at `G₁` and at `G`;
- the curve of (MC-173)'s proof reaches `G`'s target.

These are certificates at those instances, not coverage.

`[CONSTRUCTED orbitlink.py --witness]` *(the cell is forced)* `K₄` with every edge subdivided
twice (16 vertices, 18 edges) is in 𝒮, with `def₂ = 9 > def₃ = 0`. It is rigid, it has no
(MC-80) core, and each of its six chains has `k = 2`, `a ≁ b` and `δ = δ₂ = 3`. So in (MC-89)'s
step list its only covering step is this cell:
- it is 2-connected, not a cycle or a θ-graph, and not FLAT;
- it has no `def₂`-rigid subgraph, by (S) and (MC-76);
- it has no core for (MC-71);
- it has no chain with `k ≠ 2` or with `δ = 0`.

Splitting off a chain vertex gives exactly `G₁`, the cell's own antecedent. So the cell cannot be
routed around with the planned steps.

> **(MC-177)** `[PROVED]` *(the path brick, and (MC-16) in rank form; any field; written at the
> second reading, 2026-09-26, and so one writer's)* Let `P = a − x₁ − ⋯ − x_k − b`, `k ≥ 0`, be a
> path of bodies with `a ≠ b`, and put `x₀ := a`, `x_{k+1} := b`. Let its `k + 1` hinges have
> nonzero extensors `C₀, …, C_k`, with `C_i` joining `x_i` and `x_{i+1}`. Then:
> **(i)** `[PROVED]` `rank R_P = 5(k + 1)`;
> **(ii)** `[PROVED]` `{X_b − X_a : X ∈ M_P} = span(C₀, …, C_k) = Λ_k`;
> **(iii)** `[PROVED]` hence, for an open ear `G = G′ + ear_k` with `a ≁ b` in `G′` and every ear hinge
> nonzero, `rank R_G = rank R_{G′} + 5k − 1 + dim(ρ + Λ_k)`, with
> `ρ = {X_b − X_a : X ∈ M_{G′}}`.
>
> (iii) is the rank form in (MC-176)'s Step 3, which the second reading confirmed. It is stated
> here once, with its proof through the vertex-2-cut gluing, for CHAIN (`notes/Phase40-design.md`
> §3 STEPS), which builds (MC-16).

*Proof.* **(i)** A hinge with nonzero extensor `C` between bodies `u ≠ v` asks `X_u − X_v ∈ ⟨C⟩`.
Its five rows are the annihilator of `⟨C⟩` read on `X_u − X_v`, and they are independent because
`X ↦ X_u − X_v` is onto at `u ≠ v`. Solving along the path, `X_a` is free, and
`X_{x_{i+1}} = X_{x_i} − ω_i C_i` with each `ω_i` free. So `dim M_P = 6 + (k + 1)`, and
`rank R_P = 6(k + 2) − (k + 7) = 5(k + 1)`.
**(ii)** At a motion, `X_b − X_a = −Σ ω_i C_i ∈ Λ_k`. Every `ω ∈ K^{k+1}` is realized, so every
element of `Λ_k` is.
**(iii)** The sides `V(G′)` and `{a, x₁, …, x_k, b}` meet exactly in `{a, b}`, and every edge of
`G` lies inside one side. Because `a ≁ b` in `G′`, the second side induces exactly `P`. The
vertex-2-cut gluing (Phase 39's Layer B6, `BodyHingeFramework.finrank_span_rigidityRows_vertexTwoCut_eq`)
gives `rank R_G = rank R_{G′} + rank R_P + dim(ρ + Λ_k) − 6`. Substitute (i) and (ii). ∎

It agrees with (MC-16), whose dimension formula gives the same identity by
`−r + dim(ρ ∩ Λ) − λ = −dim(ρ + Λ)`. The Lean instantiation (at `pointJoinFramework`, where `ρ`
and `Λ_k` are the join-model spaces as written) is recorded in `notes/Phase40-design.md` §3 STEPS
(ORBIT).

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
- *(2026-09-26)* an `orbitlink.py` assert firing: (MC-173), (MC-176) end to end, or the witness.

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
| `python3 notes/scripts/w4/orbitlink.py --link` | *(2026-09-26, seed `20260926`)* (MC-173): 1 500 trials per orbit; orbit (i) four-curve span 6 and the proof's curve certifies the bound at 1 500/1 500; orbit (ii) family span 5 (asserted), random draws printed, not claimed | 6 s |
| `python3 notes/scripts/w4/orbitlink.py --witness` | *(2026-09-26)* the subdivided-`K₄` witness: 𝒮, `def₂ = 9 > def₃ = 0`, rigid, no (MC-80) core, six chains `k = 2`, `a ≁ b`, `δ = δ₂ = 3` | 0.3 s |
| `python3 notes/scripts/w4/orbitlink.py --e2e` | *(2026-09-26, seed `20260926`)* (MC-176) end to end at 30 chains (6 witness + 24 capped): all attain over certified-main pictures; (MC-16) at `G₁`, `G` | 21 s |

