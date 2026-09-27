## §(K-main) — Step MC10 — the ear step on `X₀` (P3 Track 1)

#### Step MC10 — the ear step on `X₀` (P3 Track 1)

*Worked by a forked agent (2026-09-24) and checked by the coordinator; driver `w4/earstep.py`
(new). **Second-read 2026-09-25** by a fresh reader, together with Steps MC1–MC6: every claim
re-derived by hand, independent exact checks (`w4/mc10indep.py`), every driver re-run. Nothing on
(MC-89)'s path is refuted. (MC-25) and (MC-26) are repaired in scope (span-generic placements;
(MC-26)'s first link excludes orbit (iii)). (MC-27)'s bad set was wrong as worded (`bkwit.py`), and
(MC-27) is off the path. (MC-169) supplies the missing proof of (MC-19)(b) at `k = 1`, and (MC-170)
upgrades (MC-18)'s count to certified. The question: does the `X₀` motive, "`X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)`",
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
  lies over the proper locus `{P_a = P_b}`. (If `φ₀` is a nonzero constant, the second component is
  empty; the conclusion is the same.) ∎

Two instances of `dim U = 1`:
- `φ₀ ∝ ℓ_{ab}`: an edge or implied edge `ab`, the triangle case.
- `C₄ = a c b d` with `a, b` opposite: `P_a − P_b ∈ N_c^⊥ ∩ N_d^⊥ = K ℓ_{cd}`, and `G = K_{2,3}`.
  This is (MC-9)'s mechanism.

`[MEASURED earstep.py --rdelta 7]` `dim U = 1` occurs at 241 of the 11 573 vertex pairs of simple
2EC graphs on `≤ 7` vertices: 114 adjacent, 127 not. Each is at one draw. Every accepted draw has
`q ∈ U` (`rdreplay.py`, the second reading: 577/577 graphs). At such a `q`, `dim U(q) ≤ min(δ₂, 3)`
(`a ≁ b`) or `≤ min(δ₂, 1)` (`a ∼ b`) with no citation ((MC-62)). The drawn value equals that bound
at all 11 573 pairs, so the 241 are **certified** generic values (MC-170).

> **(MC-19)** `[PROVED]` *(chain spans; `earstep.py --chains`, 16/16 certificates; hand proof over every field: (MC-134))* **(a)** A generic
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

> **(MC-21)** `[PROVED]` *(class theorems; the first infinite families attaining on `X₀`; (b) without
> the 30 certificates: (MC-139))* **(a)**
> Every graph obtained from a cycle by successively adding closed ears and open ears with at least 5
> interior vertices attains on `X₀`. **(b)** **Every simple θ-graph `θ(p₁, p₂, p₃)` attains on
> `X₀`.**

*Proof.* `X₀(C_n)` has no hubs, so `L = K^V`, and by (MC-19)(a)
`dim M = 6 + n − min(n, 6) = 6 + def₃(C_n)`. Then (a) follows by induction with (MC-20). For (b):
if `p₃ ≥ 6`, the θ-graph is `C_{p₁+p₂}` plus an open ear with `p₃ − 1 ≥ 5` interior vertices. If
`p₃ ≤ 5`, it is one of 30 graphs, each with an exhibited attaining `X₀` point
(`earstep.py --thetas 5`, mod-`2⁶¹ − 1` rank equal to the target). ∎

This extends (MC-7)'s finite `a + b + c ≤ 16` to every θ-graph. It is characteristic-free: (MC-19)
holds over every infinite field (MC-134), and (b) needs no per-graph computation (MC-139). (Over ℚ
the landed `--thetas` points are certificates only at `q ∈ U`, which holds at 30/30, (MC-140).)
*(Repaired at the second readings of Steps MC20 and MC10, 2026-09-25.)* Nondegeneracy is not claimed:
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
> where `G′` attains and `q ∈ U` (`dim L(q) = 3 + def₂`; not asserted by the driver, but true at all
> 577 accepted draws, `rdreplay.py`), `r_draw ≤ r_generic ≤ δ`, so each observed equality **certifies** the generic
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

> **(MC-25)** `[PROVED]` *(`k = 4`: (P₄) holds for every `ρ`; `earstep.py --lamcap`; hand proof over every field: (MC-136))* The intersection
> of `Λ` over the placements of generic span (`λ = 5`) is `0` in all four orbits at `k = 4`. Hence, **under strong induction on
> `|V|`, the `k = 4` open-ear step holds**: (P₄) from this, (R₄) from (MC-24).

*Proof.* Here `λ = 5`. For `r ≥ 1`, (P₄) says that `ρ ⊄ Λ` for some placement, and that fails only
if `ρ ⊆ ⋂ Λ`. The exhibited intersection over 12 placements per orbit frame is already `0`, and all
48 of those placements have `λ = 5` (`lamguard.py --replay`). So it contains the intersection over
the dense open set of span-generic placements, which is therefore `0`. (The span guard is needed: a
deficient draw can make an intersection `0` spuriously, (MC-97). Hand proof over every field:
(MC-136).) *(Repaired at the second reading, 2026-09-25: "over all placements".)* ∎

*(2026-09-27, SHORT recon, found by formalization and second-read the same day.)* On (MC-89)'s route the
`k = 4` step is now (MC-180) (Step MC13). It counts against the antecedent `G′ + ear₃` (`G` with `x₂`
suppressed), and its placement condition is one tetrahedron. (MC-24)'s gadget, (MC-25)'s proof and
(MC-136) are off the route, and stay proved.

> **(MC-26)** `[PROVED]` *(degeneration links; the `r = 1` sentence, corrected, proved over every
> field: (MC-137)(c))* For a given `ρ`: (P₁) ⟹ (P₂) at `r ≥ 4` in orbits (i), (ii), (iv) (where
> `λ₁ = 2`; in (iii) the degenerate 1-ear spans only `⟨m⟩` and the argument gives nothing; *scope
> added at the second reading, 2026-09-25*), and
> (P₂) ⟹ (P₃) at `r ≥ 3`. (P_k) holds at `r = 1` for every `k ≤ 4`, except in the two cells where
> `⋂Λ ≠ 0`: orbit (iii) at `k = 1`, and orbit (iv) at `k = 2`.
> *Erratum (2026-09-24, found independently as (MC-97) and (MC-115)): orbit (ii) at `k = 1` is a
> third such cell (in both mirror forms, `p_b ∈ π_a` or `p_a ∈ π_b`), `⋂Λ₁ = ⟨π_a ∩ π_b⟩`, since `p_b ∈ π_a ∩ π_b` puts that line in every 1-ear span.
> `--lamcap`'s `0` there came from one span-deficient random draw, which the driver did not guard
> against. `lamguard.py`'s guarded re-run confirms every other cell, and no landed claim uses the
> orbit-(ii), `k = 1` cell.*

*Proof.* For the first implication, degenerate the 2-ear to `x₁ ∈ π_a ∩ π_b` with `x₂` on the line
`x₁ p_b ⊆ π_b`. Its line set is then a 1-ear's, so the limit of `Λ₂` contains `Λ₁` plus one
dimension. Upper semicontinuity gives `dim ρ ∩ Λ₂ ≤ max(0, r − 4) + 1`, which is the (P₂) value
iff `r ≥ 4`. The second implication is the same, with `x₂` on the line `p_a x₁`. At `r = 1`,
(P_k) means `ρ ⊄ ⋂Λ` (`--lamcap`). ∎

*(2026-09-27, SHORT recon.)* On (MC-89)'s route (MC-26)'s links were consumed only by (MC-45)'s proof
of the `k = 3` step. That step is now (MC-181) (Step MC13, second-read 2026-09-27). The links are off the
route, and stay proved.

Orbit (iv) is harmless on `X₀`. It is `P_a = P_b` at the generic point, i.e. `U = 0`. By the
argument of (MC-13), applied to `G′ + ab + x` with `x` adjacent to `a` and `b`, and assuming
Jackson–Jordán, `a` and `b` then lie in a common `def₂`-rigid subgraph. That subgraph is also
`def₃`-rigid, so `δ = 0` and `r = 0`.
*Repair (2026-09-24, the second reader of Step MC16):* read literally, (MC-13)(c) at `G′ + ab` gives
a common `def₂`-rigid subgraph of `G′ + ab`, not of `G′`. That does not give `δ = 0`: take
`G′ = C₇` with `a, b` at distance 2, where the triangle `acb` is rigid in `C₇ + ab` but `δ₂ = 2` and
`δ = 1`. The conclusion stands by another route: (MC-62)'s count, `dim U ≥ min(δ₂, 3)` for `a ≁ b`
(JJ at `G′ + ab + x`) and `dim U ≥ min(δ₂, 1)` for `a ∼ b` (JJ at `G′ + x`), gives
`U = 0 ⟹ δ₂ = 0`. Then `δ = 0` by (MC-88), and `r = 0` by (MC-16)'s `r ≤ δ`. *(Both adjacency cases
and the (MC-88) step added at the second reading, 2026-09-25.)*

> **(MC-27)** `[OPEN]` *(the open ear steps, `k = 1, 2, 3`)* At `X₀(G′)`'s generic point, `ρ` avoids
> the placement bad set `B_k(r) = {ρ : dim(ρ ∩ Λ) > max(0, r + k − 5) at every placement of generic
> span λ = k + 1}` (equivalently, at the generic placement: `(P_k)` fails).
> *(2026-09-25, the second reading: "at every placement" alone is wrong. At orbit (iv), `k = 2`,
> `ρ = ⟨ℓ⟩` with `ℓ ⊂ π`, `(P₂)` fails, yet the valid placement with `x₂ ∈ p_a x₁` has `λ = 2` and
> `ℓ ∉ Λ` (`bkwit.py`). (MC-43), (MC-46) and (MC-47) already use the generic reading.)*
> **The universal form is false.** `Λ` always contains the line `p_a x₁`, which lies in the pencil
> `Pen(p_a, π_a)`. So every `ρ ⊇ Pen(p_a, π_a)` is bad when `r ≤ 5 − k`, and likewise for
> `Pen(p_b, π_b)`. Whether such `ρ` occur on `X₀` is open. They do not occur at any `(G′, a, b, k)`
> with `|V(G′)| + k ≤ 8` where (MC-22) applies (dominance, `λ = k + 1`, and `X₀(G′)` and `X₀(G)` both
> attaining: (MC-7) for 2EC graphs, (MC-52)/(MC-53) otherwise), since (MC-22)'s "⟹" then forces
> (R_k) and (P_k). *(Scope repaired at the second reading: `exh8` holds only 2EC graphs.)*
> *`k = 1` in orbit (i), an exact criterion* `[PROVED]`. Put `m := π_a ∩ π_b` and `n := p_a p_b`,
> which are skew. Then `Λ(x) = x ⊗ n̂` inside `W₄ := m̂ ⊗ n̂`, the lines meeting both `m` and `n`. Put
> `ρ₄ := ρ ∩ W₄`. The 2-planes of `m̂ ⊗ n̂` meeting every `x ⊗ n̂` are exactly the `m̂ ⊗ y₀`. So (P₁)
> fails iff either `r ≤ 4` and (`dim ρ₄ ≥ 3`, or `ρ ⊇ m̂ ⊗ y₀` for some `y₀ ∈ n`), or `r = 5` and
> `ρ ⊇ W₄`.
> **Stop rule fired** (W4-reopen): the remaining cells split by `k` × orbit × `r`.
> *(2026-09-24: answered in part by Step MC13, (MC-43)–(MC-50); the cells that remain are
> (MC-51).)*

**Added at the second reading (2026-09-25).**

> **(MC-169)** `[PROVED]` *((MC-19)(b) at `k = 1`, by hand, over any field; agrees with (MC-134)(b))*
> Let `x ∈ m = π_a ∩ π_b` (in orbit (iv), `x ∈ π`), `x ≠ p_a, p_b`. Then `Λ₁(x) = span(p_a ∧ x, x ∧ p_b)`,
> and `λ = 2` unless `x ∈ n = p_a p_b`. So `λ = 2` at every valid placement in orbits (i) and (ii),
> `λ = 2` at `x ∉ n` in (iv), and `λ = 1` at every placement in (iii).

*Proof.* Two distinct lines have non-proportional Plücker vectors, so `λ = 2` unless the lines
`p_a x` and `x p_b` coincide, i.e. unless `x ∈ n`.
- Orbit (i): `n ∩ m = ∅`, since a common point `c` would put the line `p_a c` in `π_a`, and then
  `p_b ∈ π_a`.
- Orbit (ii): `n ∩ m` is the single point `p_b` (resp. `p_a`).
- Orbit (iii): `n = m`.
- Orbit (iv): `n` is a proper line of `π`. ∎

> **(MC-170)** `[CONSTRUCTED]` *(`earstep.py --rdelta 7`'s own draws, replayed by `rdreplay.py` and
> `dUreplay.py`)* On every vertex pair of every simple 2EC graph on 3–7 vertices (11 573 pairs), the
> generic `dim U` is exactly (MC-62)'s no-citation bound: `min(δ₂, 3)` for `a ≁ b` and `min(δ₂, 1)` for
> `a ∼ b`. This is a finite theorem, with no Jackson–Jordán.
> - The driver's accepted draw has `q ∈ U` at 577/577 graphs.
> - At such a draw `dim U(q) ≤ dim U_generic` (lower semicontinuity on the bundle), and
>   `dim U ≤ dim F − dim F_weld ≤ δ₂`.
> - The drawn value meets the bound at every pair. The histogram of (adjacent, `dim U`, bound) is
>   (F,0,0) 4 479; (F,1,1) 127; (F,2,2) 80; (F,3,3) 10; (T,0,0) 6 763; (T,1,1) 114.
>
> `PYTHONHASHSEED=0 python3 notes/scripts/w4/rdreplay.py 7` (~6 s); `… dUreplay.py 7` (~7 s).

`[CONSTRUCTED]` *(`mc10indep.py`; stdlib only, exact, string seeds, no code shared with the other
drivers)* `python3 notes/scripts/w4/mc10indep.py all` (~35 s, exit 0) re-checks (MC-3)'s Plücker
split, (MC-4)(a)–(b) and (MC-5)(i) at 474 `(G, q)` pairs (2 at jump strata), (MC-6)'s form at 30
`(G, q, z)`, (MC-16)'s dimension formula at 80 configurations (9 span-deficient), (MC-17)'s count at
606 random ears, (MC-18) at 159 draws, (MC-19)'s spans in every orbit, the guarded intersections, and
(MC-26)'s links and (MC-27)'s criterion at structured `ρ`. There are 0 failures; the populations and
caps are in its docstring. `python3 notes/scripts/w4/bkwit.py` (< 1 s) is the (MC-27) witness.

**What an ear-only induction on `X₀` still lacks** *(as updated by Step MC13)*.
*(Superseded 2026-09-24/25: (MC-89) is a coverage theorem modulo Jackson–Jordán that uses no open ear
cell. CONTRACT needs no per-graph certificate at additive cores ((MC-71)). Of (MC-51)'s cells, Steps
MC16–MC18 close all but (MC-117), which Step MC21 narrows to Case II-cyclic (MC-154). The bullets
below are the 2026-09-24 Step-MC13 state.)*
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

