## §(K-main) — Step MC17 — relative deficiency, the triangle gadget for `a ∼ b`, and most of the ear cells (modulo Jackson–Jordán)

#### Step MC17 — relative deficiency, the triangle gadget for `a ∼ b`, and most of the ear cells (modulo Jackson–Jordán)

*Worked 2026-09-24 by a read-only agent (the third 2026-09-24 session's Track F), commissioned on
the lemma "`δ₂ = 1 ⟹ δ ≤ 1`" and then refocused on the cell (a′). The coordinator checked (MC-90),
(MC-91)(a), (MC-94) and (MC-97) at the level of the written proofs. **Second-read 2026-09-25 for
(MC-105) only** (by Step MC21's reader): (MC-85), (MC-90), (MC-91)(a), (c), (MC-92)(iii), (MC-94),
(MC-95)(ii), (iii) and (MC-105) were re-derived and confirmed. The rest of the step, with Step MC18,
was second-read the same day by another reader: nothing refuted, and the repairs are to hypotheses,
tags and wording, each marked. None of
it is on (MC-89)'s critical path. It closes ear cells that the coverage theorem routes around, and so
feeds the EAR-only route of Step MC18. Drivers `w4/deltapairs.py`, `w4/splitcells.py`,
`w4/splitdu.py`, `w4/lamguard.py`, `w4/cellwit.py`, `w4/aprime.py` (new).*

**Verdict.**
- **Relative deficiency is a minimum over induced subgraphs** (MC-90):
  `δ_D = min{def_D(G′[Y]) : a, b ∈ Y}`, for any graph and `D`. Hence **`δ₂ ≤ 2 ⟹ δ ≤ δ₂`** (MC-91),
  which is sharper than (MC-88) and proved independently of it (MC-107). `δ ≥ 3` forces `δ₂ = 3`. All
  13 admissible pairs `(δ, δ₂)` occur. This explains Step MC11's "`δ ≤ 1` at `dim U = 1`". Four of that
  histogram's 1 017 instances are pictures that jump for `G′` ((MC-91)(d)).
- **(MC-51)(a) for `a ≁ b`** needs only `U ≠ 0`, with Jackson–Jordán at `G′ + ab + x` alone (MC-93).
- **For `a ∼ b` the triangle is the chord gadget** (MC-94). `X₀(G′ + x)` attaining gives `r = δ`, and
  the `k = 2`, `a ∼ b` cell closes (MC-95), which **closes Step MC16's cell (a′)** (MC-105): the hinge
  `ab` is never locked under the strong induction.
- **Erratum to (MC-26)** (MC-97). In orbit (ii) at `k = 1`, `⋂Λ₁ = ⟨m⟩`, not `0`. `earstep.py --lamcap`
  intersected spans over random placements without guarding against span-deficient draws.
  `lamguard.py`'s guarded re-run confirms every other cell. No landed claim uses the orbit-(ii),
  `k = 1` cell.
- **Cell (MC-51)(c)** closes at `δ = 1` (MC-100), at `(δ, δ₂) = (2, 2)` (MC-101), and at `δ = 2` with a
  path of `def₃`-classes (MC-102). Step MC18 closes the rest of `δ ≤ 2`.

**Notation.** `val_D(𝒫) := D(|𝒫| − 1) − (D − 1)d(𝒫)`, `def_D := max val_D`. So `def₂ = def_{D=3}` and
`def₃ = def_{D=6}`. For a pair `a ≠ b` of `G′`: `f_D := def_D(G′)`, and `g_D` is the maximum over partitions
with `a, b` in one part (`def_D(G′/ab)`). `δ_D := f_D − g_D`, so `δ₂ = δ_{3}` and `δ = δ_{6}`. `G′[Y]` is the
induced subgraph. `U`, `ρ`, `r`, `Λ_k`, the orbits (i)–(iv), `m := π_a ∩ π_b` and `n := p_a p_b` are as in
Step MC10 and (MC-27). The **strong induction hypothesis (IH)** at `G` is: `X₀(H)` attains for every `H`
satisfying (H) with `|V(H)| < |V(G)|`.

**Part I — `δ` against `δ₂`.**

> **(MC-90)** `[PROVED]` *(relative deficiency is the least deficiency through both terminals)* Let `G′` be
> any finite (multi)graph, `a ≠ b` vertices, `D ≥ 1`. Then
>
>   `δ_D = min { def_D(G′[Y]) : a, b ∈ Y ⊆ V(G′) }`.
>
> In particular `δ₂ = min_Y def₂(G′[Y])` and `δ = min_Y def₃(G′[Y])`.

*Proof.* **`≤` (merge).** Fix `Y ∋ a, b` and a `def_D`-optimal partition `𝒬` of `G′`. Let `t` parts of `𝒬`
meet `Y`, and merge them into one part, getting `𝒬′`, which has `a ∼ b`. Let `μ` be the number of edges
between two distinct merged parts. Then `val_D(𝒬′) = val_D(𝒬) − D(t − 1) + (D − 1)μ`. Every edge of
`G′[Y]` crossing `𝒬|_Y` joins two distinct parts that meet `Y`, so `μ ≥ d_{G′[Y]}(𝒬|_Y)`, and `𝒬|_Y` has
`t` parts. Hence `val_D(𝒬′) ≥ f_D − val_D^{G′[Y]}(𝒬|_Y) ≥ f_D − def_D(G′[Y])`. So
`g_D ≥ f_D − def_D(G′[Y])`. (This is (MC-13)(b)'s merge, done at `Y`.)
**`≥` (refine).** Let `𝒫` attain `g_D` with `a, b` in its part `Y`. Refine `Y` by any partition `ℛ` of `Y`.
The result has `|𝒫| + |ℛ| − 1` parts and `d(𝒫) + d_{G′[Y]}(ℛ)` crossing edges, so its value is
`g_D + val_D^{G′[Y]}(ℛ)`. That value is at most `f_D`, so `val_D^{G′[Y]}(ℛ) ≤ δ_D`. Maximising over `ℛ`:
`def_D(G′[Y]) ≤ δ_D`. ∎

*Remarks.*
- The matroid reading gives `≤` too. `δ_D = r(M ∪ D·ab) − r(M)`, where `M` is `(D − 1)` copies of each
  edge in the union of `D` graphic matroids and `D·ab` is `D` parallel copies of `ab`. It is
  non-increasing in the edge set by submodularity.
- For `D = 3`, contracting the `def₂`-classes turns (MC-90) into (MC-63)(a)'s formula
  `δ₂ = min_{X ∋ A,B} loss(X)`. The same holds for `D = 6` with the `def₃`-classes (used in (MC-102)).
- `Y = {a, b}` gives `δ_D ≤ D` for `a ≁ b`, and `δ_D ≤ 1` for `a ∼ b`.

> **(MC-91)** `[PROVED]` *(the sharp relation)*
> **(a)** Let `D ≤ D′`. If `δ_D ≤ D − 1`, then `δ_{D′} ≤ δ_D`. In particular **`δ₂ ≤ 2 ⟹ δ ≤ δ₂`**
> (so `δ₂ = 1 ⟹ δ ≤ 1` and `δ₂ = 0 ⟹ δ = 0`), and **`δ ≥ 3 ⟹ δ₂ = 3`**.
> **(b)** For `a ≁ b` in graphs satisfying (H), the pairs `(δ, δ₂)` that occur are exactly
> `{(0,0)} ∪ {(δ, δ₂) : δ₂ ∈ {1, 2}, 0 ≤ δ ≤ δ₂} ∪ {(δ, 3) : 0 ≤ δ ≤ 6}`, 13 pairs, each with a witness
> `[CONSTRUCTED]` *(`deltapairs.py --witness`)*.
> **(c)** For `a ∼ b`: `δ ≤ δ₂ ≤ 1`. `δ₂ = 0` iff `a, b` lie in a common `def₂`-rigid subgraph, and `δ = 0` iff
> they lie in a common `def₃`-rigid subgraph (equivalently, the edge `ab` does).

*Proof.* (a) Take `Y` attaining `δ_D` in (MC-90). A graph whose vertex set splits into two nonempty sides
with no edge between them has `def_D ≥ D` (the two-part partition). Since `def_D(G′[Y]) ≤ D − 1`, `G′[Y]` is
connected. On a connected graph, partition by partition,
`val_{D′} − val_D = (D′ − D)(|𝒫| − 1 − d(𝒫)) ≤ 0` (this is (MC-5)(i)). So
`δ_{D′} ≤ def_{D′}(G′[Y]) ≤ def_D(G′[Y]) = δ_D`. The last sentence is the contrapositive, with `δ₂ ≤ 3`.
(b) Everything outside the list is excluded by (a) and by `δ ≤ 6`. The witnesses, with `a ≁ b` and
`G′` satisfying (H), are:
- `(0,0)`: `K_{2,3}` at its hubs.
- `(0,1)`: `C₄`, opposite vertices.
- `(1,1)`: two triangles joined by a bridge, `a`, `b` not at the bridge.
- `(0,2)`: `C₅`, distance 2.
- `(1,2)`: a triangle, a bridge, then a `C₄`.
- `(2,2)`: three triangles chained by two bridges, `a`, `b` in the end triangles.
- `(j,3)`: `C_{6+j}` with `a`, `b` at distance `⌊(6+j)/2⌋`, for `j = 0, …, 6`.
(c) From (MC-90) with `Y = {a, b}`, which gives `def = 1` at `D = 3` and at `D = 6`, and (a). ∎

Why the hypothesis in (a) is needed: at `δ₂ = 3` the minimiser can be the disconnected `{a, b}`. For
example, `C₁₁` with `a, b` at distance 5 has `(δ, δ₂) = (5, 3)`: the `δ₂`-minimiser is `{a, b}`, while the
`δ`-minimiser is a path or the whole cycle.

> **(MC-91)(d)** `[MEASURED]` *(`deltapairs.py --exh 7 --minY --brute`, `splitcells.py --exh 8`, `splitdu.py --exh 8`; checks, not proof)*
> - (MC-90) and (MC-91) are asserted at all 11 693 pairs of all 583 graphs satisfying (H) on ≤ 7 vertices,
>   not only the 2EC ones. They agree with brute-force partition enumeration.
> - Step MC11's split-off population (4 751 instances on ≤ 8 vertices, `splitext.py`'s own
>   eligibility) has `δ₂` marginal `0 / 1 / 2 / 3` = 3 251 / 1 013 / 374 / 113.
>   - The recorded `dim U` histogram is 3 247 / 1 017 / 374 / 113.
>   - The difference is 4 instances with `δ₂ = 0` where `splitext.py` records `dim U = 1`. Replaying its
>     own pictures: its IH picture `q′` is certified for `G″ = G′ + ab` only. At those 4 it **jumps for
>     `G′`**: `dim F(G′, q′) = 4 + def₂(G′)`. They are `x8_255003425`, `x8_258896002`, `x8_261349512`,
>     `x8_266226696`.
>   - At the other 4 747, `dim U(q′) = min(δ₂, 3)` exactly, and `q′` is certified for `G′`.
> - So the histogram's "`δ ≤ 1` at `dim U = 1`" is explained at every instance. 1 013 have `δ₂ = 1`, so
>   `δ ≤ 1` by (MC-91). 4 have `δ₂ = 0`, so `δ = 0`.
> - The joint `(δ₂, δ)` counts are:
>   - `δ₂ = 0`: (0,0) 3 251;
>   - `δ₂ = 1`: (1,0) 113, (1,1) 900;
>   - `δ₂ = 2`: (2,0) 53, (2,1) 86, (2,2) 235;
>   - `δ₂ = 3`: (3,0) 1, (3,1) 13, (3,2) 15, (3,3) 53, (3,4) 16, (3,5) 7, (3,6) 8.

This does not touch (MC-30) or (MC-31). Their assertions use `c` at `q′` and the `G`-certificate
`q_x1`, not a `G′`-certificate. It is a caveat on what the histogram's `dim U` column measures.

**Part II — (MC-51)(a) for `a ≁ b`.**

> **(MC-92)** `[PROVED]` *(the `k = 2`, `r = 1` cell of (MC-26), re-derived)* In orbits (i), (ii) and (iii),
> `⋂_y Λ₂(y) = 0` over the 2-ear placements `y = (x₁ ∈ π_a, x₂ ∈ π_b)` of generic span. So at `r = 1`,
> `(P₂)` holds for every `ρ` in these orbits. In orbit (iv), `⋂Λ₂ = Λ²π` ((MC-47)(i)).

*Proof.* Suppose `ω ∈ Λ₂(y)` for `y` in a dense open set. Then `rank[Λ₂-rows(y); ω] ≤ 3` everywhere. At any
`y₀` with `dim Λ₂(y₀) = 3` this says `ω ∈ Λ₂(y₀)`. So it suffices to exhibit placements with `λ = 3`
whose spans meet in `0`. Each orbit is one `PGL₄`-orbit; take `p_a = e₀` and `p_b = e₃`, and write
`e_{ij} = e_i ∧ e_j`.
- **(i)** `π_a = ⟨e₀,e₁,e₂⟩`, `π_b = ⟨e₁,e₂,e₃⟩`.
  - `(e₁, e₂)` gives `⟨e₀₁, e₁₂, e₂₃⟩`, and `(e₂, e₁)` gives `⟨e₀₂, e₁₂, e₁₃⟩`. These meet in `⟨e₁₂⟩`.
  - `(e₀+e₁, e₂+e₃)` gives `⟨e₀₁, e₀₂+e₀₃+e₁₂+e₁₃, e₂₃⟩`, which does not contain `e₁₂`.
- **(ii)** `π_a = ⟨e₀,e₂,e₃⟩ ∋ p_b`, `π_b = ⟨e₁,e₂,e₃⟩`.
  - `(e₂, e₁)` gives `⟨e₀₂, e₁₂, e₁₃⟩`, and `(e₀+e₂, e₁)` gives `⟨e₀₂, e₀₁−e₁₂, e₁₃⟩`. These meet in
    `⟨e₀₂, e₁₃⟩`.
  - `(e₂, e₁+e₂)` gives `⟨e₀₂, e₁₂, e₁₃+e₂₃⟩`, cutting the intersection to `⟨e₀₂⟩`.
  - `(e₂+e₃, e₁)` gives `⟨e₀₂+e₀₃, e₁₂, e₁₃⟩`, which does not contain `e₀₂`.
- **(iii)** `π_a = ⟨e₀,e₁,e₃⟩`, `π_b = ⟨e₀,e₂,e₃⟩`.
  - `(e₁, e₂)` gives `⟨e₀₁, e₁₂, e₂₃⟩`, and `(e₁+e₃, e₂)` gives `⟨e₀₁+e₀₃, e₁₂, e₂₃⟩`. These meet in
    `⟨e₁₂, e₂₃⟩`.
  - `(e₁, e₀+e₂)` gives `⟨e₀₁, e₁₂, e₀₃+e₂₃⟩`, cutting the intersection to `⟨e₁₂⟩`.
  - `(e₁, e₂+e₃)` gives `⟨e₀₁, e₁₂+e₁₃, e₂₃⟩`, which does not contain `e₁₂`.

Every placement listed has `λ = 3`, asserted exactly by `lamguard.py --hand`. ∎

> **(MC-93)** `[PROVED]` *(the step)* Let `G = G′ + ear₂` be an open ear with `a ≁ b` in `G′`, and assume
> the strong induction hypothesis. If **`δ₂ ≤ 1`** and **`U ≠ 0`** at generic `q`, then `X₀(G)`
> attains. **Corollary** `[PROVED-MOD]` *((MC-33); JJ at `G′ + ab + x` only)*: **(MC-51)(a) holds for
> `a ≁ b`.** That is, the `k = 2` open-ear step holds whenever `dim U = 1`, in each of orbits (i)–(iii);
> orbit (iv) cannot occur, since `U ≠ 0`.

*Proof.*
- By (MC-91)(a), `δ ≤ δ₂ ≤ 1`.
- *`δ = 0`* is (MC-54).
- *`δ = 1`.* `G′` and `G′ + ab` satisfy (H). The second is simple because `a ≁ b`. Both have
  `|V(G)| − 2` vertices, so both attain by IH. (MC-44) gives `r ≥ min(δ, 5) = 1`, and (MC-16) gives
  `r ≤ δ`, so `r = 1`.
- *Applying (MC-22) at `k = 2`.* Its hypotheses hold: `X₀(G′)` attains; dominance holds by (MC-18)(a);
  `λ = 3` by (MC-19)(b), in every orbit, since `p_a ≠ p_b`. So `G` attains iff `(R₂)` and `(P₂)`.
  - `(R₂)`: `r = 1 ≥ min(δ, 3)`.
  - `(P₂)`: the value `max(0, r − 3)` is `0`, so `(P₂)` asks that the line `ρ` avoid the generic `Λ₂`,
    i.e. `ρ ⊄ ⋂Λ₂`.
- *`(P₂)` holds.* `π_a = π_b` iff `P_a = P_b` at `P = Ψz`. At generic `z` the difference `P_a − P_b` is a
  generic element of `U ≠ 0`, so the orbit is not (iv), and (MC-92) gives `(P₂)`.

*The corollary.* `dim U = 1` gives `U ≠ 0` outright. It also gives `δ₂ ≤ 1` by the `≥` half of (MC-62),
`dim U ≥ min(δ₂, 3)`, which uses JJ at `G′ + ab + x` and (MC-4)(b) at `G′`. That half was re-derived here. By
(MC-13)(a), `{P ∈ F(G′) : P_a = P_b} ≅ F(G′ + ab + x)`, and `def₂(G′ + ab + x) = f₂ − min(δ₂, 3)`. ∎

*What it uses, and what it avoids.*
- It needs neither the orbit rule (MC-64) nor (MC-63)(b); the second reader of Step MC15 owes both.
  Orbit (iii) needs no exclusion, since `⋂Λ₂ = 0` there too.
- The one citation is at `G′ + ab + x`, which satisfies (H) and has `|V(G)| − 1` vertices.
- *Per-graph form (no citation):*
  - `δ₂ ≤ 1` is a partition count;
  - `U ≠ 0` is an open condition, so one picture certified in `U(G′)` (`dim L = 3 + def₂(G′)`) with
    `dim U(q) ≥ 1` certifies it.
- *(MC-26)'s `k = 2`, `r = 1` claim and its `--lamcap` certificate check out.* (MC-92) re-derives the cell
  by hand, and the guarded re-run agrees (MC-97).

**Part III — `a ∼ b`.**

> **(MC-94)** `[PROVED]` *(the triangle is the chord gadget for `a ∼ b`)* Let `a ∼ b` in `G′`, which
> satisfies (H), and let `x` be a new vertex joined to `a` and `b`. If `X₀(G′)` and `X₀(G′ + x)` attain,
> then **`r = δ`** at `X₀(G′)`'s generic point, where `δ ≤ 1`. In the ear step `G = G′ + ear_k` with
> `k ≥ 2`, the graph `G′ + x` is simple, satisfies (H) and has fewer vertices than `G`. So **under IH,
> `(R_k)` holds for every `k ≥ 2` when `a ∼ b`**. For `k = 1`, `G′ + x` is `G` itself.

*Proof.*
- *The count.* The path `a − x − b` contributes `−4` to a partition separating `a, b`, and `0` otherwise.
  So `def₃(G′ + x) = max(f_sep − 4, g)`. Since `f_sep ≤ f ≤ g + 1` ((MC-91)(c)), this is `g`.
- *The triangle welds.* At any configuration with `p_x ∉ p_a p_b`, the three hinge lines of the triangle
  `p_a p_b p_x` lie in its plane and are not concurrent, so they are linearly independent. A motion of
  `G′ + x` has `X_a − X_b ∈ ⟨C_ab⟩ ∩ (⟨C_xa⟩ + ⟨C_xb⟩) = 0` and then `X_x = X_a`. So
  `M_{G′+x} ≅ M_weld(G′) := {X ∈ M_{G′} : X_a = X_b}`. This holds in every orbit.
- *The restricted point.* Let `w` be a generic point of `X₀(G′ + x)`. Its picture `(q, q_x)` is generic,
  so `q ∈ U(G′)`, `q_x ∉ q_a q_b`, and `w′ := w|_{G′} ∈ B(G′)`, since removing `x` only drops lifting
  conditions. There `dim M_weld(G′)(w′) = dim M_{G′+x}(w) = 6 + g`, by attainment.
- *Semicontinuity.* `dim M_weld` is a kernel dimension, polynomial in the point, so it is upper
  semicontinuous on the irreducible `B(G′)`. At the generic point it is therefore `≤ 6 + g`, while
  `dim M_{G′} = 6 + f`.
- *Conclusion.* `r = dim M_{G′} − dim M_weld ≥ δ`, and (MC-16) gives `≤`. This is (MC-44)'s argument,
  with the triangle in place of the chord. ∎

> **(MC-95)** *(the `k = 2`, `a ∼ b` cell)* Let `G = G′ + ear₂` with `a ∼ b`, and assume IH.
> **(i)** `[PROVED]` If `δ = 0`, `X₀(G)` attains ((MC-54)).
> **(ii)** `[PROVED]` If `δ = 1`, then **`X₀(G)` attains iff `U ≠ 0`** at generic `q`, i.e. iff the generic
> flag pair is in orbit (iii) and not (iv).
> **(iii)** `[PROVED-MOD]` *((MC-33); JJ at `G′ + x`)* At `δ = 1`, `U ≠ 0`. **Hence the cell is closed**, modulo
> JJ at `G′ + x`, a graph with `|V(G)| − 1` vertices.

*Proof.*
- **(ii)**
  - *The setup.* By (MC-94), `r = 1`. Every motion has `X_b − X_a ∈ ⟨C_ab⟩`, so `ρ = ⟨n⟩`. The edge `ab`
    puts `p_b ∈ π_a` and `p_a ∈ π_b`, so the orbit is (iii) or (iv). (MC-22) applies as in (MC-93), and
    `(R₂)` holds.
  - *Orbit (iii).* Choose `x₁ ∈ π_a ∖ n` and `x₂ ∈ π_b ∖ π_a`. Then `p_a, x₁, x₂, p_b` form a frame
    `e₀..e₃`, `Λ₂ = ⟨e₀₁, e₁₂, e₂₃⟩ ∌ e₀₃ = n`, and `(P₂)` holds, being an open condition.
  - *Orbit (iv).* `Λ₂ = Λ²π ∋ n` at every placement, so `(P₂)` fails, and by (MC-22)'s "only if" `X₀(G)`
    does not attain.
  - *The orbit.* It is (iv) iff `U = 0`.
- **(iii)**
  - `δ = 1` forces `δ₂ = 1` by (MC-91)(a).
  - For `a ∼ b`, (MC-13)(a) gives `{P ∈ F(G′) : P_a = P_b} ≅ F(G′ + x)`, and
    `def₂(G′ + x) = max(f₂^sep − 1, g₂) = f₂ − 1`.
  - (MC-4)(b) at `G′` and JJ at `G′ + x` give `dim U ≥ 1`. This is the `a ∼ b` row of (MC-62), `≥` half. ∎

*Remark.* At this cell, under IH, the `X₀` motive at `G` and the JJ-type statement "`U ≠ 0` at
`(G′, a, b)`" are equivalent. A failure of JJ at `G′ + x` of exactly this shape would make `X₀(G′ + ear₂)`
fall short.

> **(MC-96)** *(the `k = 1`, `a ∼ b` cell, and whether the structural half needs these cells)*
> **(i)** `[PROVED]` *(the `U = 0`, `δ = 1` exclusion is modulo (MC-33), JJ at `G′ + x = G`; second
> reading, 2026-09-25)* At `k = 1` with `a ∼ b` and `dim U = 1` (orbit (iii)), the ear route has no entry.
> Restriction is not dominant ((MC-18)(b)), `λ = 1` ((MC-19)(b)), and the only smaller gadget would be
> `G′ + x = G`. At `U = 0` (orbit (iv)) and `δ = 0`, (MC-54)'s proof goes through verbatim: dominance
> holds because `U = 0`, and `λ = 2`. `U = 0` with `δ = 1` is excluded modulo JJ at `G′ + x`, as in (MC-95)(iii).
> **(ii)** `[PROVED]` The structural half does not need (i). `G` contains the triangle `x a b`, which is
> `def₂`-rigid.
> - If `def₂(G) = 0`, FLAT applies (modulo JJ at `G`).
> - If `G` is not 2EC, CUT or BRIDGE applies ((MC-55)(ii)).
> - Otherwise a maximal `def₂`-rigid `W ∋ x, a, b` is proper, and `G/H` is simple by maximality (a vertex
>   with two neighbours in `W` would join it). Then CONTRACT applies with no certificate, modulo JJ at
>   `H` and `G/H` ((MC-59)(d); the second reading's corollary).
> **(iii)** `[CONSTRUCTED]` *(`deltapairs.py --akb`)* The `k = 2`, `a ∼ b` cell **does** occur in graphs with no
> `def₂`-rigid set.
> - `G = θ(1,3,4)`, i.e. `G′ = C₅` with the ear on an edge: `(δ₂, δ) = (1, 0)`.
> - `G = θ(1,3,6)`, i.e. `G′ = C₇`: `(δ₂, δ) = (1, 1)`.
> - Neither `G` has an induced subgraph with `def₂ = 0` on ≥ 2 vertices. Both are also covered by THETA.
>
> So the structural half may meet this cell outside the reach of CONTRACT, and (MC-95) is the closure it
> would use.

**Part IV — an erratum to (MC-26).**

> **(MC-97)** `[REFUTED]` *(witness: orbit (ii) at `k = 1`, by hand and by `lamguard.py`; (MC-26)'s sentence "(P_k) holds at `r = 1` for every `k ≤ 4`, except
> in the two cells where `⋂Λ ≠ 0`: orbit (iii) at `k = 1`, and orbit (iv) at `k = 2`" misses a third cell.*
> **In orbit (ii) at `k = 1`, `⋂Λ₁ = ⟨m⟩`**, with `m = π_a ∩ π_b`. So at `r = 1` in orbit (ii), `(P₁)` fails
> exactly when `ρ = ⟨m⟩`.

*Proof.* Say `p_b ∈ π_a` and `p_a ∉ π_b`. Then `p_b ∈ m`, and the 1-ear point `y` lies on `m`. So
`y ∧ p_b ∝ m` for every placement, and `Λ₁(y) = span(p_a ∧ y, m)` is the pencil `Pen(y, π_a)`. Two
distinct `y` give pencils meeting in `⟨m⟩`. ∎

*Why the certificate said `0`.* `earstep.py --lamcap` intersects `Λ` over 12 random placements but does
not check that each has the generic span. Its own RNG stream (`lamguard.py --replay`) draws, in orbit
(ii) at `k = 1`, a placement with `y ∝ p_b`: span 1, and `Λ = ⟨p_a ∧ p_b⟩ ∌ m`. That one draw zeroes the
intersection. Span-deficient draws also occur at (ii) `k = 2, 3` and (iv) `k = 1`.

*The guarded re-run.* 24 placements per cell, each asserted to have generic `λ`, with deficient draws
rejected and counted. Apart from (ii) at `k = 1`, every cell's intersection is `0` except the two
recorded ones: (iii) at `k = 1` (`⟨n⟩`) and (iv) at `k = 2` (`Λ²π`). So (MC-25) (`k = 4`, every orbit), (MC-45) (`k = 3` at `r = 1`) and
(MC-46)'s `B₂(1) = ∅` stand.

*Downstream.* The orbit-(ii), `k = 1` cell is used by no landed claim. At `k = 1`, (MC-26)'s `r = 1`
sentence is cited only by (MC-100), in orbit (i), where it is correct. The only `k = 1` leaves of
(MC-89) are (MC-54) at `δ = 0` (`r = 0`) and SPLITOFF (MC-31), which uses no `(P₁)`. Of the
span-deficient draws, the one at (ii) `k = 3` (draw 8: `λ = 3`, every hinge nonzero) **is** on
(MC-89)'s path, through (MC-45) at `r = 1`. There the as-run `--lamcap` certificate was invalid,
though its value `0` is right. The cell is certified by `lamguard.py`'s guarded run and proved by
hand in (MC-135)/(MC-137)(b). The (ii) `k = 2` draw sits under (MC-85) and (MC-88)'s corollary only,
now covered by (MC-92). The (iv) `k = 1` draw sits under no landed claim. *(Rewritten at the second
reading, 2026-09-25, `replay_odd.py`.)*

*Suggested fix.* Add a per-draw `λ` guard to `--lamcap`, and add orbit (ii) at `k = 1` to (MC-26)'s
exceptions.

**Part V — what `δ` against `δ₂` does to (MC-51)(c).**

Cell (c) is `k = 1`, `a ≁ b`, `dim U ≥ 2`, `1 ≤ δ ≤ 4`.

> **(MC-98)** `[PROVED]` *(the pairs in cell (c); the pair list is combinatorial, while "`dim U ≥ 2` is
> `δ₂ ≥ 2`" is modulo (MC-33): JJ at `G′` for `⟹` ((MC-62)'s `≤` half) and at `G′ + ab` for `⟸`
> ((MC-48)(ii)'s argument); second reading, 2026-09-25)* Modulo (MC-62), `dim U ≥ 2` is `δ₂ ≥ 2`. By (MC-91), the
> cell holds exactly the pairs `(δ, δ₂) ∈ {(1,2), (2,2), (1,3), (2,3), (3,3), (4,3)}`, and all occur (the
> (MC-91)(b) witnesses). **`δ ∈ {3, 4}` forces `δ₂ = 3`** (`U = K³` modulo JJ), and **`δ₂ = 2` forces
> `δ ≤ 2`**.

> **(MC-99)** `[PROVED-MOD]` *((MC-33); JJ at `G′` and `G′ + ab` only)* If `a ≁ b` and `dim U ≥ 2` at generic
> `q`, the generic flag pair is in **orbit (i)**.

*Proof.* Suppose the orbit is (ii), with `U ⊆ p̂_b^⊥`. Then `dim U = 2` and `U = p̂_b^⊥ ∋ ℓ_ab`.
- The citation-free first line of (MC-63)(b)'s proof applies: the kernel of
  `F(G′) → U/(U ∩ Kℓ_ab)` is `F(G′ + ab)`. So `dim F(G′) − dim F(G′ + ab) = dim U − 1 = 1`.
- (MC-4)(b) at `G′` and JJ at `G′ + ab`, with `def₂(G′ + ab) = f₂ − min(δ₂, 2)` ((MC-48)(ii)'s count),
  bound the left side below by `min(δ₂, 2)`. So `δ₂ ≤ 1`.
- JJ at `G′` gives `dim U ≤ min(δ₂, 3) ≤ 1` ((MC-62)'s `≤` half), a contradiction.
- Orbits (iii) and (iv) have `dim U ≤ 1`. ∎

This is sharper than (MC-64) for the present use. For `k = 1`, (MC-64) would need JJ at
`G′ + ab + x = G + ab`, which is not smaller than `G`. `G′` and `G′ + ab` are.

> **(MC-100)** `[PROVED-MOD]` *((MC-33); `δ = 1` closes; JJ at `G′`, `G′ + ab` for the orbit)* In cell (c) with
> `δ = 1`, under IH, `X₀(G′ + ear₁)` attains.

*Proof.*
- (MC-44) gives `r = 1`; `G′ + ab` has `|V(G)| − 1` vertices.
- (MC-22) at `k = 1` applies: dominance holds because `dim U ≥ 2`, and `λ = 2` in orbit (i) (MC-99).
  `(R₁)` holds.
- `(P₁)` at `r = 1` is `ρ ⊄ ⋂Λ₁`. In orbit (i), `Λ₁(y) = y ∧ n̂` for `y ∈ m`, with `m̂ ∩ n̂ = 0`, so two
  distinct `y` give spans meeting in `0`. (This is the correct half of (MC-26)'s `k = 1` claim; compare
  (MC-97).) ∎

> **(MC-101)** `[PROVED-MOD]` *((MC-33); `(δ, δ₂) = (2, 2)` closes; JJ at `G′`, `G′ + ab` and at the blobs
> below)* In cell (c) with `δ = δ₂ = 2`, under IH, `X₀(G′ + ear₁)` attains.

*Proof.* **Combinatorics.**
- Let `Y` attain `δ₂ = 2` in (MC-90). It is connected ((MC-91)(a)), and `2 = δ ≤ def₃(G′[Y]) ≤ def₂(G′[Y]) = 2`.
- A `def₃`-optimal partition `𝒫` of `G′[Y]` therefore has `val₃ = val₂ = 2`. From
  `val₃ = val₂ + 3(|𝒫| − 1 − d)` and connectivity, `d = |𝒫| − 1` and `|𝒫| = 3`. So `𝒫 = {P₁, P₂, P₃}` with
  exactly two crossing edges forming a path.
- `𝒫` is `def₂`-optimal in `G′[Y]`, so each `P_i` is a single vertex or a `def₂`-rigid set.
- `a` and `b` are not in one part, since then `δ ≤ def₃(G′[P_i]) = 0`. They are not in adjacent parts,
  since then `δ ≤ def₃(G′[P_i ∪ P_j]) ≤ def₂(G′[P_i ∪ P_j]) = 1`.
- So `a ∈ P₁`, `b ∈ P₃`, with bridge edges `e₁ = u₁v₁` (`u₁ ∈ P₁`, `v₁ ∈ P₂`) and `e₂ = u₂v₂`
  (`u₂ ∈ P₂`, `v₂ ∈ P₃`).

**Rigidity of the blobs** (JJ at each `P_i` with `|P_i| ≥ 3`; such a `P_i` satisfies (H) and is smaller
than `G`). As in (MC-13)(c)'s "if", every `P ∈ F(G′, q)` is constant on `P_i`. So at every point of
`B(G′)` the planes of `P_i` coincide, in a plane `σ_i` holding all of `P_i`'s points. The affine map
`(x, y, z) ↦ (x, y, z − h_{σ_i}(x, y))` carries this subframework to the flat framework of `G′[P_i]` at
`q|_{P_i}`. By (MC-4)'s block split that framework has kernel dimension `3 + dim F = 6`: it is rigid. So
every motion of `G′[Y]` is constant on each blob, and `X_b − X_a ∈ ⟨L₁, L₂⟩` with `L_j := C_{e_j}`.
Since `ρ(G′) ⊆ ρ(G′[Y])` and `r = δ = 2` ((MC-44)), `ρ = ⟨L₁, L₂⟩`.

**`(P₁)`.** In orbit (i) (MC-99), at `r = 2`, (MC-27)'s criterion says `(P₁)` fails iff
`ρ = m̂ ⊗ y₀ = Pen(y₀, ⟨m, y₀⟩)` for some `y₀ ∈ n`. Re-derived here. `Λ₁(y) = y ∧ n̂ ⊆ W₄`, so
`ρ₄ := ρ ∩ W₄` must meet every `y ∧ n̂`.
- If `dim ρ₄ ≤ 1`, it cannot, since `⋂_y (y ∧ n̂) = 0`.
- If `ρ₄ = ρ`, view `m̂ ⊗ n̂` as `2 × 2` matrices. The determinant restricted to `ρ` either has at most two
  rank-one lines, which meet only two of the `y ∧ n̂`, or vanishes identically. In the second case `ρ` is
  `y₁ ⊗ n̂`, which meets only one, or `m̂ ⊗ y₀`, which meets all.

So if `(P₁)` fails, `⟨L₁, L₂⟩` is the pencil `Pen(y₀, ⟨m, y₀⟩)`. A pencil's lines all pass through its
vertex, so `y₀ ∈ L₁ ∩ L₂ ∩ n`.

Project from the vertical point `(0:0:1:0)`, which lies on none of `L₁`, `L₂`, `n`, since those
endpoints have distinct `q`. The lines `q_{u₁}q_{v₁}`, `q_{u₂}q_{v₂}` and `q_a q_b` would then be concurrent
in `P²`. The only possible vertex coincidences are `u₁ = a`, `v₁ = u₂` and `v₂ = b`, and no vertex lies on
all three lines. So concurrency is a proper closed condition on `q`:
- if `v₂ ≠ b`, `b` occurs only in `q_a q_b`: move `q_b` off the line through `q_a` and
  `ℓ₁ ∩ ℓ₂` (here `ℓ₁ := q_{u₁}q_{v₁}`, `ℓ₂ := q_{u₂}q_{v₂}`; `ℓ₁ ∩ ℓ₂ ≠ q_a` at generic `q`);
- if `u₁ ≠ a`, `a` occurs only in `q_a q_b`: move `q_a` off the line through `q_b` and `ℓ₁ ∩ ℓ₂`;
- if `u₁ = a` and `v₂ = b`, the common point would be `q_a`, and it would have to lie on
  `q_{u₂}q_b`.
The planar picture of `X₀(G′)`'s generic point is generic. So `(P₁)` holds, and (MC-22) concludes. ∎

Special case: if `a` and `b` have a common neighbour `c`, take `Y = {a, c, b}`. It attains `δ₂ = 2`, its
blobs are singletons, and `L₁ ∩ L₂ = p_c`. Then no blob needs JJ.

> **(MC-102)** `[PROVED-MOD]` *((MC-33); `δ = 2` with a class path; rests on (MC-68)(d) and (MC-70), read
> but not re-derived by the author; JJ at `G′`, `G′ + ab`, each class `R_j` and each `G′/R_j`)*
> - Let `Γ₃` be `G′` with its `def₃`-classes contracted. It is simple: two classes joined by two edges
>   would merge at a gain of `+4`.
> - `δ = min_{X ∋ A,B} [6(|X| − 1) − 5e_{Γ₃}(X)]`, by (MC-90) and the class-partition argument of
>   (MC-63)(a) with `(6, 5)`.
> - If a minimising `X` spans a tree, then `|X| = δ + 1`, and minimality makes it a path of classes
>   `A = R₀ − R₁ − ⋯ − R_δ = B`, joined by single edges.
> - **In cell (c) with `δ = 2` and such a path, `X₀(G′ + ear₁)` attains** under IH.

*Proof.*
- *Additivity.* `def₃(G′) ≥ δ > 0`, so each class `R_j` with `|R_j| ≥ 2` is a maximal proper
  `def₃`-rigid set with `G′/R_j` simple. It is additive by (MC-70), outside the exceptional case, which
  needs `def₃(G′) = 0`.
- *Rigidity of the classes.* By (MC-68)(d), restriction `L_{G′}(q) → L_{R_j}(q|_{R_j})` is onto at
  generic `q`. So `B(G′) → B(R_j)` is dominant. `R_j` satisfies (H) and attains by IH, and
  `def₃(R_j) = 0`, so `R_j` is rigid at `X₀(G′)`'s generic point.
- *Conclusion.* As in (MC-101), `ρ = ⟨L₁, L₂⟩`, and the projection argument, which uses only the vertex
  pattern, gives `(P₁)`. ∎

`(δ, δ₂) = (2, 3)` with a class path does occur: `W2` below, a `C₆` class, a vertex, then a triangle. So
(MC-102) is not subsumed by (MC-101).

> **(MC-103)** `[OPEN]` *(what remains of (MC-51)(c), the rest of the cell. Superseded: the `δ = 2`
> bullet is closed by (MC-112), for cyclic class quotients too. The `δ ∈ {3, 4}` bullets are (MC-117),
> narrowed in 𝒮 by (MC-154). "asks each `L_j` to meet `m` and `n`" is the `δ = 3` case; at `δ = 4`
> only `dim(ρ ∩ W₄) ≥ 3` is asked. Second reading, 2026-09-25.)*
> - **`δ = 2` with a cyclic class quotient.** Then `|X| − 1 = 2 + 5c` with `c ≥ 1`, so at least 8 classes;
>   for example `C₈` with `a, b` at distance 4. Here `ρ` is an intersection of two path spans, not a span
>   of bridge lines.
> - **`δ ∈ {3, 4}`, where `δ₂ = 3`.** For a class path, the argument of (MC-102) still gives
>   `ρ = ⟨L₁, …, L_δ⟩`. `(P₁)` then fails iff `dim(ρ ∩ W₄) ≥ 3`, or `ρ ⊇ m̂ ⊗ y₀` ((MC-27)).
>   - The pencil alternative is killed by projection whenever the only pencils in `ρ` are at shared
>     bridge vertices.
>   - The `W₄` alternative asks each `L_j` to meet `m` and `n`. That depends on heights, not only on
>     `q`. When the chain is the path `a − c₁ − c₂ − b` of singleton classes, `L₁ ⊂ π_a` and `L₃ ⊂ π_b`
>     lie in `W₄` automatically, and only `L₂` is in question.
>   - This is genuinely geometric.
> - Split-off instances on ≤ 8 vertices (from (MC-91)(d)'s joint count) in the open part: `(δ, δ₂) = (2, 3)`:
>   15 (some have class paths, not separated here), `(3, 3)`: 53, `(4, 3)`: 16.

> **(MC-104)** `[CONSTRUCTED]` *(`cellwit.py`; targeted checks above the census range)*
> - `W1`, (MC-101)'s three-triangle chain plus the ear, on 10 vertices, and `W2`, (MC-102)'s
>   `C₆`–vertex–triangle chain plus the ear, on 11 vertices, have the stated `(δ, δ₂)`.
> - Each has an `X₀` point with rank equal to its target (54 and 60). This is a certificate that both
>   attain.
> - It checks the conclusions at one instance each. It is not evidence for the class statements beyond
>   that.

**Part VI — the cell (a′) of Step MC16, and a cross-check of (MC-88).**

*Added after Step MC16's author reported.*

> **(MC-105)** `[PROVED]` *(cell (a′) is closed under the strong induction, with no citation beyond the
> cell's own orbit hypothesis)* Take Step MC16's (a′): `k = 2`, `a ∼ b`, `δ = 1`, orbit (iii). There
> `X₀(G′ + ear₂)` attains.

*Proof.*
- (MC-85) reduces the step to `r = 1` at `X₀(G′)`'s generic point.
- (MC-94) gives `r = δ = 1` from `X₀(G′)` and `X₀(G′ + x)` attaining, with `x` joined to `a` and `b`.
  `G′ + x` is simple, satisfies (H) and has `|V(G)| − 1` vertices, so it attains by IH.
- This is (MC-95)(ii). The orbit-(iii) hypothesis is part of (MC-85)'s cell. Where it must itself be
  derived, it is `U ≠ 0`: modulo JJ at `G′ + x` by (MC-95)(iii), or at `G′` and `G′_{ab}` by (MC-79)(vi). ∎

*Why the triangle succeeds where (MC-24) gave up.* At `a ∼ b` with `dim U = 1`, `X₀(G′ + x)` lies over
the proper locus `{π_a = π_b}` of `B(G′)` ((MC-18)(b)). So it is not dominant, and (MC-22) cannot be
applied to it. (MC-94) never uses dominance. On `X₀(G′ + x)` the triangle `a b x` welds `a` to `b`, so
there `dim M_weld(G′) = 6 + g`. Upper semicontinuity of `dim M_weld` on the irreducible `B(G′)` carries
this bound from the special locus to the generic point. That is exactly (MC-44)'s mechanism, with the
triangle playing the chord. **So the hinge `ab` is never locked at an (a′) chain under IH.**

> **(MC-106)** `[CONSTRUCTED]` *(`aprime.py`; targeted checks at Step MC16's family, `A⁶` on 24 vertices and
> `A⁷` on 28)* At the chain of bead 0 in each:
> - `(δ, δ₂) = (1, 1)`;
> - at an attaining `X₀(G′)` point, `r_draw = 1`, which certifies `r = 1` at the generic point;
> - at an attaining `X₀(G′ + x)` point, `dim M_{G′+x} = dim M_weld(G′)` at the restriction, `= 6 + g`
>   (6 and 7);
> - `X₀(Aᵘ)` attains, at 138/138 and 161/161.
>
> These are ranks mod `2⁶¹ − 1`, used only as certificates. They check the conclusion at two instances.

> **(MC-107)** *(cross-check of (MC-88))* **(MC-91) is an independent proof of (MC-88)'s statement, and it is
> stronger.** It uses no class quotient and no Lemma T (MC-78). (MC-90)'s one-merge-one-refine formula
> `δ_D = min_Y def_D(G′[Y])` and connectivity give `δ ≤ δ₂` whenever `δ₂ ≤ 2`, including
> `δ₂ = 2 ⟹ δ ≤ 2`, which (MC-88) records only as `[CONJECTURED]` (`δ₂ ≥ min(δ, 3)`). (MC-91)(a) proves that conjecture for
every finite graph and pair. The author also read (MC-88)'s own proof.
> - Its second case holds: at most one edge joins two `def₂`-classes, and merging along
>   `def₃`-rigid classes does not lower `val₃`, so the union of the classes in `R` is `def₃`-rigid.
> - Its first case holds: two classes joined by one edge have `def₃ = 1`, which is (MC-90) at
>   `Y = A ∪ B`.
> - Lemma T (MC-78) itself was not re-derived. (MC-91) does not need it.
> - Both (MC-85) and (MC-88)'s corollary cite (MC-26) only at `k = 2`, `r = 1`, which (MC-92) confirms. The
>   (MC-26) erratum (MC-97) is at `k = 1` and does not touch them.

**Where the citations sit.**

Every JJ use above is at a named graph with fewer vertices than `G`:
- `G′ + ab + x` for (MC-93), with `k = 2`;
- `G′ + x` for (MC-95);
- `G′ + x` again in (MC-96)(i)'s `U = 0`, `δ = 1` exclusion. At `k = 1` that graph is `G` itself,
  not a smaller one, so there it is a citation of the theorem, not an induction hypothesis;
- `G′` and `G′ + ab` for (MC-99)–(MC-102);
- the blobs of (MC-101) and the classes of (MC-102), which satisfy (H);
- the quotients `G′/R_j` of (MC-102), which are simple but may have a degree-1 vertex `v*` when `G′` has a
  bridge.

Under (MC-60)'s strengthened motive ("attains **and** `ℓ₀ = 3 + def₂`"), those satisfying (H) would be
induction hypotheses. For `k = 1` and `k = 2`, the (MC-60) remark's propagation through EAR covers `G`
itself. But that motive consumes JJ at FLAT, so this relocates the citation rather than removing it. I
have not second-read the (MC-60) remark.


**Drivers** (all at `PYTHONHASHSEED=0` from the repository root; exact integer or ℚ arithmetic; ranks
mod `2⁶¹ − 1` only as certificates):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/deltapairs.py --witness` / `--exh 7 --minY --brute` / `--akb` | 13/13 witness pairs; (MC-90)/(MC-91) asserted at 11 693 pairs of 583 graphs on ≤ 7 vertices; `θ(1,3,4)`, `θ(1,3,6)` | 0.2 s / ~30 s / 0.2 s |
| `python3 notes/scripts/w4/splitcells.py --exh 8` / `splitdu.py --exh 8` | (MC-91)(d): the joint `(δ₂, δ)` over Step MC11's 4 751 instances; the 4 jump pictures | ~6 s / ~52 s |
| `python3 notes/scripts/w4/lamguard.py` / `--replay` / `--hand` | (MC-97): guarded intersections per orbit and `k`; the deficient draws of `--lamcap`; (MC-92)'s hand placements | < 1 s each |
| `python3 notes/scripts/w4/cellwit.py` | (MC-104): `W1`, `W2` attain (54/54, 60/60) | < 1 s |
| `python3 notes/scripts/w4/aprime.py --u 6 7` | (MC-106): `A⁶`, `A⁷` | ~1 s |


