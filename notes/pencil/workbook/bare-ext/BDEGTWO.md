## §(K-bare-ext), continued — direction BDEGTWO: **BOTH OF (BE-134)'s GAPS ARE SETTLED, AND THE ARCHITECTURE — NOT THE CLAUSE — IS WHAT FAILS AT SIDE-DEGREE `≥ 2`** (*Steps BE135–BE140*)

**The `p_x`-sweep EXISTS at every `k ≥ 2`**, so (BE-134)(i)'s *"no lemma in the section covers that"* is a **gap in the write-up, not an obstruction**: at `k ≥ 2` the flag normal `n_x` is no longer *free*, but it is **determined and rational** in `q_x` — `n_x = (q_{c₁} − q_x) × (q_{c₂} − q_x)`, nonzero off the fixed line `q_{c₁} ∨ q_{c₂}` — and (BE-124)(ii)'s completion never used the pencil's *dimension*, only that a plane through the fixed side-`i` star exists, so the rest of it runs verbatim. The fibre has **four** shapes, not (BE-134)(ii)'s three: `𝔸³`, the plane `π_{c₁}`, the line `π_{c₁} ∩ π_{c₂}`, and — at `k ≥ 3`, which (BE-134) does not mention — the plane `π_x` **itself**, with `π_x` **constant** along its own fibre; all four are **realized as legal chart points**, 411/411 targets over 70 peels on 35 (CH-1)-asserted composites. **The reduction is then exact and uniform in `k`**: `Π_x = p_x ∧ L_{jk}` for *every* pair of side-neighbours, so all `C(k,2)` instances of (BE-127)(ii) are **one** condition, `Π_x ∩ A ≠ 0` — which makes the hand-off's *"exact `k ≥ 2` reduction keeping `xc₂…xc_k`"* **MOOT as a relaxation-level move**, and makes (BE-130)(i) a **one-line count** (`2 + 5 > 6`) with no Segre analysis. **And `(∗)` is STRICTLY STRONGER than the route needs:** what (BE-127)(ii) has to exclude is `Bad ≠ P³`, and at the **β-ruling** `Λ²π′ ⊆ A` with `L_c ⊆ π′` the condition `(∗)` **fails** while `Bad` is the **proper plane** `π′` — so BLINE refuted more than it had to, recovering **2** of its own 142 failures, though **not one** of the 140 `dim A ≥ 5` rows where a generic chart point lives. **Gap (ii) closes as a criterion at all four shapes:** a fibre is entirely bad exactly when `A` swallows a **2-dimensional totally singular family adapted to it** — `Π_{c₁} ⊆ A` at the one-hub plane, `dim(A ∩ Λ²π_x) ≥ 2` at the `k ≥ 3` plane, `M ∧ t₀ ⊆ A` at the two-hub line — or a dimension count forces it, each asserted as an **iff** against an exact identically-vanishing-quadric test. **What actually fails is the ARCHITECTURE.** At `k = 1` the pendant edge's multiplier `ω` is **free**, which is the whole of (BE-114)(i); at `k ≥ 2` it is **determined by the core motion**, and the exact space is `ρ̄_i = {s(m) + a(m)ℓ₁ : m ∈ r^{-1}(Π_x)}` — asserted as an identity of **subspaces** at 162/162 rows — whose subspace `r^{-1}(Π_x)` **moves with `p_x`**. `A` is recovered *only* by dropping that constraint, and it is the **only** `p_x`-free object available. So (BE-114)(iii)'s *"a condition on a point against a **fixed** subspace"* — the technique the whole `deg_i(x) = 1` theorem rests on — is **provably unavailable at `k ≥ 2`**. **The price, and the successor:** the sharp object `A_sharp = s(r^{-1}(Π_x))` is strictly smaller than `A` at **89 of 162** rows and has `dim ≤ 4` at **30** rows where `dim A ≥ 5`, so it has content exactly where the relaxation has none; and along the sweep the relaxed condition holds at **every** point of the fibre on **28 of 70** peels while the clause **itself** is violated at **0 of 411** — *not found under this cap*, never *"cannot happen"*. **Nothing is refuted**: (BE-127)(i), (BE-116), (BE-119)(i), (BE-129)–(BE-133) and every landed measurement stand, and (BE-133)(ii)'s figures are reproduced **exactly**

### Standing notation (on top of *Steps BE128–BE134*)

BLINE's and BPROPER's, verbatim: `x, y` the peel's terminals, `deg_i(v)` the
degree of `v` **inside** `side_i`, `core := side_i − x`,
`A := ρ̄(core; c₁, y)`, `ℓ_j := p_x ∧ p_{c_j}`, `Π_x := p_x ∧ π_x`,
`Σ_p := p ∧ K⁴`, `Λ²π` the β-plane of `π`, `L_c := p_{c₁} ∨ p_{c₂}`,
`𝒜(H)`/`Chart(H)` §(K-chart) *Step CH1*'s two ambients. Three more, all
introduced here:

> **`Bad := {p ∈ P³ : (p ∧ L_c) ∩ A ≠ 0}`** — the locus (BE-127)(ii)'s
> reduction confines the clause to, written as a condition on `p` rather
> than as a quantifier over `L_c`. **`F`** is the `p_x`-**fibre**: the set
> of `q_x` reachable with the whole core held fixed (*Step BE135*).
> **`A_sharp`** is *Step BE138*'s `p_x`-dependent replacement for `A`.
>
> **One reading convention, because it is the section's whole point.**
> *BAD* (the clause) always means `Π_x ⊆ ρ̄_i` **with `ρ_i ≤ 5`**; *relaxed
> bad* means the strictly weaker `Π_x ∩ A ≠ 0`, which is what (BE-127)(ii)
> reduces to. Every count below says which one it counts.

### Step BE135 — (BE-136): the `p_x`-sweep at `k ≥ 2`, and the FOUR fibre shapes

> **(BE-136)(i)** *(**PROVED**; the equations, listed exhaustively at
> `k ≥ 2`)* Read off §(K-chart) *Step CH3*'s tower exactly as (BE-124)(i)
> does, but without its `deg_i(x) = 1`: the defining equations of `𝒜(H)`
> are `n_h · (q_u − q_h) = 0` for every hub `h` and every `u ∼ h`, so with
> the whole core held fixed the equations coupling `q_x` to fixed data are
>
> - **`q_x ∈ π_{c_j}`** for every side-`i` neighbour `c_j` that is a
>   **hub** (its normal is core data) — at most **two** such `j`, by
>   `hcard` (`d_x ≤ 2`);
> - **`n_x · (q_{c_j} − q_x) = 0` for every `j = 1..k`** — which at
>   `k ≥ 2` no longer leaves a pencil: `π_x` must carry the **whole fixed
>   set** `{q_{c_1}, …, q_{c_k}}`.
>
> Every other equation involving `q_x` or `n_x` names a **side-2** vertex,
> and `x ≁ y` keeps `q_x` out of `y`'s equations ((BE-118)(i)). ∎

> **(BE-136)(ii)** *(**PROVED**; the fibre, exactly — four shapes)* Let
> `W := aff⟨q_{c_1}, …, q_{c_k}⟩`. Since every `c_j` lies in `π_x`,
> `dim W ≤ 2` at every chart point, and `assert_generic_star` at `x`
> forbids `q_x ∈ W` when `dim W = 1`. Hence, writing `Π_{hub}` for the
> intersection of the `π_{c_j}` over the **hub** side-neighbours,
>
> > **`F = Π_{hub} ∖ W` when `dim W = 1`, and `F = Π_{hub} ∩ W` when
> > `dim W = 2`** — and in the second case `π_x = W` is **CONSTANT** on
> > `F`, while in the first `π_x = ⟨q_x⟩ + W` is **determined by `q_x`**.
>
> With `hcard` capping the hub count at 2, that is exactly **four**
> shapes: `𝔸³` (no hub `c_j`, `dim W = 1`), the **plane** `π_{c₁}` (one
> hub, `dim W = 1`), the **line** `π_{c₁} ∩ π_{c₂}` (two hubs,
> `dim W = 1`) and the **plane** `W = π_x` (`dim W = 2`, i.e. `k ≥ 3` with
> the `c_j` not collinear). ∎ The first three are (BE-134)(ii)'s reading,
> **confirmed at source**; the fourth is not in it, and it is the only one
> in which `Π_x` varies without `π_x` varying.

> **(BE-136)(iii)** *(**PROVED**; the rational completion — gap (i)
> discharged)* Fix a point of `𝒜(H)` and fix the core's points **and**
> normals. Given a target `q_x' ∈ F`, complete it: `n_x'` is the **unique**
> normal of `⟨q_x'⟩ + W` — `n_x' = (q_{c_1} − q_x') × (q_{c_2} − q_x')`
> when `dim W = 1`, a **polynomial** in `q_x'`, nonzero exactly off `W`;
> the core's own normal when `dim W = 2` — and then side 2 is rebuilt by
> (BE-124)(ii)'s own three stages **verbatim**: hub points, those adjacent
> to `x` placed in `π_x'`; hub normals, nonzero by `hcard`, the row
> `q_x' − q_h` of `A_h` being *itself* the equation `q_x' ∈ π_h`; non-hub
> points as intersections of hub planes. Every stage is a linear solve, so
> a fixed choice gives a **rational** `ψ : F ⇢ 𝒜(H)` with `q_x ∘ ψ = id`,
> regular on a dense open of `F` and landing in `𝒫(H) ∩ U_H ∩ N°` there. ∎
>
> **What this discharges, exactly.** (BE-134)(i) reads *"the completion it
> builds re-solves `n_x` from a pencil of planes through `q_x ∨ q_c`, which
> exists precisely because `π_x` is not yet determined"*. That is true and
> is **not** what the completion needs: it needs a **nonempty** fibre for
> `n_x`, and a determined-but-rational `n_x` serves the argument better,
> not worse — the pencil's extra dimension was spent, in (BE-124), on
> nothing at all. So a proof of `(∗)` would leave item 1 **one** step
> short, not two.
>
> Measured, as an adversarial control on the construction rather than as
> the statement: **411/411** targets over **70** free peel draws on **35**
> composites realized as legal chart points, with `hcard`, min degree 2,
> `girth ≥ 4`, both terminals hubs of `H`, `x ≁ y` and side 2
> `rnode_shaped` asserted at **35/35** *before* any target is drawn; and at
> every realized target the core asserted **unchanged as a placement**,
> `verify_pencil_witness` passing, `π_x` asserted to carry the fixed
> side-`i` star, and the fibre asserted **unchanged** under its own sweep
> (it is core data). Fibre shapes over the 70 peels: `𝔸³` 36, plane
> `π_{c₁}` 18, plane `π_x` 10, line 6 (`bdegtwo.py sweep`).

### Step BE136 — (BE-137): the reduction, uniform in `k` — and what it really needs

> **(BE-137)(i)** *(**PROVED**; `Π_x = p_x ∧ L_{jk}` for every pair, so
> "keep `xc₂…xc_k`" is MOOT at this level)* `π_x = ⟨p_x⟩ + L_{jk}` for any
> two side-neighbours `c_j, c_k` with `p_x ∉ L_{jk}`, so
> `Π_x = p_x ∧ π_x = p_x ∧ L_{jk}` — the **same** 2-space for every pair.
> And `Π_x ⊆ ⟨ℓ_j⟩ + A` for one `j` already gives `Π_x ∩ A ≠ 0`: pick
> `u ∈ Π_x` independent of `ℓ_j`, write `u = cℓ_j + a`, and `a ≠ 0` lies
> in `Π_x ∩ A`. Hence, with (BE-114)(iv)'s inclusion for each `j`,
>
> > **BAD ⟹ `Π_x ∩ A ≠ 0`, and every one of the `C(k,2)` instances of
> > (BE-127)(ii) is THIS ONE CONDITION.** ∎
>
> So the successor the `(K-bare)` row and `notes/Phase39.md` item 0(a)
> both name — *the exact `k ≥ 2` reduction keeping `xc₂, …, xc_k`* — buys
> **nothing** as long as the object on the right is `A`: retaining the
> deleted edges changes `ρ̄_i`, not the reduction. What it *can* change is
> `A` itself, and that is *Step BE138*. Asserted at **288** pairs over
> **192** side configurations (`bdegtwo.py exact`).

> **(BE-137)(ii)** *(**PROVED**; (BE-130)(i) in one line)* `dim(p ∧ L_c) = 2`
> for every `p ∉ L_c`, so `dim A ≥ 5` forces `(p ∧ L_c) ∩ A ≠ 0` by
> `2 + 5 > 6` — **at every `p`**. Hence `Bad = P³` and the reduction is
> vacuous, with **no** reference to the Segre rulings. ∎ Asserted at 300
> draws with `dim A ∈ {5, 6}`.

> **(BE-137)(iii)** *(**PROVED**; `(∗)` is SUFFICIENT, NOT NECESSARY)*
> What (BE-127)(ii) must exclude is `Bad = P³`, and that is **decidable in
> closed form**: `Bad(p)` says the `(6 − dim A) × 2` matrix
> `M(p)_{ij} = f_i(p ∧ t_j)` (the `f_i` spanning `A^⊥`, `t_1 = p_{c₁}`,
> `t_2 = p_{c₂}`) drops rank to `≤ 1`; its entries are **linear** in `p`,
> so each `2 × 2` minor is a **quadratic form** and `Bad = P³` iff every
> one of them vanishes **identically**. Now compare with `(∗)`:
>
> - the **α-ruling** `Σ_{t₀} ⊆ A` with `t₀ ∈ L_c` — `(∗)`'s first half —
>   gives `p ∧ t₀ ∈ A` for **every** `p`, so `Bad = P³`: **necessary**;
> - the **β-ruling** `Λ²π′ ⊆ A` with `L_c ⊆ π′` — a `(∗)` failure by
>   (BE-129)(iii) — has `V_t ∋ t` for every `t ∈ L_c ⊆ π′`, so every `V_t`
>   lies in `π′` and `Bad = π′` is a **PROPER PLANE**: `(∗)` fails and the
>   route survives. ∎
>
> Both are **CONSTRUCTED** (30 each) and asserted; a random `A` never
> reaches either, so the separation is **invisible to any sampler** — at
> 300 random `(A, L_c)` spread over `dim A = 0..6`, `(∗)` and `Bad ≠ P³`
> agree at every draw. `(∗) ⟹ Bad ≠ P³` is asserted at all 300.

> **(BE-137)(iv)** *(**MEASURED**; the recount on BLINE's own population,
> and it does NOT rescue the stratum)* Over (BE-133)(i)'s **27**
> topologies at BLINE's own seeds — **270** rows, `dim A` census
> `{1: 30, 2: 10, 3: 60, 4: 30, 5: 60, 6: 80}`, reproducing (BE-133)(ii)
> **exactly** — `(∗)` fails at **142** and `Bad = P³` at **140**, the
> latter being **precisely** the `dim A ≥ 5` stratum (asserted). So the
> correct condition **recovers 2 rows**, both of them (BE-133)(ii)'s own
> β-ruling failures at `dim A = 3` and `4`, and **none** of the 140 where
> (BE-133)(iii) puts a *generic* chart point. **The route is dead exactly
> where BLINE said it was**, for a reason one dimension count shorter.

### Step BE137 — (BE-138): gap (ii), settled in closed form at all four shapes

> **(BE-138)(i)** *(**PROVED**; the components of `Bad`)* `Bad` is the
> image of the projective incidence `J = {(p,t) ∈ P³ × P(L_c) : p ∧ t ∈ A}`,
> hence **closed**; the fibre of `J` over `t` is the linear
> `P(V_t)`, `V_t = {p : p ∧ t ∈ A}`, so the irreducible components of `Bad`
> are the **ruled surface** `R := \overline{⋃_{generic t} P(V_t)}` together
> with `P(V_{t₀})` for the finitely many `t₀` at which `dim V_t` jumps. A
> fibre `F` is entirely bad iff `\overline{F}` sits inside one of them
> (`F` irreducible), so each shape is decided by naming which. ∎

> **(BE-138)(ii)** *(**PROVED**; the ONE-HUB plane `π_{c₁}`)* Here
> `L_c ∩ π_{c₁} = ⟨p_{c₁}⟩`, because `q_{c₂} ∈ π_{c₁}` would need
> `c₂ ∼ c₁` and `x c₁ c₂` is a triangle, excluded by `girth ≥ 4`. So
> `R = π_{c₁}` would force `V_t ⊆ π_{c₁}` for generic `t`, hence
> `L_c ⊆ π_{c₁}` — impossible; and `P(V_{t₀}) = π_{c₁}` forces
> `t₀ ∈ L_c ∩ π_{c₁}`, i.e. `t₀ = p_{c₁}`, whose `V_{t₀} = π_{c₁}` says
> `p ∧ p_{c₁} ∈ A` for **every** `p ∈ π_{c₁}`. Therefore
>
> > **`π_{c₁} ⊆ Bad ⟺ Bad = P³` or **`Π_{c₁} ⊆ A`**,**
>
> where `Π_{c₁} = p_{c₁} ∧ π_{c₁}` is `c₁`'s **own** pencil space
> (`bimage.pencil_space`). ∎ Asserted as an **iff** at 300 draws, 137 of
> them with `Π_{c₁}` **planted** inside `A` (`bdegtwo.py fibrebad`).

> **(BE-138)(iii)** *(**PROVED**; the `k ≥ 3` plane `π_x`)* Here
> `L_c ⊆ π_x` and `p ∈ π_x`, so `p ∧ L_c = p ∧ π_x ⊆ Λ²π_x` — a 2-space
> inside the 3-space `Λ²π_x`, namely (under `Λ²π_x ≅ π_x^*`) the **dual
> line** of the point `p`. Writing `A₀ := A ∩ Λ²π_x`, the condition
> `(p ∧ L_c) ∩ A₀ ≠ 0` holds for every `p` iff `dim A₀ ≥ 2` (then
> `2 + 2 > 3`), fails outside one line of `π_x` if `dim A₀ = 1`, and never
> holds if `A₀ = 0`. Therefore
>
> > **`π_x ⊆ Bad ⟺ dim(A ∩ Λ²π_x) ≥ 2`.** ∎
>
> Asserted as an **iff** at 300 draws, 150 with a β-plane slice planted.

> **(BE-138)(iv)** *(**PROVED**; the TWO-HUB line `M := π_{c₁} ∩ π_{c₂}`)*
> `p_{c₁} ∉ π_{c₂}` and `p_{c₂} ∉ π_{c₁}` (girth again), so
> `M ∩ L_c = 0`, `M ⊕ L_c = K⁴` and `M ∧ L_c ≅ M ⊗ L_c ≅ K^{2×2}`, in
> which `p ∧ L_c` is the space of rank-`≤ 1` matrices of **column space**
> `⟨p⟩` — one ruling of the Segre quadric `Q`. With
> `B := A ∩ (M ∧ L_c)`, `M ⊆ Bad` says `P(B)` meets **every** line of that
> ruling. A **plane** meets every line of `P³`, so `dim B ≥ 3` suffices; a
> **line** `P(B)` meets only two points of `Q` unless it *is* a ruling
> line, and the surjecting ruling is `{p ∧ t₀ : p ∈ M}`; `dim B ≤ 1` never
> suffices. Therefore
>
> > **`M ⊆ Bad ⟺ dim(A ∩ (M ∧ L_c)) ≥ 3` or `M ∧ t₀ ⊆ A` for some
> > `t₀ ∈ L_c`,**
>
> the second condition being **linear** in `t₀` and hence exactly
> decidable. ∎ Asserted as an **iff** at 300 draws, with **both** branches
> separately exercised (82 by the dimension branch, 100 by the ruling
> branch) and `dim B = 3` **constructed**, since `dim A ≤ 4` makes
> `dim B = 2` the generic value.

> **(BE-138)(v)** *(the reading — what gap (ii) turns out to be)* The three
> criteria are **one** statement: *a fibre is entirely bad exactly when `A`
> swallows a **2-dimensional totally singular** family of lines adapted to
> that fibre* — a pencil `Π_{c₁}` at the one-hub plane, a β-plane slice at
> the `k ≥ 3` plane, a ruling `M ∧ t₀` at the two-hub line — or a
> dimension count forces it. That is a **membership**, not a quantifier
> over the fibre, and it is the same shape as (BE-115)(iii)'s exception
> `Λ²π ⊆ A`, which the `k = 1` theorem neutralized by the chart fact
> `p_c ∈ π_c`. **No analogous chart fact is available here**, and *Step
> BE139* says why looking for one is the wrong move.

### Step BE138 — (BE-139): the EXACT structure at `k ≥ 2`, and where the architecture stops

> **(BE-139)(i)** *(**PROVED**; the exact relative screw space at `k = 2`)*
> A motion of `side_i` is a motion `m` of the core together with a screw
> `μ` at `x` satisfying `μ − m(c_j) ∈ ⟨ℓ_j⟩` for `j = 1, 2`. Subtracting,
> `r(m) := m(c_1) − m(c_2) ∈ ⟨ℓ_1⟩ + ⟨ℓ_2⟩ = Π_x`; and given that,
> writing `r(m) = a(m)ℓ_1 + b(m)ℓ_2`, the multiplier at `x` is **forced**,
> `μ = m(c_1) − a(m)ℓ_1`. With `s(m) := m(y) − m(c_1)`,
>
> > **`ρ̄_i = span{ s(m) + a(m)ℓ_1 : m ∈ N }`, `N := r^{-1}(Π_x) ⊆ M°`.** ∎
>
> Asserted as an identity of **subspaces** (and of dimensions, against
> `rho_bar_of`) at **162/162** rows over the long-core library
> (`bdegtwo.py sharp`). The general `k` is the same computation with the
> extra consistency conditions `a_2(m) = ⋯ = a_k(m)`; only `k = 2` is
> driver-checked, and that is disclosed as a cap.

> **(BE-139)(ii)** *(**PROVED**; `k = 1` is the DEGENERATE case, and that
> is the whole of (BE-114)(i))* At `deg_i(x) = 1` there is no second
> equation, so `r` imposes nothing, `N = M°` and the multiplier `ω` is
> **free** — giving `ρ̄_i = ⟨ℓ⟩ + A` with `A = s(M°)` a function of the
> core alone. **The pendant edge's free multiplier is not a convenience of
> the proof; it is the reason a `p_x`-free subspace exists at all.** At
> `k ≥ 2` the analogous object is
>
> > **`A_sharp := s(r^{-1}(Π_x)) ⊆ A`, and `Π_x` depends on `p_x`.** ∎
>
> `A` itself is recovered *only* by dropping the constraint `r(m) ∈ Π_x`,
> i.e. by (BE-114)(iv)'s edge deletion — so on this route `A` is the
> **unique** `p_x`-free candidate, and (BE-137)(ii) makes it vacuous
> wherever `dim A ≥ 5`.

> **(BE-139)(iii)** *(**MEASURED**; the sharp object has content exactly
> where the relaxed one has none)* Over the same 162 rows,
> `(dim A, dim A_sharp)` is
> `{(1,1): 18, (2,1): 6, (3,1): 12, (3,2): 6, (3,3): 18, (4,2): 12,
> (4,3): 6, (5,3): 12, (5,4): 6, (5,5): 18, (6,4): 12, (6,5): 17,
> (6,6): 19}`: `A_sharp` is **strictly smaller at 89 of 162**, and has
> `dim A_sharp ≤ 4` — where (BE-138)'s criteria and (BE-115) have
> content — at **30** rows carrying `dim A ≥ 5`, where the relaxation has
> none. `A_sharp ⊆ A` is asserted at every row.

> **(BE-139)(iv)** *(**the verdict**, stated as a negative and meant as
> one)* **Half (B)'s item 1 does not close at side-degree `≥ 2` by
> (BE-127)(i)'s architecture**, and the missing input is now named
> precisely. That architecture is: *constructibility* + *a `p_x`-sweep* +
> *properness of the bad locus in the swept fibre*. Inputs 1 and 2 are
> **available** at `k ≥ 2` — (BE-123)(i) is general and (BE-136)(iii) is
> proved here — and input 3 is available **as a criterion**
> ((BE-138)). What is **not** available is the *technique* (BE-114)(iii)
> names, *"a condition on a point against a **fixed** subspace"*: the only
> `p_x`-free subspace on this route is `A`, and `A` is vacuous on the
> stratum where a generic chart point lives ((BE-137)(ii)/(iv),
> (BE-133)(iii)). **What would close it** is properness for the
> `p_x`-**varying** locus `{p : (p ∧ L_c) ∩ A_sharp(p) ≠ 0}` — a
> determinantal condition of bounded degree in `p`, so decidable at each
> configuration, but needing a class-uniform argument that no landed
> lemma supplies. **That is a change of method, not a further reduction**,
> which is why this direction reports it rather than attempting it.

### Step BE139 — (BE-140): the price, measured ALONG the sweep

> **(BE-140)(i)** *(**MEASURED**; the clause itself, and the control no
> earlier population could run)* At each of the **411** swept chart points
> of *Step BE135* — real points of `𝒜(H)` for a composite peel, not side
> draws — both the clause and the relaxed condition are evaluated. The
> clause `Π_x ⊆ ρ̄_i` with `ρ_i ≤ 5` holds at **0 of 411**: *not found
> under this cap*, never *"cannot happen"*, and it takes the standing tally
> at side-degree `≥ 2` to **0 of 772** (91 at (BE-127)(iii), 270 at
> (BE-133)(v), 411 here). `dim A` census
> `{0: 12, 1: 45, 2: 60, 3: 93, 4: 36, 5: 69, 6: 96}`.

> **(BE-140)(ii)** *(**MEASURED**; the relaxation's cost, which is the
> quantitative form of (BE-139)(iv))* The relaxed condition holds at
> **165 of 411**, and — the figure that matters — at **28 of 70** peels it
> holds at **every** swept point of the fibre, so on those the relaxation
> can prove properness **nowhere**, while the clause is violated on none of
> them. Per fibre shape (points, relaxed-bad, clause-bad): `𝔸³`
> (216, 132, 0), plane `π_{c₁}` (99, 33, 0), plane `π_x` (60, 0, 0), line
> (36, 0, 0).

> **(BE-140)(iii)** *(**MEASURED**; and (BE-134)(ii)'s hazard is NOT
> realized here)* At **all 96** confined-fibre points — 60 on the `k ≥ 3`
> plane, 36 on the two-hub line — the relaxed condition holds at **none**,
> so no chart point in this population puts its fibre inside `Bad`, let
> alone realizes one of (BE-138)'s memberships. (BE-134)(ii)'s witnesses
> stay **abstract**, exactly as that step disclosed, and this is the first
> population that could have contradicted it.

> **(BE-140)(iv)** *(**MEASURED + ASSERTED**; the shortfall control, and
> item 0(c) is untouched)* At the first swept point of each of the 70
> peels, **asserted**: `margin ≤ 0` at `Π_x`, at `Π_y` and at `⟨M⟩`.
> Margin histogram at `Π_x`: `{−3: 24, −2: 46}`; **0 shortfalls**, so
> `notes/Phase39.md` item 0(b) stays **unexhibited** and item 0(c)
> **untouched**. *(Disclosed: `row_of` costs seconds a row, so the margin
> control runs on 70 of the 411 points and the clause evaluation on all
> 411.)*

### Step BE140 — (BE-141): the board, the reading, the classification, the E-rider

> **(BE-141)(i)** *(**the board**)* **What moved.** (BE-134)'s **two gaps
> are both settled**: gap (i) is a write-up gap and the sweep is
> **PROVED** with its fibre classified into **four** shapes
> ((BE-136)); gap (ii) is **closed as a criterion** at every one of them
> ((BE-138)). The reduction is **uniform in `k`** and the named successor
> *"keep `xc₂…xc_k`"* is **MOOT at the relaxation level** ((BE-137)(i));
> (BE-130)(i) gets a **one-line** proof ((BE-137)(ii)); `(∗)` is shown
> **sufficient but not necessary**, recovering 2 of BLINE's 142
> ((BE-137)(iii)/(iv)); the exact `k ≥ 2` structure is **PROVED** and the
> pendant multiplier identified as the architecture's load-bearing fact
> ((BE-139)). **What did not move.** `PencilPair K 3 G`, `hbareSplit`,
> `hK`, (GR-15), (BE-14), the 2-cut step, half (B) as a whole, class
> uniformity, cross-pair welding — untouched. **(BE-127)(i) is untouched**:
> the theorem at side-degree `1` stands exactly as landed. **No shortfall
> is exhibited**; **no landed measurement is refuted** — (BE-133)(ii)'s
> figures reproduce exactly.

> **(BE-141)(ii)** *(**the coordinator's reading**, classified —
> `RESEARCH-ARC.md` §7)* **The spec offered NO prediction on the
> mathematics**, deliberately and on the record (*"yesterday I put three
> predictions into three specs and all three were wrong; the useful half
> each time was naming which section I had not opened"*). What it offered
> instead was an **evidence-stratum declaration** — (BE-134), (BE-127)(i)/(ii)
> and (BE-124)(i) read at source; (BE-123), (BE-125) and `bline.py fibre`
> **not** opened — and one framing claim: that (BE-134)(i) leaves item 1
> *"two steps short, not one"*, to be rated on that rather than on the
> hand-off's phrasing. **Verdict: the framing is CONFIRMED as to which
> question to ask and REFUTED as to the count.** The two gaps are the
> right two, and the hand-off's mechanical-restate reading was wrong. But
> item 1 is **one** step short, not two: the sweep exists, and (BE-134)(i)'s
> own reason for doubting it — the pencil's disappearance — is not a
> reason, because (BE-124)(ii) never used the pencil's dimension. **The
> unopened sections were the right ones to flag**: (BE-123)(i)'s
> constructibility is what makes the architecture `k`-free, and
> `bline.py fibre`'s implementation is what showed (BE-134)(ii)'s
> witnesses to be abstract rather than chart-realized. **Tally**: §7 stands
> at **eighteen instances and eight kinds**; this landing **cites and does
> not increment it** (the 2026-09-02 concurrent-counter finding), and
> offers the coordinator nothing to reconcile beyond a **ninth candidate
> kind — DECLINED-AND-REPLACED**: a spec that withholds a prediction on
> purpose and substitutes a stratum declaration, whose *stratum* half then
> does the work the prediction would have. Whether that is a kind at all,
> or simply §7 working, is the coordinator's call.

> **(BE-141)(iii)** *(classification, mandatory and explicit)* **What is
> proved**: (BE-136)(i)/(ii)/(iii), (BE-137)(i)/(ii)/(iii),
> (BE-138)(i)/(ii)/(iii)/(iv), (BE-139)(i)/(ii). **What is measured, not
> proved**: (BE-137)(iv), (BE-139)(iii), (BE-140)(i)/(ii)/(iii)/(iv) —
> populations, censuses and the margin control. **What is constructed**:
> the α- and β-ruling witnesses, the planted `Π_{c₁} ⊆ A` /
> `Λ²π_x`-slice / `M ∧ t₀ ⊆ A` instances, `dim B = 3`, and
> `wide_library`'s `k ≥ 3` and two-hub-fibre sides. **What is cited**:
> (BE-105)(iv), (BE-114)(i)/(ii)/(iii)/(iv), (BE-115), (BE-118)(i),
> (BE-119)(i), (BE-123)(i)/(ii)/(iii)/(iv), (BE-124)(i)/(ii),
> (BE-127)(i)/(ii)/(iii), (BE-129)(iii), (BE-130)(i), (BE-133)(i)/(ii)/(iii),
> (BE-134)(i)/(ii)/(iii), (CH-1), (CH-2), (CH-3) — all landed. **What is
> refuted**: (BE-134)(i)'s *"two steps short"* count and its *"no lemma
> covers that"* as an obstruction claim; and `(∗)`'s status as the
> condition the route needs. **What is NOT refuted**: `PencilPair K 3 G`;
> `hbareSplit`; (BE-14); half (B); (BE-127)(i); (BE-116); (BE-119)(i);
> (BE-129)–(BE-133) in full; (BE-134)(ii)/(iii); (PENCIL-SATURATES-CHART)
> itself at side-degree `≥ 2`, which stays **OPEN**; **any** landed
> measurement. **Not a PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 1 — a NAMED GAP DISSOLVES.** (BE-134)(i) is a write-up gap:
  the `k ≥ 2` sweep is **proved** and **constructed**, 411/411
  ((BE-136)).
- **HIT shape 2 — an EXACT CLASSIFICATION where a hazard stood.** Gap (ii)
  becomes three closed-form memberships, each an **iff** ((BE-138)).
- **HIT shape 3 — a SUCCESSOR REFUTED AS STATED.** The reduction is uniform
  in `k`, so *"keep `xc₂…xc_k`"* buys nothing against `A` ((BE-137)(i)).
- **HIT shape 4 — a LANDED CONDITION SHOWN TOO STRONG.** `(∗)` is
  sufficient, not necessary; the β-ruling separates them and no sampler
  could see it ((BE-137)(iii)).
- **HIT shape 5 — THE OBSTRUCTION IS LOCATED, AND IT IS THE METHOD.** The
  pendant edge's **free multiplier** is what makes `A` `p_x`-free; at
  `k ≥ 2` it is determined, and the sharp object moves with `p_x`
  ((BE-139)).
- **A partial result, not a full one — say so.** (BE-139)(i) is
  driver-checked at `k = 2` only; the general-`k` consistency conditions
  are stated and not exercised. (BE-138)(iv)'s `dim B = 3` branch is a
  statement over `ℚ̄` in one step of its argument (a plane meets every line
  of `P³`, which is field-free) but its *converse* corner at `dim B = 2`
  uses that a line meets `Q` in `≤ 2` points, which needs only that the
  field be infinite — recorded rather than assumed.
- **NOT HIT** — **(PENCIL-SATURATES-CHART) at side-degree `≥ 2` is still
  OPEN**, and this direction makes it no closer: what is delivered is a
  **located obstruction** plus a named method change, not the clause.
- **The price, stated as a price.** **(a)** The verdict is architectural:
  a *different* method could still close item 1, and (BE-139)(iv) names
  what it would have to do. **(b)** `A_sharp` is defined and measured but
  **no properness statement is proved for it** — that is the successor.
  **(c)** Every population is **CONSTRUCTED** — one skeleton (`K₃,₃`), one
  branch profile (all 3s), 27 + 8 sides — and every "N/N" is a statement
  about them under seed `20260902`. **(d)** `k ∈ {2,3,4}` only; the
  `k ≥ 3` rows all have the `c_j` non-collinear, so the collinear corner
  (where `π_x` regains a pencil) is **unsampled**. **(e)** No chart point
  realizes any of (BE-138)'s memberships, so the criteria are **exact but
  unwitnessed on a chart** — the same disclosure (BE-134)(ii) made.
  **(f)** Everything downstream of (CH-1)/(CH-2) inherits their
  **proven-informally** status. **(g)** Exact ℚ only; the proofs use rank
  arithmetic and Segre/Klein incidence and are characteristic-free, the
  numerics are not.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py sweep      #    4.9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py exact      #   10.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py fibrebad   #    1.1 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py sharp      #   18.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py direct     #  194.1 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py support    #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdegtwo.py validate   #  228.7 s (all six)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single
seed is `20260902` (`bunif.SEED`), printed by every mode; `validate` fits
the 600 s foreground budget. **Every headline is an `assert`, and each
headline's own driver is named:** (CH-1) at 35/35 composites and 411/411
targets rebuilt into legal chart points with the core asserted unchanged,
`π_x` asserted to carry the fixed side-`i` star and the fibre asserted
unchanged under its own sweep, over all four fibre shapes (`sweep`);
`Π_x = p_x ∧ L_{jk}` at 288 pairs, `dim A ≥ 5 ⟹ Bad = P³` at 300 draws,
`(∗) ⟹ Bad ≠ P³` at 300, the α- and β-rulings **constructed** 30 each, and
BLINE's 270 rows re-decided exactly (`exact`); the three fibre criteria as
**iffs** at 300 draws each, every branch separately planted (`fibrebad`);
the exact `k = 2` structure as a **subspace identity** at 162/162 with the
`(dim A, dim A_sharp)` census (`sharp`); the clause and the relaxed
condition at all 411 swept chart points with `margin ≤ 0` asserted at 70
(`direct`); the §4 support audit (`support`).

**Where each headline's own sampler can and cannot see** (`RESEARCH-ARC.md`
§4's BSATUR sharpening, applied to this direction's own drivers):

1. **`sweep` is a CONSTRUCTION, not a sample.** It varies the target `p_x`
   inside its own fibre and holds the whole core byte-fixed; the **four
   fibre shapes are enumerated from the tower** ((BE-136)(ii)), not
   discovered by drawing, and the driver's job is only to show each is
   inhabited by a legal chart point. It reaches the existence quantifier
   and no other.
2. **`exact` (a) reaches the PAIR quantifier exhaustively** — all
   `C(k,2)` pairs at every row — and the configuration only by sampling.
   Its (b)/(c) draws `A` uniformly from `[−9,9]`, a support that **misses
   every ruling**, all of which are proper closed; that is exactly why
   both rulings are **built**. The `Bad = P³` test itself is **exact**
   (identically-vanishing quadratic forms), so it is not a sample at all.
3. **`exact` (d) reuses BLINE's support verbatim, on purpose**, because the
   claim is *about* that population; it inherits (BE-133)(v)'s caps in
   full — `deg_i(x) = 2` only, tree cores only.
4. **`sharp` varies the configuration and holds the `k = 2` shape at `x`
   fixed.** The identity is **proved**; the census is a sample and is
   quoted as one. It cannot see `k ≥ 3`.
5. **`direct` is the only population that varies `p_x` at a CHART point.**
   It holds the core, the skeleton and the seed set fixed, so it reaches
   the configuration quantifier **along one fibre** and does **not** reach
   the class. Its `0 of 411` is a **cap**, not a theorem — and, per the
   BSATUR sharpening, the clause it fails to find is quantified over
   objects (the core, the skeleton) it never varies.

### Caps, disclosed rather than smoothed — with the denominator named

1. **(BE-136), (BE-137)(i)/(ii)/(iii), (BE-138) and (BE-139)(i)/(ii) need
   no cap** — they are proofs; the driver can only falsify them.
2. **The clause's own violation is NOT FOUND under this cap** — 0 of 411
   swept chart points, 0 of 772 cumulatively at side-degree `≥ 2`. Never
   *"cannot happen"*.
3. **(BE-138)'s memberships are NOT FOUND at a chart point** — 0 of 96
   confined-fibre points, 0 of 411 overall. The criteria are exact; their
   chart-realizability is **open**, and (BE-134)(ii) said so first.
4. **`k ≥ 5` is unsampled**, and at `k ≥ 3` the **collinear-`c_j`** corner
   is unsampled (it is proper closed in the core, but it is where `π_x`
   regains a pencil and the fibre becomes 3-dimensional again).
5. **Non-tree cores are unsampled** in `sharp` and `exact` (d),
   inherited from (BE-133); `sweep` and `direct` do carry cyclic cores
   (`wide_library`'s ring-4 sides), which is new here.
6. **One skeleton, one profile.** Side 2 is always `K₃,₃` subdivided ×3,
   glued at two non-adjacent hubs — BPROPER's, BOPEN's and BLINE's own
   composite, unchanged, so nothing here varies the welded side.
7. **Everything inherits `bearcase.sample_piece_config`'s shape guard** and
   `bpeel.rnode_shaped`'s disclosed stand-in, unchanged from BSIGMA
   through BLINE.

### Harness note — `w4/bdegtwo.py`, and a SILENT `bimage.span` hazard

`w4/bdegtwo.py` imports `bline`, `bopen`, `bproper`, `bsigma`, `bsatur`,
`bunif`, `bdecor`, `bpeel`, `binduc`, `bimage`, `kbare_common` and
`exactcore` read-only and reimplements none of them: no `ρ̄`, no motion
space, no sampler, no peel constructor, no `slide`, no `(∗)`. It adds a
**fourth** consumer to `bproper.composite`/`core_of`, a **second** to
`bopen.chart_data`/`sides_of`/`slide` and to `bline.longcore_library`/
`rand_line`/`rand_subspace`/`star_ok`; no move-down is made, for BOPEN's
own recorded reason. Four new devices: `bdegtwo.fibre_k` (the `k ≥ 2`
fibre, from the tower), `bdegtwo.bad_on` (the exact identically-vanishing
minor test), `bdegtwo.sharp_data` ((BE-139)(i)'s exact structure) and
`bdegtwo.wide_library` (the `k ≥ 3` and two-hub-fibre sides).

**A hazard, recorded because it is silent and it is the same family as
BLINE's `pt_in` trap.** `bimage.span` is a `Λ²K⁴` helper: it special-cases
width 6 (`d == 6 → I6`) and otherwise returns `nullspace(nullspace(rows))`,
which is **empty — dimension 0 — on any FULL-RANK input whose width is not
6**. `span(I4)` is `[]`, and `dim(span(I4))` is `0`. `bimage.isect` shares
the defect through `perp_std`, which returns `I6` on an empty argument
regardless of the caller's width. It bit twice while this driver was written
(two fibre tests silently produced zero draws rather than failing). Every
`K⁴`-side rank test here therefore goes through `exactcore.rank`, and
`bdegtwo.k4span`/`k4meet` are the guarded wrappers. **New, unpaid**
harness-debt item: the right fix is a width parameter on `span`/`perp_std`,
which would touch every consumer and re-baseline their figures, so **no
move made**.

**No divergence is created.** `k4span`/`k4meet` are *guards* around
`bimage.span`/`isect`, not variants of them, and they are documented as
such at their definition.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-136)(i) the `k ≥ 2` equations at `q_x` | **PROVED** (read off (CH-2)'s tower, as (BE-124)(i) does) |
| (BE-136)(ii) the four fibre shapes | **PROVED**; all four **realized** as chart points |
| (BE-136)(iii) the rational completion | **PROVED**; **CONSTRUCTED** 411/411, core asserted fixed |
| (BE-137)(i) `Π_x = p_x ∧ L_{jk}`, pair-free | **PROVED**; asserted at 288 pairs |
| (BE-137)(ii) `dim A ≥ 5 ⟹ Bad = P³` | **PROVED** (one count), 300 draws |
| (BE-137)(iii) `(∗)` sufficient, not necessary | **PROVED**; both rulings **CONSTRUCTED**, 30 each |
| (BE-137)(iv) the recount on 270 rows | **MEASURED**; (BE-133)(ii) reproduced exactly, 2 recovered |
| (BE-138)(i) the components of `Bad` | **PROVED** (linear fibres of a projective incidence) |
| (BE-138)(ii) one-hub plane ⟺ `Π_{c₁} ⊆ A` | **PROVED**; asserted as an **iff**, 300, 137 planted |
| (BE-138)(iii) `k ≥ 3` plane ⟺ `dim(A ∩ Λ²π_x) ≥ 2` | **PROVED**; **iff** at 300, 150 planted |
| (BE-138)(iv) two-hub line, two branches | **PROVED**; **iff** at 300, both branches exercised |
| (BE-138)(v) the unified reading | **READING**, grounded in the three proofs |
| (BE-139)(i) the exact `k = 2` structure | **PROVED**; subspace identity asserted 162/162 |
| (BE-139)(ii) `k = 1` is degenerate; `A_sharp` moves | **PROVED** |
| (BE-139)(iii) `A_sharp` beats `A` at `dim A ≥ 5` | **MEASURED**, 30 of 162 |
| (BE-139)(iv) the architectural verdict | **VERDICT** — a negative about the *method*, not the clause |
| (BE-140)(i) the clause at 411 chart points | **MEASURED**, 0/411 — *not found under this cap* |
| (BE-140)(ii) the relaxation's cost | **MEASURED**, 28 of 70 peels wholly relaxed-bad |
| (BE-140)(iii) the confined fibres are clean | **MEASURED**, 0 of 96 |
| (BE-140)(iv) no shortfall at the 2-blocks | **MEASURED + ASSERTED**, 70 peels; item 0(c) stays OPEN |
| (BE-141)(ii) the coordinator's framing | **CONFIRMED as to the question, REFUTED as to the count** |

### What would change this

- **A properness statement for `A_sharp`** — i.e. for the `p_x`-varying
  locus `{p ∈ F : (p ∧ L_c) ∩ A_sharp(p) ≠ 0}` ((BE-139)(iv)). **This is
  the named successor**, and it is a *method* change: bounded-degree
  determinantal properness in a moving subspace, class-uniformly.
- **A chart point realizing one of (BE-138)'s three memberships**
  (`Π_{c₁} ⊆ A`, `dim(A ∩ Λ²π_x) ≥ 2`, `M ∧ t₀ ⊆ A`). That would upgrade
  gap (ii) from *exact-but-unwitnessed* to *realized*, and it is the
  cheapest thing on this list — the criteria are linear or a single
  intersection dimension.
- **A proof that `dim A_sharp ≤ 4` at every `k ≥ 2` terminal that an
  internal R-node peel presents.** That would put (BE-115)'s incidence lemma back in
  play with `A_sharp` in place of `A`, and (BE-139)(iii)'s 30 rows say it
  is not obviously false — but (BE-133)(iii)'s semicontinuity argument runs
  the other way for `A`, so it would have to be a statement about the
  *induction's* peels.
- **The general-`k` form of (BE-139)(i)**, with the consistency conditions
  `a_2 = ⋯ = a_k` exercised; cheap, and it is a stated cap here.
- **A row with `Π_x ⊆ ρ̄_i` and `ρ_i ≤ 5`** — still unexhibited, now after
  411 further *chart* points (0 of 772 cumulatively), and it would be a far
  bigger event than anything here.
- **A defect in (CH-1) or (CH-2)**, on which everything here stands.

## TERMINATION check (E1/E2/E3) — read at source, decided explicitly

Read at `notes/pencil/fanout-archive.md` (the ledger's own statement, not by
analogy), each decided:

- **(E1)** — *a g-flank: a `D = 0` shape whose every admissible colouring is
  binding, refuting per-shape (GR-15)*. **DOES NOT FIRE.** This direction is
  on the `(K-bare)` line and exhibits no colouring object at all; (GR-15) is
  untouched.
- **(E2)** — *the target is refuted or unprovable-as-posed **and** no ledger
  entry is left open-with-a-named-dispatchable-attack*. **DOES NOT FIRE**,
  on **both** conjuncts: what is reported is an **architectural** negative
  about one route to one clause of half (B) — not about the target — and the
  residue ((BE-139)(iv)'s properness statement for `A_sharp`, and
  (BE-138)'s three memberships as a chart-realizability hunt) is a named,
  dispatchable attack. *The clause `notes/Phase39.md` item 0(a) carries is
  OPEN, unrefuted, and unviolated at 772 rows.*
- **(E3)** — *the target is **proven** and every remaining ledger entry is
  adjudication-gated rather than dispatchable*. **DOES NOT FIRE**: nothing
  is proven that was open, (BE-14), `hbareSplit` and `hK` are untouched,
  and dispatchable entries remain.

**Per the "otherwise" clause the natural next step is a further direction**;
this landing does not prep one. See `notes/Phase39.md` *Hand-off*.
