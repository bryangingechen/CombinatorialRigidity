## §(K-bare-ext), continued — direction BARCH: **THE `p_x`-FREE SUBSPACE METHOD IS NOT DEAD AT SIDE-DEGREE `≥ 2` — IT CHANGES AMBIENT — AND 14 → 12 SURVIVES THE CLAUSE'S LOSS** (*Steps BE148–BE154*)

**Both maps the route uses are `p_x`-free, and (BE-139) used only one of
them.** At `deg_i(x) = k ≥ 2` the exact space is
`ρ̄_i = {s(m) + a(m)ℓ₁ : m ∈ r^{-1}(Π_x)}` ((BE-139)(i)), with
`s(m) = m(y) − m(c₁)` and `r(m) = m(c₁) − m(c₂)`. **Both `s` and `r` are
linear maps on the core's motion space `M°`, and `M°` does not contain `x`** —
so both are `p_x`-free, and so is their **graph**
`Γ := {(s(m), r(m)) : m ∈ M°} ⊆ V ⊕ V`, `V := Λ²K⁴`, a **fixed** subspace of
a **fixed** 12-dimensional ambient. Writing `ψ_p` for the `ℓ₁`-coordinate
functional on `Π_x(p)` and `φ_p(u, w) := u + ψ_p(w)ℓ₁`,
**`ρ̄_i(p) ∩ Π_x(p) = φ_p(Γ ∩ (Π_x(p) ⊕ Π_x(p)))` EXACTLY** — asserted as an
identity of **subspaces** at **99/99** rows — so the clause **is** the
statement that `φ_p` is **surjective**, i.e. a condition on the **point** `p_x`
against the **fixed** subspace `Γ`. Hence (BE-139)(iv)'s *"provably
unavailable at `k ≥ 2`"* is **right inside `Λ²K⁴` and over-scoped as
written**: what the pendant multiplier buys at `k = 1` is not the *existence*
of a `p_x`-free subspace, it is that the `p_x`-free subspace lives in the
**same 6-dimensional ambient where (BE-115)'s incidence lemma does**.
**And there is a second `p_x`-free subspace in `V` itself, which the route
never named:** `R := r(M°) = ρ̄(core; c₁, c₂)` and its sharper sibling
`R₀ := r(ker s)`, for which the clause forces
**`ℓ₁(p) ∈ A` or `Π_x(p) ∩ R₀ ≠ 0`** — a `V`-level certificate that fires at
**every** row with `dim A ≤ 5` (63 of 99, asserted **sound** at 63/63) and at
no row with `dim A = 6`. **The structural reason `A` saturates and `R` does
not** is a **path bound**, proved and asserted at 99/99: `ρ̄(H; u, v)` sits
inside the span of the hinge lines of *any* `u–v` path, so
`dim R ≤ dist_core(c₁, c₂)` — the distance between **two neighbours of the
same vertex** — while `dim A ≤ dist_core(c₁, y)`, the distance to the **far**
terminal. **The graph condition then does what neither `A` nor `R₀` can**:
`dim Γ_Π(p) ≤ 1` **proves GOOD** at `p`, and along the fibre it fires on
**39 of the 54** configurations where the relaxed condition `Π_x ∩ A ≠ 0`
holds at **every** swept point — 18 of them at `dim A = 5` and **21 at
`dim A = 6`, where even the `V`-level certificate is vacuous**. **AND
QUESTION 2 SPLITS TWO WAYS.** Weakening (PENCIL-SATURATES) **per side** is
**dead**: over the whole 6 400-tuple enumeration the floor family
`c_i(Π_x) = 2 ⟹ ρ_i ≥ f` leaves **313 / 164 / 74 / 24 / 0** escapes at
`f = 2/3/4/5/6`, so the landed clause is the **weakest member of its own
family** that delivers 14 → 12, and relaxing it to BSATUR's own threshold
`ρ_i ≥ 5` still leaves 24. But a **two-sided** clause does it: **(E4)**
`c_i(Π_x) = 2 ⟹ e₁ + e₂ ≥ 4`, with `e_i := ρ_i − c_i(Π_x)`, leaves **0**
escapes, is **implied by** (PENCIL-SATURATES) (0 counterexamples) and
**strictly weaker** (970 separating tuples), keeps (BE-101)(ii) intact at
`a₁ = a₂ = 0`, and **holds at BSATUR's own recorded witness** — because that
refutation exhibits **one side**, and a per-side witness cannot refute a
statement about the **pair**. **Nothing is refuted**: (BE-139)(i)/(ii)/(iii)
are reproduced, (BE-140)'s every figure stands, and the clause itself stays
**OPEN**

### Standing notation (on top of *Steps BE135–BE140*)

BDEGTWO's, verbatim — `x, y`, `deg_i(v)`, `core := side_i − x`,
`A := ρ̄(core; c₁, y)`, `ℓ_j := p_x ∧ p_{c_j}`, `Π_x := p_x ∧ π_x`,
`Σ_p := p ∧ K⁴`, `Λ²π`, `L_c := p_{c₁} ∨ p_{c₂}`, `F` the `p_x`-fibre,
`A_sharp := s(r^{-1}(Π_x))`, and BDEGTWO's *BAD* / *relaxed bad* reading
convention. Six more, all introduced here:

> **`V := Λ²K⁴`.** **`M°`** is the core's motion space
> (`binduc.motion_space` on `core`) — a **fixed** space, since `core` does not
> contain `x`. **`s(m) := m(y) − m(c₁)`** and **`r(m) := m(c₁) − m(c₂)`**, the
> two maps (BE-139)(i) already uses; `A = s(M°)`.
> **`Γ := {(s(m), r(m)) : m ∈ M°} ⊆ V ⊕ V`** is their **graph**, and
> **`Γ_Π(p) := Γ ∩ (Π_x(p) ⊕ Π_x(p))`** its cut. **`R := r(M°)`** and
> **`R₀ := r(ker s)`** are the two new `p_x`-free subspaces of `V`.
> **`e_i := ρ_i − c_i(Π_x) = dim((ρ̄_i + Π_x)/Π_x)`**, the per-side reach
> *out of* the pencil.
>
> **One reading convention, and it is the one BDEGTWO set.** *BAD* is the
> clause `Π_x ⊆ ρ̄_i` with `ρ_i ≤ 5`; *relaxed bad* is `Π_x ∩ A ≠ 0`. A third
> is added here: ***graph-bad*** is `dim Γ_Π(p) ≥ 2`, the necessary condition
> (BE-149)(iii) extracts. Every count below says which it counts.

### Step BE148 — (BE-149): the GRAPH — the clause is a condition on `p_x` against a FIXED subspace, in `V ⊕ V`

> **(BE-149)(i)** *(**PROVED**; the identity, and it is exact, not a bound)*
> Fix a chart point and a `p = p_x ∈ F`; write `Π := Π_x(p) = ⟨ℓ₁, ℓ₂⟩`
> (2-dimensional by `assert_generic_star` at `x`), let `ψ_p : Π → K` be the
> `ℓ₁`-coordinate functional in the basis `(ℓ₁, ℓ₂)`, and set
> `φ_p(u, w) := u + ψ_p(w)·ℓ₁` on `Π ⊕ Π`. Then
>
> > **`ρ̄_i(p) ∩ Π_x(p) = φ_p(Γ_Π(p))`, `Γ_Π(p) = Γ ∩ (Π ⊕ Π)`, `Γ` FIXED.**
>
> *Proof.* By (BE-139)(i), `ρ̄_i = {s(m) + a(m)ℓ₁ : m ∈ N}` with
> `N = r^{-1}(Π)` and `a(m) = ψ_p(r(m))`; `a` is linear on `N`, so that set is
> already a subspace and no span is taken.
> (⊇) Let `(u, w) ∈ Γ_Π`, say `u = s(m)`, `w = r(m)`. Then `w ∈ Π` gives
> `m ∈ N`, so `φ_p(u, w) = s(m) + a(m)ℓ₁ ∈ ρ̄_i`; and it lies in `Π` because
> `u ∈ Π` and `ℓ₁ ∈ Π`.
> (⊆) Let `v ∈ ρ̄_i ∩ Π`, say `v = s(m) + a(m)ℓ₁` with `m ∈ N`. Then
> `r(m) ∈ Π` and `s(m) = v − a(m)ℓ₁ ∈ Π`, so `(s(m), r(m)) ∈ Γ_Π` and `φ_p`
> sends it to `v`. ∎
>
> Asserted as an identity of **subspaces** *and* of dimensions, against
> `bimage.rho_bar_of`, at **99/99** rows over **33** shapes — BLINE's
> `longcore_library` (27) plus the **new cycle-7/8 corner** (6, *Step BE149*)
> — three coordinate scales each. At the same rows (BE-139)(i)'s own subspace
> identity is **reproduced** through `bdegtwo.sharp_data` (99/99), and the
> `(dim A, dim A_sharp)` census lands on **exactly the same 13 pairs**
> (BE-139)(iii) reports, with different multiplicities because the population
> differs: `{(1,1): 9, (2,1): 3, (3,1): 6, (3,2): 4, (3,3): 9, (4,2): 8,
> (4,3): 6, (5,3): 6, (5,4): 3, (5,5): 9, (6,4): 9, (6,5): 12, (6,6): 15}`
> (`barch.py graph`).

> **(BE-149)(ii)** *(**PROVED**; the clause IS a surjectivity statement)*
> Immediately from (i), since `dim Π_x = 2`:
>
> > **`Π_x(p) ⊆ ρ̄_i(p)  ⟺  φ_p : Γ_Π(p) → Π_x(p)` is SURJECTIVE.** ∎
>
> In the basis `(ℓ₁, ℓ₂)` of `Π`, writing `(u, w) = (u₁ℓ₁+u₂ℓ₂,
> w₁ℓ₁+w₂ℓ₂)`, `φ_p` is `(u₁, u₂, w₁, w₂) ↦ (u₁+w₁, u₂)`, so surjectivity is
> the statement that `Γ_Π(p)` is contained in no hyperplane
> `λ(u₁+w₁) + μu₂ = 0` — a **rank condition on a fixed subspace cut by a
> moving one**. Asserted, together with the agreement of the intersection
> test and `contains(ρ̄_i, Π_x)`, at 99/99.

> **(BE-149)(iii)** *(**PROVED**; the necessary condition, and it is the
> usable half)* Surjectivity onto a 2-space needs a 2-dimensional source, so
>
> > **BAD ⟹ `dim Γ_Π(p) ≥ 2`; equivalently `dim Γ_Π(p) ≤ 1` PROVES GOOD.** ∎
>
> Asserted at every row where the clause holds (vacuously here — the clause
> holds at none, consistent with (BE-140)(i)). The census over the 99 rows is
> `{0: 63, 1: 21, 2: 12, 3: 3}`: **15 rows are graph-bad**, and the other
> **84 carry a proof of GOOD from `Γ` alone**.

> **(BE-149)(iv)** *(**PROVED + ASSERTED**; `Γ` really is `p_x`-free)* `Γ` is
> built from `M°`, `s` and `r`, all functions of the core's points alone, so
> it cannot depend on `p_x`. Asserted as the exact analogue of the control
> (BE-114)(i) runs for `A` (`bproper.py reduce`'s 164 moves): at every row,
> `p_x` is re-drawn inside its own fibre (`bdegtwo.fibre_k`) with the core
> held fixed, and `Γ`'s **width-12 row space is asserted UNCHANGED** —
> `rank(Γ) = rank(Γ') = rank(Γ ∪ Γ')` — at **99/99** rows.

> **(BE-149)(v)** *(the reading, stated against (BE-139)(iv) and naming what
> is genuinely missing)* (BE-139)(iv) reads: *"the only `p_x`-free subspace on
> this route is `A`"*, hence *"a condition on a point against a **fixed**
> subspace … is **provably unavailable** at `k ≥ 2`"*. The first clause is
> **true of `Λ²K⁴`** — `A` is indeed the only `p_x`-free `s`-image in `V`, and
> `A_sharp` does move. The second **does not follow**, because the technique
> is not tied to that ambient: (i) exhibits the fixed subspace in `V ⊕ V`, and
> the equivalence is **exact**, not a relaxation. **So the verdict's scope is
> `Λ²K⁴`, and `w4/bdegtwo.py`'s own `sharp` verdict print states it without
> that scope.** What is genuinely unavailable is narrower and worth naming
> precisely: **an incidence lemma for `Γ` against the family
> `{Π_x(p) ⊕ Π_x(p) : p ∈ F}`** — the `V ⊕ V` analogue of (BE-115).
> Three facts fix how hard that is, all three **ASSERTED at 60/60 draws off
> the graphs entirely** — they are statements about `K⁴`, not about a side
> (`barch.py graph`, the geometry block).
> **(a) The family is very special, and classically so.**
> **`Π_x(p) = Σ_{p_x} ∩ Λ²π_x`** — the α-plane at `q_x` meets the β-plane of
> `π_x` in exactly the pencil, which is why (BE-114)'s `Σ` route and
> (BE-138)(iii)'s `Λ²π_x` route are two views of one object — and **`Π_x` is
> TOTALLY SINGULAR**, `Q ≡ 0` and `B ≡ 0` on it (any two lines through `q_x`
> inside `π_x` meet). So the missing lemma is about `Γ`'s intersections with
> **products of totally singular planes**, the geometry (BE-138)(v) already
> speaks in.
> **(b) One half of (BE-115) lifts and the other does not.** (BE-115)(i)'s
> mechanism does: for independent `p₁, p₂, p₃ ∈ π`,
> `Σ_{p₁}+Σ_{p₂}+Σ_{p₃} = V` gives `Σ_j (Σ_{p_j} ⊕ Σ_{p_j}) = V ⊕ V`, since
> the product summands are independent in each factor — **asserted at rank
> 12**. (BE-115)(ii)'s does **not**: its proof counts incidences on
> `S = P(A) ∩ Q`, and `Q` is a form on `V`, not on `V ⊕ V`. **That single
> lemma is the successor**, and it is a different downstream object from the
> four the wall has eaten.

### Step BE149 — (BE-150): the SECOND `p_x`-free subspace, and why `A` saturates while it does not

> **(BE-150)(i)** *(**PROVED**; the path bound, and it is general — not the
> ear case)* For any `u–v` path `P` in a side `H` and any motion `m`,
> `m(v) − m(u) = Σ_{(w,w') ∈ P} (m(w') − m(w))`, and each summand lies in
> `⟨ℓ_{ww'}⟩` by the hinge constraint (read at source,
> `kbare_common.build_rigidity` emits `perp_basis(C_e)` as `+wv`/`−wv`, i.e.
> exactly `m(w') − m(w) ∈ ⟨C_e⟩`; the same source reading (BE-114)(i) makes).
> Hence
>
> > **`ρ̄(H; u, v) ⊆ Σ_{e ∈ P} ⟨ℓ_e⟩` for EVERY `u–v` path `P`, so
> > `ρ(H; u, v) ≤ dist_H(u, v)`.** ∎
>
> Asserted as a **subspace containment** for **both** `(c₁, c₂)` and
> `(c₁, y)` at **99/99** rows. (BE-30) is the *ear* case of this and
> (BE-102)(i) records that it is an upper bound only; the general statement
> costs one line and is what the next item needs.

> **(BE-150)(ii)** *(the consequence, and it is the whole structural
> asymmetry)* `A = ρ̄(core; c₁, y)` and `R = ρ̄(core; c₁, c₂)` are relative
> screw spaces of the **same** core between **different** pairs, so
>
> > **`dim R ≤ dist_core(c₁, c₂)`  and  `dim A ≤ dist_core(c₁, y)`.**
>
> `dist_core(c₁, c₂) + 2` is the length of the shortest cycle through `x`
> using both `xc₁` and `xc₂`; `dist_core(c₁, y)` is the distance to the
> **far** terminal. **That is why `A` is vacuous where a generic chart point
> lives** ((BE-137)(ii): `dim A ≥ 5 ⟹ Bad = P³`) and `R` need not be: the
> library that makes `dim A` reach 6 is called `longcore_library` precisely
> because it lengthens the `c₁ → y` path, which does nothing to
> `dist_core(c₁, c₂)`. Measured `(dist_core(c₁,c₂), dim R)` over the 99 rows:
> `{(2,2): 27, (3,3): 27, (4,4): 27, (5,4): 1, (5,5): 8, (6,6): 9}` — the
> bound is **attained** at 98 of 99 (`barch.py two`).

> **(BE-150)(iii)** *(**PROVED**; the `V`-level necessary condition, from the
> `ℓ₁` component of surjectivity)* BAD gives `ℓ₁ ∈ ρ̄_i`, so there is
> `m ∈ N` with `s(m) + a(m)ℓ₁ = ℓ₁`, i.e. `s(m) = (1 − a(m))ℓ₁`. Split:
>
> - **`a(m) ≠ 1`:** `ℓ₁ = s(m)/(1 − a(m)) ∈ A`;
> - **`a(m) = 1`:** `s(m) = 0`, so `m ∈ ker s` and
>   `r(m) = ℓ₁ + b(m)ℓ₂ ≠ 0` lies in `Π_x ∩ r(ker s)`.
>
> Therefore
>
> > **BAD ⟹ `ℓ₁(p) ∈ A`  or  `Π_x(p) ∩ R₀ ≠ 0`,  `R₀ := r(ker s) ⊆ R`,**
>
> both conditions on the point `p` against a **fixed** subspace. ∎ And the
> same argument with the labels swapped (using
> `ρ̄_i = {s'(m) − b(m)ℓ₂ : m ∈ N}`, `s' = s + r`) gives the companion
> **BAD ⟹ `ℓ₂(p) ∈ A'` or `Π_x(p) ∩ r(ker s') ≠ 0`**, `A' := s'(M°)`.
>
> The contrapositive is a **certificate**, and it is asserted **SOUND** at
> every row where it fires: **63 of 99**, distributed by `dim A` as
> `{1: 9, 2: 3, 3: 19, 4: 14, 5: 18}` — i.e. **exactly the rows with
> `dim A ≤ 5`, including all 18 at `dim A = 5` where (BE-137)(ii) makes the
> relaxed condition vacuous**, and **none** of the 36 rows at `dim A = 6`.
> Note the second disjunct is `Bad(R₀)` in BDEGTWO's own notation
> (`Π_x(p) = p ∧ L_c`, (BE-137)(i)), so **(BE-129), (BE-137)(iii) and
> (BE-138) apply verbatim with `R₀` in place of `A`** — including the
> `2 + 5 > 6` count, which is why `dim R₀ ≤ 4` is what it needs.

> **(BE-150)(iv)** *(the two corners this certificate does **not** reach,
> stated before anything else)* **(a) `dim A = 6`.** Then `ℓ₁ ∈ A` for every
> `p` and the first disjunct is vacuous; the companion is vacuous too when
> `dim A' = 6`. Measured: it fires at **0 of 36** such rows. Only
> (BE-149)'s graph condition has content there — which is *Step BE150*.
> **(b) `dist_core(c₁, c₂) ≥ 5`.** Then `dim R` can saturate and `Bad(R₀)`
> goes vacuous by the same count that killed `A`. This is why the cycle-7/8
> shapes are added here: they are **unreachable in `longcore_library`** (all
> of whose rings are 4/5/6, so `dist_core(c₁,c₂) ≤ 4`), and they are the
> population that varies the claim's **own** variable past where it holds —
> 8 of their 18 rows sit at `dim R = 5` and 9 at `dim R = 6`.

### Step BE150 — (BE-151): what the graph certificate buys, measured ALONG the fibre

> **(BE-151)(i)** *(**MEASURED**; the comparison (BE-140)(ii) sets up)*
> (BE-140)(ii) is the quantitative form of the architectural verdict: on
> **28 of 70** peels the relaxed condition holds at **every** swept point, so
> the relaxation can prove properness **nowhere** there. Run the same shape of
> sweep with both certificates. Over **99** configurations and **783** swept
> fibre points (core held fixed, `p_x` re-drawn from `bdegtwo.fibre_k`, the
> hard gate `assert_generic_star` passed at every kept point):
>
> | | fires somewhere on the fibre | per-point bad |
> |---|---|---|
> | relaxed `Π_x ∩ A = 0` | **45** of 99 | 429 of 783 |
> | graph `dim Γ_Π ≤ 1` | **84** of 99 | 120 of 783 |
>
> and **on the 54 configurations where the relaxation fires nowhere, the
> graph certificate still fires at 39** — by `dim A`,
> `{5: 18, 6: 21}`. Both certificates are asserted **SOUND** at every point
> where they fire (663 graph firings). `barch.py cert`.

> **(BE-151)(ii)** *(the reading, and the honest limit)* The graph condition
> has content **exactly where the relaxation has none** — which is
> (BE-139)(iii)'s 30 rows, now with a **fixed** object behind them — and, the
> part (BE-150) cannot reach, **at `dim A = 6`** (21 of the 39). Combined
> with (BE-123)(i)'s constructibility and the irreducibility of `F`, a single
> `p ∈ F` with `dim Γ_Π(p) ≤ 1` **is a proof that BAD is proper in that
> fibre** — the (BE-52)/(BE-53) shape, one exact-ℚ witness. **What it is not
> is class-uniform:** it is decided per configuration, and **15 of 99**
> configurations have no firing point at all under this sweep, which is the
> honest residue. (BE-139)(iv) already conceded decidability per
> configuration; what this step adds is that the deciding object is
> **fixed**, so a class-uniform statement is now a statement about **one
> subspace `Γ` and one 3-parameter family of totally singular products**
> rather than about a moving `A_sharp`.

### Step BE151 — (BE-152): question 2, half one — WEAKENING (PENCIL-SATURATES) PER SIDE IS DEAD

> **(BE-152)(i)** *(**PROVED**; the arithmetic content of (BE-101)(i), named)*
> Let `e_i := ρ_i − c_i(Π_x)`. A `Π_x` failure is `c₁ + c₂ > 2 + slack`, so
>
> > `ρ₁ + ρ₂ = (c₁ + c₂) + (e₁ + e₂) > 2 + slack + (e₁ + e₂)`,
>
> and therefore **`e₁ + e₂ ≥ 4` forces the `U = Λ²K⁴` inequality to fail**
> too, which is (BE-101)(i)'s conclusion. ∎ Conversely every tuple that
> **escapes** (fails at `Π_x`, holds at `Λ²K⁴`) has `e₁ + e₂ ≤ 3`: asserted
> over the whole enumeration, histogram
> `{0: 21, 1: 58, 2: 114, 3: 120}` on the 313 escapes. So `e₁ + e₂ ≥ 4` is
> **exactly** the arithmetic the redundancy theorem needs, and
> (PENCIL-SATURATES) delivers it by the crudest possible route: `c_i = 2` and
> `ρ_i = 6` give `e_i = 4` on **one** side alone.

> **(BE-152)(ii)** *(**PROVED by exhaustion**; the per-side floor family, and
> it is dead below 6)* Over all **6 400** tuples the caps allow — the
> `ρ`-capped space of (BE-101)(iii), `bdouble.py arith`'s own — impose
> `(PS-f)`: `c_i(Π_x) = 2 ⟹ ρ_i ≥ f`, and count escapes:
>
> | `f` | 2 | 3 | 4 | 5 | 6 |
> |---|---|---|---|---|---|
> | escapes | **313** | **164** | **74** | **24** | **0** |
> | of which attaining (`a₁=a₂=0`) | 30 | 15 | 6 | 2 | 0 |
>
> Asserted, both the monotonicity and each endpoint. Hence
>
> > **(PENCIL-SATURATES) is the WEAKEST member of its own per-side family
> > that delivers 14 → 12.**
>
> In particular relaxing the floor to `ρ_i ≥ 5` — **exactly the threshold
> BSATUR's refutation sits at** ((BE-105)) — still leaves **24** escapes, **2
> of them in the attaining case S-mark's pin carries**. **This refutes the
> obvious fifth attempt before it is tried:** "the clause is false at
> `ρ_i = 5`, so weaken it to `ρ_i ≥ 5`" does not close 14 → 12.
> `barch.py arith`.

### Step BE152 — (BE-153): question 2, half two — a TWO-SIDED clause does it, and the landed refutations do not touch it

> **(BE-153)(i)** *(**PROVED**; the clause, stated failure-free)*
>
> > **(E4).** At an internal R-node peel, if `c_i(Π_x) = 2` for some side `i`,
> > then `e₁ + e₂ ≥ 4` — equivalently, the two sides' relative screw spaces
> > together fill the 4-dimensional quotient `Λ²K⁴/Π_x`. Same at `Π_y`.
>
> **(E4) ⟹ (BE-101)(i)'s conclusion.** *Proof.* A `Π_x` failure has
> `c₁ + c₂ > 2 + slack ≥ 2` with each `c_i ≤ 2`, so some `c_i = 2` and (E4)
> applies; then (BE-152)(i) gives the `Λ²K⁴` failure. ∎ Asserted by
> exhaustion: **0** escapes over all 6 400 tuples.
>
> **The form matters and is the trap.** Stated as *"at every peel where the
> `Π_x` obligation fails, `e₁+e₂ ≥ 4`"* the condition is **logically
> equivalent to the conclusion** at `a₁ = a₂ = 0` (there the `Λ²K⁴`
> inequality always holds, so it would say *"`Π_x` never fails"*). The
> hypothesis must be `c_i(Π_x) = 2` — **the same hypothesis
> (PENCIL-SATURATES) has** — which is what makes (E4) a clause and not the
> target restated. Recorded because it is exactly the kind of circularity
> (BE-142) struck one step earlier in this section.

> **(BE-153)(ii)** *(**PROVED by exhaustion**; strictly weaker, and 14 → 12
> survives)* Over the same enumeration:
>
> - **(PENCIL-SATURATES) ⟹ (E4)** at every `Π_x`-violating tuple —
>   **0** counterexamples, asserted;
> - **(E4) holds where the clause fails** at **970** violating tuples, so the
>   implication is **strict**; the three smallest by `ρ₁+ρ₂` are
>   `(δ,a,ρ,c) = (0,0 | 2,5 | 2,5 | 1,2)`, `(0,0 | 2,5 | 2,5 | 2,1)` and
>   `(0,0 | 3,4 | 3,4 | 1,2)`;
> - **(BE-101)(ii)'s corollary survives**: under (E4) there are **0** `Π_x`
>   violations at `a₁ = a₂ = 0`, asserted — so **14 → 12 stands with (E4) in
>   place of (PENCIL-SATURATES)**, and half (B)'s live block list is 12
>   without the clause the wall has eaten four attempts at.

> **(BE-153)(iii)** *(**ASSERTED at (BE-104)(i)'s own numbers**; a per-side
> witness cannot refute a two-sided clause)* (BE-104)(i) records its
> refuting peel exactly: `δ = (5,3)`, `a = (0,0)`, `c₁(Π_x) = 2` at
> `ρ₁ = 5`, `c₂(Π_x) = 0`. Then `e₁ = 5 − 2 = 3` and `e₂ = 3 − 0 = 3`, so
>
> > **`e₁ + e₂ = 6 ≥ 4`: (PENCIL-SATURATES) FAILS and (E4) HOLDS at the very
> > configuration that killed the clause.** Asserted, together with the check
> > that the witness is **not** a shortfall (`c₁+c₂ = 2 ≤ 2 + slack = 4`,
> > (BE-100)'s reading).
>
> **Why this is structural and not luck.** BSATUR's refutation, BSIGMA's
> refutation of `-GEN`, and BLINE's `dim A ≥ 5` stratum are all statements
> about **one side's** screw space at **one** terminal; (E4)'s content at the
> hard corner is that the **other** side is not swallowed by the pencil
> (`ρ_j > c_j(Π_x)`, i.e. `ρ̄_j ⊄ Π_x`, which needs `ρ_j ≤ 2`). A per-side
> witness therefore does not refute it — refuting it requires exhibiting
> **both** sides at once.

> **(BE-153)(iv)** *(**PROVED by exhaustion**; and patching BSATUR's corner
> alone is NOT enough)* The minimal patch of exactly the refuted corner —
> *"`c_i = 2` and `ρ_i = 5` ⟹ `ρ_j > c_j(Π_x)`"* — leaves **287** escapes,
> asserted. So the two-sidedness has to be carried at **every** `ρ_i`, not
> only at 5; (E4) is the statement that works and the patch is not.

> **(BE-153)(v)** *(what (E4) would take to prove, and where it is NOT
> sourceable)* `e_i = ρ_i − c_i(Π_x)` is expressible in **exactly** the four
> numbers `(ρ₁, ρ₂, c₁(Π_x), c₂(Π_x))` that (BE-96)(ii)'s block law reads, so
> (E4) lives inside the landed reach machinery's own variables. But that
> machinery runs the **wrong way**: (BE-95)(i) **caps** `reach` from above and
> (BE-96)(i)/(ii) show the cap **attained**, whereas (E4) is a **lower** bound
> on each side's reach *out of* `Π_x`. **No landed lemma bounds `e_i` from
> below.** Two cheap consequences worth recording as the target's shape:
> `e_i ≥ ρ_i − 2` always, so **(E4) is automatic whenever `ρ₁ + ρ₂ ≥ 8`**;
> and at `c_i = 2` it reads `ρ₁ + ρ₂ ≥ 6 + c_j(Π_x)`. **(E4) is therefore
> UNREFUTED and UNPROVED**, and it is a *different* object from the clause —
> not a fifth repair of it.

### Step BE153 — (BE-154): the verdict on the method class, and the §8 bar

> **(BE-154)(i)** *(the answer to question 1)* **NO — the `p_x`-free-subspace
> method class does not die at `k ≥ 2`.** What dies is the method class
> *inside `Λ²K⁴`*, and (BE-139)(iv) proves exactly that. In `Λ²K⁴ ⊕ Λ²K⁴` the
> technique (BE-114)(iii) names is available and the reduction is **exact**
> ((BE-149)); inside `Λ²K⁴` itself a **second** `p_x`-free subspace exists
> ((BE-150)) and covers every `dim A ≤ 5` row. **The correction to record is
> a SCOPE, not a refutation:** (BE-139)(iv)'s mathematics stands, its
> universal quantifier does not.

> **(BE-154)(ii)** *(the answer to question 2)* **YES — the 12-block residue
> is reachable without (PENCIL-SATURATES-CHART), but not by weakening it.**
> The per-side floor family is dead below the landed clause ((BE-152)); the
> two-sided **(E4)** delivers 14 → 12, is strictly weaker, and survives the
> per-side refutations at their own witnesses ((BE-153)). The 12 blocks
> (BE-97)(iv) calls **unwitnessed-not-excluded** are untouched by this and
> stay so — this step changes only what the *reduction to 12* costs.

> **(BE-154)(iii)** *(**the §8 bar, and it LIFTS — narrowly, with the
> reason recorded here**)* `notes/Pencil-strategy.md` §8 bars, as a build,
> *"`A_sharp` properness — or any further single-clause repair of
> (PENCIL-SATURATES-CHART) at side-degree `≥ 2`"* until this recon runs, the
> reason being that four structurally-different attempts hit **one** named
> obstruction and the recurring-wall rule says suspect the shared
> **downstream** object. The recon's finding is that the shared downstream
> object **was** `A ⊆ Λ²K⁴`, and that two different ones are available. So:
>
> - **STAYS BARRED — `A_sharp` properness as posed.** (BE-149) explains why
>   it must fail *as a fixed-subspace argument in `Λ²K⁴`*: `A_sharp(p)` is
>   `p_x`-dependent by construction, and `A` is the only `p_x`-free
>   `s`-image. Pricing it as a candidate inside the method question, as §8's
>   bar asks: **it is the worst of the three**, because it is the one that
>   keeps the refuted downstream object.
> - **LIFTS for `Γ`-properness** — the single lemma (BE-149)(v) names:
>   properness of `{p ∈ F : dim(Γ ∩ (Π_x(p) ⊕ Π_x(p))) ≥ 2}`, i.e. an
>   incidence lemma for one **fixed** subspace of `Λ²K⁴ ⊕ Λ²K⁴` against a
>   3-parameter family of products of **totally singular** 2-spaces. This is
>   a **new downstream object**, which is precisely what the recurring-wall
>   rule asks for, and (BE-151) shows it already decides 84 of 99
>   configurations and 39 of the 54 the relaxation cannot touch.
> - **LIFTS for (E4)** — substituting a **two-sided** clause for the per-side
>   one in (BE-101), which is likewise a new object and is the cheaper of the
>   two: (BE-152)/(BE-153) are already exhaustive on the arithmetic, so what
>   remains is the geometry of a single lower bound on `e₁ + e₂`.
>
> **The cheapest decisive next move is a falsification, not a proof**:
> exhibit a peel with `c_i(Π_x) = 2` and `e₁ + e₂ ≤ 3` — both sides' screw
> spaces nearly inside the pencil at `x`. That needs `ρ_i ≤ 5` **and**
> `ρ_j ≤ c_j(Π_x) + (5 − ρ_i)`, so on BSATUR's own `ρ_i = 5` witness it needs
> `ρ̄_j ⊆ Π_x` outright, i.e. `ρ_j ≤ 2`. **If that configuration exists,
> (E4) dies and the bar should come back down for the whole clause family.**

> **(BE-154)(iv)** *(the smallest concrete successor, named as one commit)*
> Not the lemma — the **hunt**: extend `barch.py`'s `cert` sweep to
> composite **chart** points (`bdegtwo.sweep_points`, which reaches all four
> fibre shapes and 411 targets) and, at each, evaluate `dim Γ_Π(p)` and
> `(e₁, e₂)` at **both** sides of the peel. That is one driver mode against
> a landed generator, it decides (E4) by falsification if it is false, and it
> is the population (BE-151) explicitly does **not** reach.

### Step BE154 — (BE-155): the price, the board, the reading, the E-rider

> **(BE-155)(i)** *(**the board**)* **What moved.** The architectural verdict
> is **scoped**: the fixed-subspace technique is available at `k ≥ 2`, in
> `V ⊕ V`, with an **exact** identity ((BE-149)); a **second** `p_x`-free
> subspace `R₀ ⊆ R = ρ̄(core; c₁, c₂)` is named, with a **general path bound**
> explaining the `A`-saturation ((BE-150)); a properness certificate with
> content at `dim A = 6` is measured against (BE-140)(ii)'s own comparison
> ((BE-151)); and **14 → 12 is detached from (PENCIL-SATURATES)** — the
> per-side floor family **dead below 6** ((BE-152)), the two-sided **(E4)**
> sufficient, strictly weaker, and unrefuted by the four landed per-side
> witnesses ((BE-153)). §8's bar **lifts for two named new objects and stays
> down for `A_sharp` in `Λ²K⁴`** ((BE-154)).
> **What did not move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, (GR-15),
> (BE-14), the 2-cut step, S-mark, half (β), class uniformity, cross-pair
> welding, the 12 unwitnessed blocks ((BE-97)(iv)), `⟨M⟩` — all untouched.
> **(PENCIL-SATURATES-CHART) itself stays OPEN.** No shortfall is exhibited;
> **no landed measurement is refuted** — (BE-139)(i)'s subspace identity and
> (BE-139)(iii)'s 13 `(dim A, dim A_sharp)` pairs both reproduce.

> **(BE-155)(ii)** *(**the coordinator's reading**, classified —
> `RESEARCH-ARC.md` §7)* The spec offered **no prediction on the
> mathematics**; it offered a **framing** — *"BDEGTWO's mechanism is that
> what made `A` `p_x`-free is gone by construction, so say whether the method
> class is dead"* — and an **evidence-stratum declaration** naming the four
> attempts and the recurring-wall rule. **Verdict: the framing is CONFIRMED
> as to which object to examine and REFUTED as to the answer it expected.**
> The spec's own words *"if what made `A` `p_x`-free is gone by construction,
> say whether the method class is dead"* contain the error: what is gone by
> construction is `A`'s *sufficiency*, not the *existence* of a `p_x`-free
> object — and the spec's likeliest-deliverable line (*"another
> method-is-dead negative"*) is the half that was wrong. **What the spec got
> right, and it is the transferable part:** it forbade posing the question as
> *"is `A_sharp` proper"*, and that reframing is what made the ambient
> visible; had the dispatch been sent at the narrow question it would have
> been the fifth attempt. **Tally:** §7 stands at **eighteen instances and
> eight kinds**; this landing **cites and does not increment it** (the
> 2026-09-02 concurrent-counter finding), and offers the coordinator one
> **candidate kind — SCOPE-REFUTED**: a landed verdict whose mathematics is
> sound and whose quantifier is not, where the recon's whole yield is the
> missing scope word. Whether that is a kind or simply §7 working is the
> coordinator's call.

> **(BE-155)(iii)** *(classification, mandatory and explicit)* **What is
> proved**: (BE-149)(i)/(ii)/(iii)/(iv), (BE-150)(i)/(ii)/(iii),
> (BE-152)(i)/(ii), (BE-153)(i)/(ii)/(iv), and (BE-149)(v)'s three
> Klein-geometry facts (`Π_x = Σ_{p_x} ∩ Λ²π_x`, total singularity,
> (BE-115)(i)'s lift), each asserted at 60/60. **What is measured, not
> proved**:
> (BE-149)'s censuses, (BE-150)(ii)'s attainment count and (iii)'s firing
> rate, (BE-151)(i) in full. **What is asserted at a cited source's own
> numbers**: (BE-153)(iii), at (BE-104)(i)'s recorded `δ/a/ρ/c`. **What is
> constructed**: the cycle-7/8 corner shapes (`barch.wide_cycle_library`),
> which exist to vary `dist_core(c₁,c₂)` past where (BE-150) holds.
> **What is cited**: (BE-30), (BE-52)/(BE-53), (BE-95)(i), (BE-96)(i)/(ii),
> (BE-97)(iv), (BE-100), (BE-101)(i)/(ii)/(iii), (BE-102)(i), (BE-104)(i),
> (BE-105), (BE-113), (BE-114)(i)/(iii)/(iv), (BE-115)(i)/(ii),
> (BE-123)(i), (BE-129), (BE-137)(i)/(ii)/(iii), (BE-138)(v),
> (BE-139)(i)/(ii)/(iii)/(iv), (BE-140)(i)/(ii), (BE-142), (CH-1), (CH-2) —
> all landed. **What is refuted**: (BE-139)(iv)'s *"provably unavailable"* as
> an unscoped claim, and the per-side weakening of (PENCIL-SATURATES) as a
> route to 14 → 12. **What is NOT refuted**: `PencilPair K 3 G`;
> `hbareSplit`; (BE-14); half (B); S-mark; (BE-127)(i); (BE-139)(i)/(ii)/(iii);
> (BE-140) in full; (PENCIL-SATURATES-CHART) itself, which stays **OPEN**;
> **any** landed measurement. **Not a PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 1 — A LANDED VERDICT IS SCOPED.** (BE-139)(iv) is right in
  `Λ²K⁴` and unscoped as written; the exact reformulation in `V ⊕ V` is
  asserted at 99/99 ((BE-149)).
- **HIT shape 2 — A NEW OBJECT WHERE THE ROUTE SAID THERE WAS ONE.**
  `R₀ ⊆ R = ρ̄(core; c₁, c₂)` is a second `p_x`-free subspace, with a general
  path bound as the structural reason it stays small ((BE-150)).
- **HIT shape 3 — A CERTIFICATE WITH CONTENT WHERE THE RELAXATION HAS NONE.**
  39 of the 54 relaxation-blind fibres, 21 of them at `dim A = 6` ((BE-151)).
- **HIT shape 4 — A REPAIR REFUTED BEFORE IT IS TRIED.** The per-side floor
  family leaves escapes at every `f < 6`, including at BSATUR's own threshold
  ((BE-152)).
- **HIT shape 5 — THE CLAUSE IS REPLACEABLE, AND THE REPLACEMENT SURVIVES THE
  REFUTATIONS THAT KILLED IT.** (E4), exhaustively sufficient, strictly
  weaker, and holding at (BE-104)(i)'s own witness ((BE-153)).
- **A partial result, not a full one — say so.** (BE-149)/(BE-150) are
  driver-checked at **`k = 2` only**, inheriting (BE-139)(i)'s own cap. The
  general-`k` extension is mechanical and **not exercised**: with
  `r_j(m) := m(c₁) − m(c_j)`, all `ℓ_j ∈ Π_x`, so `r_j(m) ∈ Π_x` for every
  `j` and the multipliers are determined with `k − 2` extra consistency
  conditions on the `ℓ₁`-coefficient; `Γ` becomes the graph of
  `(s, r_2, …, r_k)` in `V ⊕ V^{k−1}` and (BE-149)(i) goes through against
  `Π_x^{⊕k}`. Stated, not driver-checked.
- **NOT HIT** — **(PENCIL-SATURATES-CHART) at side-degree `≥ 2` is still
  OPEN**, and (E4) is **unproved**. What is delivered is a **relocated**
  obstruction plus two named new objects, not the clause.
- **The price, stated as a price.** **(a)** Every certificate here is
  per-configuration; **class uniformity is untouched** and is the whole
  residue. **(b)** 15 of 99 swept configurations have no firing point under
  either certificate — the honest residue of (BE-151). **(c)** (E4) is
  unrefuted and unproved, and the landed reach machinery bounds reach from
  **above**, the wrong direction ((BE-153)(v)). **(d)** The two libraries are
  **CONSTRUCTED** and their cores are **TREES** (inherited from (BE-133) via
  `longcore_library`); every "N/N" is a statement about them under seed
  `20260902`. **(e)** `cert` sweeps at a **side** configuration, so only two
  of (BE-136)(ii)'s four fibre shapes are reached — `𝔸³` (72) and the plane
  `π_{c₁}` (27); the `k ≥ 3` plane and the two-hub line are **unsampled**
  here, and BDEGTWO's `sweep`/`direct` remain the stronger population.
  **(f)** No BAD row is exhibited anywhere in these populations (consistent
  with (BE-140)(i)'s 0/411 and the standing tally), so the certificates'
  soundness *asserts* are controls on GOOD rows; soundness itself is
  **proved** at (BE-149)(iii)/(BE-150)(iii). **(g)** `arith` is exhaustive
  over the **arithmetic** tuple space; whether a tuple is geometrically
  realizable is a separate question it cannot see — BDOUBLE's own caveat,
  inherited. **(h)** Everything downstream of (CH-1)/(CH-2) inherits their
  **proven-informally** status. **(i)** Exact ℚ only; the proofs use rank
  arithmetic and Klein incidence and are characteristic-free, the numerics
  are not.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py graph     #   41.4 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py two       #   11.9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py cert      #   62.9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py arith     #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py support   #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/barch.py validate  #  117 s (all five)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single seed
is `20260902` (`bunif.SEED`), printed by every sampling mode (`arith` prints it
and does not use it); `validate` fits the 600 s foreground budget with room.
**Every headline is an `assert`, and each headline's own driver is named:**
(BE-149)(v)'s three Klein-geometry facts at 60/60 draws off the graphs, the
`V ⊕ V` identity as **subspaces** plus the clause ⟺ surjectivity equivalence at
99/99, `Γ` asserted **unchanged** under moves of `p_x` inside its own fibre at
99/99, and (BE-139)(i) reproduced through `bdegtwo.sharp_data` (`graph`); the
path bound as a **subspace containment** for both vertex pairs at 99/99 and the
two-subspace certificate asserted **sound** at 63/63 (`two`); both certificates
asserted **sound** at every firing over 783 swept fibre points, with the
`assert_generic_star` gate passed at each (`cert`); the whole 6 400-tuple
enumeration — the floor family's five escape counts, (E4)'s 0 escapes,
`PS ⟹ (E4)` with 0 counterexamples, the 970-tuple separation, 0 attaining
`Π_x` violations under (E4), the 287-escape pair-patch, and (BE-104)(i)'s
witness satisfying (E4) — all `assert`ed (`arith`); the §4 support audit read at
source via `inspect.getsource` (`support`).

**Where each headline's own sampler can and cannot see** (`RESEARCH-ARC.md` §4's
BSATUR/RPOOL sharpening — population, support, and which of the **claim's own**
variables the population varies):

1. **`graph`'s identity is PROVED**; the driver can only falsify it. Its
   population varies the **configuration** (33 shapes × 3 coordinate scales
   `{3,5,9}`, one sampler: `bsigma.sample_side_config`) and, in the freeness
   control, **`p_x` inside its own fibre with the core held fixed**. It does
   **not** vary `k`: every row is `k = 2`, inherited from `longcore_library`.
   Its `dim Γ_Π` census is a sample.
2. **`two`'s path bound is PROVED.** Its census deliberately varies the
   claim's own variable `dist_core(c₁,c₂)` over `{2,…,6}` — the cycle-7/8
   shapes exist **only** to push it past where (BE-150)(iii) has content, and
   9 of 99 rows sit at `dim R = 6`, where it does not. The certificate's
   **firing rate** is a sample and is quoted as one; its **soundness** is a
   proof.
3. **`cert` varies `p_x` along the fibre at a SIDE configuration**, not at a
   composite chart point: it reaches the **fibre** quantifier and **not** the
   class, and every "fires at" count is a **cap**. It holds the skeleton, the
   core and the seed fixed, so — per the BSATUR sharpening — the class
   uniformity it cannot prove is quantified over objects it never varies.
4. **`arith` is an EXHAUSTIVE enumeration**, no sampling, no support, no seed
   used: it varies every variable its claims quantify over (`δ_i`, `a_i`,
   `c_i`, hence `ρ_i` and `e_i`) and is the only mode here that settles a
   universal. What it cannot see is **geometric realizability** of a tuple.

### Caps, disclosed rather than smoothed — with the denominator named

1. **(BE-149)(i)–(v), (BE-150)(i)–(iii), (BE-152), (BE-153)(i)/(ii)/(iv) need
   no cap** — they are proofs or exhaustions; the driver can only falsify them.
2. **`k = 2` only** in every geometric mode, inherited from (BE-139)(i); the
   general-`k` extension is stated and unexercised.
3. **Two of four fibre shapes** in `cert`: `𝔸³` and `π_{c₁}`. The `k ≥ 3`
   plane `π_x` and the two-hub line are **unsampled** here.
4. **15 of 99 configurations** are certified by neither test — not a
   counterexample, an unresolved cap.
5. **Tree cores only**; one sampler; coordinate scales `{3,5,9}`; seed
   `20260902`. The cycle-7/8 shapes add longer rings at `x` but the core is
   still a tree (deleting `x` opens the ring).
6. **`arith`'s space is arithmetic**, not geometric ((BE-101)(iii)'s
   `ρ`-capped tuple space); geometric realizability of an escaping tuple is
   not decided.
7. **(E4) is a new clause: UNREFUTED and UNPROVED.** Its falsification target
   is named at (BE-154)(iii) and is cheap.
8. **Everything inherits `bsigma.sample_side_config`'s independent-set guard
   and `binduc.assert_generic_star`**, unchanged from BSIGMA through BDEGTWO.

### Harness note — `w4/barch.py`, and three recorded hazards NAVIGATED

`w4/barch.py` imports `bdegtwo`, `bline`, `bproper`, `bsigma`, `bunif`,
`binduc`, `bimage`, `pitch` (`klein`/`Q`, for the geometry block) and
`kbare_common`, plus `exactcore`, taking the standing `w4/`
chain **eleven deep** (`barch → bdegtwo → bline → bopen → bproper → bsigma →
bsatur → … → kbare_common`). It adds a **fifth** consumer of
`bproper.core_of`, a **second** of `bdegtwo.fibre_k`/`fibre_kind`/`sharp_data`,
a **fourth** of `bline.longcore_library` and a **first** of `bline._arc` (a
private helper — recorded as such), plus the next consumer of
`bsigma.sample_side_config` and `binduc.assert_generic_star`/`motion_space`.
**All folded into the standing sibling-import item; NO MOVE MADE**, by the same
rule that forbids a dispatch from moving a landed name.

**It opens NO new hazard item, and all three recorded silent hazards were
navigated rather than fixed:**

- **`bimage.pt_in`'s `K⁴` truncation** — every call here is on a **width-4**
  fibre basis from `bdegtwo.fibre_k`, which is what `pt_in` is for. **No
  `Λ²`-side draw goes through it.**
- **`bimage.span`'s width-6-only special case** (the eleventh debt item, added
  at the BDEGTWO landing) — this driver is the first to work in a **width-12**
  ambient, where the defect has a **new face worth recording in the item**:
  `span(rows)` on width-12 input of rank **6** takes the `d == 6` branch and
  returns `I6`, i.e. a **width-6** answer to a width-12 question, still with no
  assert firing. `barch.py` therefore routes **every** 12-wide measurement
  through `exactcore.rank`, which is width-agnostic, and computes `Γ_Π` in
  `M°`-coordinates so no width-12 subspace is ever round-tripped. **A
  one-sentence addition to the existing item, not a new item** — same device,
  same unpaid fix (a width parameter on `span`/`perp_std`).
- **`bwin.dehom`'s list return** (BSCOND's *Recorded observation*) — `bwin` is
  **not imported**; `barch._aff3` returns a **TUPLE** for exactly that reason,
  and `support` asserts `assert_generic_star`'s `pt[u] != pt[v]` check present
  at source so the guard is live on every point this driver writes.

One new local device is named so it cannot be mistaken for a competitor:
**`barch.star_holds`** is the **soft** reading of
`binduc.assert_generic_star` (a `try`/`except AssertionError` wrapper, no
duplicated body), so a fibre draw landing on the guard's own locus is
**skipped** rather than crashing the sweep. Every row kept has passed the
guard as a hard assert. **No `Divergences` entry**: it is a wrapper around the
canonical gate, not a variant of it.

**Figures gate (`notes/scripts/README.md` *figures do not move*): DISCHARGED
BY THE ONE-LINE CHECK.** `git diff --name-only -- '*.py' '*.m2'` and
`--cached` are both **empty**, and `git status --porcelain notes/scripts/`
shows only the **addition** of `w4/barch.py`. A commit that only adds a driver
cannot move an existing figure; no baseline/re-run pairs are owed. Determinism
was checked anyway: two consecutive `PYTHONHASHSEED=0 … validate` runs are
**byte-identical apart from the driver's own timing lines**, the one documented
exception.

### E-rider (the (BE-14)/(GR-15) arc's exit test)

- **(E1)** — *a g-flank: a `D = 0` shape whose every admissible colouring is
  binding, refuting per-shape (GR-15)* (read at
  `notes/Pencil-fanout-archive.md`, the ledger's own statement). **DOES NOT
  FIRE**: this landing is on the `(K-bare)` line and exhibits no colouring
  object at all; (GR-15) is untouched.
- **(E2)** — the target refuted or unprovable-as-posed **and** no ledger entry
  left open with a named dispatchable attack. **DOES NOT FIRE on both
  conjuncts**: nothing is refuted but a *scope*, and this landing leaves two
  explicitly named dispatchable attacks ((BE-154)(iii)) plus a cheap
  falsification ((BE-154)(iv)).
- **(E3)** — the target proven and every remaining entry adjudication-gated.
  **DOES NOT FIRE**: nothing that was open is proven; (BE-14), `hbareSplit`
  and `hK` are untouched.

**Per the "otherwise" clause the natural next step is a further direction**;
this landing does not prep one, and names its own successor at
(BE-154)(iii)/(iv). See `notes/Phase39.md` *Hand-off*.
