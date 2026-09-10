## §(K-bare-ext) — continuation (direction BLONGARC): **THE DISPATCH'S QUESTION IS NO — AND THE LADDER EXTENDS ANYWAY, TWO RUNGS, TO A BOUNDARY THAT IS EXACT.** `rank(B|_U) ≤ 2` is **not** forced at arc length 4 (the rank is 4, and the arc supplies its own hyperbolic splitting, so (BE-193)(iv)'s warrant becomes **unconditional**); but the object was slightly wrong — `Π_x` already contains `ℓ_j`, so the containment lives in `U ∩ α_x` — and **one count, `dim(U ∩ α_x) = max(1, min(|arc|,6) − 3)`, subsumes (BE-190), (BE-191)/(BE-193) and two new rungs**, closing half (B)'s item 0(a) generically at arc `≤ 5` on **48 of 99** configurations and stopping at `|arc| = 6`, which is **(BE-189)(iii)'s own threshold** (*Steps BE195–BE202*)

**It opens at exactly the tail BRANKV declared** (*"THE LIVE TAIL IS NOW
(BE-196) / Step BE195"*), 0-hit verified at HEAD for `(BE-197)`–`(BE-203)`,
`BE-197`–`BE-203` and `BE196`–`BE202` (0 hits / 0 files each), with
`(BE-196)` **1 / 1**, `BE-196` **2 / 1** and `BE195` **1 / 1** — BRANKV's own
tail declaration, not a consumption. `BLONGARC`/`blongarc` were **0 / 0** as
raw substrings.

**THE DISPATCH'S QUESTION, ANSWERED FIRST AND NEGATIVELY.** At `|arc_j| = 4`
the Gram matrix of the Klein form on `(ℓ_j, ℓ_{cw}, ℓ_{wz}, ℓ_{zy})` has
determinant `(ac)²` with `a = B(ℓ_1, ℓ_3)`, `c = B(ℓ_2, ℓ_4)`, and
`rank(B|_U) = 2·rank([[a,b],[0,c]])` — **always even, never 3**, and equal to
**4** at 60 of 60 generic draws. `a` and `c` vanish exactly when four
*consecutive* arc bodies are coplanar, a proper closed condition that
`assert_generic_star` does **not** forbid (it forbids *collinearity* at a
body, strictly stronger). So `rank(B|_U) ≤ 2` is **not forced**, and the
coordinator's hypothesis and its stated reasoning are both **CONFIRMED**
((BE-197)). The named *tell* that would have refuted it — a graph-side
constraint keeping the form degenerate at every legal chart point — **does not
exist**: nothing in `(CH-1)`, `legal_peel` or `assert_generic_star` forces a
coplanarity of four consecutive bodies.

**AND (BE-193)(iv)'s WARRANT IS UPGRADED WHILE ITS CONCLUSION STANDS.** It
said a nondegenerate rank-4 form *"does admit totally singular 2-spaces (the
hyperbolic case)"* — true only **if** hyperbolic, which over `ℚ` is a
discriminant condition the sentence did not discharge. It is discharged for
free by the arc itself: consecutive hinge lines meet, so `⟨ℓ_1, ℓ_2⟩` and
`⟨ℓ_3, ℓ_4⟩` are **both totally singular** and `U` is their direct sum —
hyperbolic over **any** field, `rad(U) = 0`, with the totally singular
2-spaces forming exactly **two `P¹`-rulings** (300 members CONSTRUCTED and
each asserted totally singular and inside `U`). **The isotropic 2-plane the
dispatch asked to see exhibited is the arc's own consecutive pair
`⟨ℓ_1, ℓ_2⟩`** ((BE-198)).

**BUT THE OBJECT WAS SLIGHTLY WRONG, AND CORRECTING IT IS FREE.** `Π_x` is
the span of the **two** star lines at `x`, so `ℓ_j ∈ Π_x` **already** and

> **`Π_x ⊆ U` ⟺ `ℓ_{j'} ∈ U`,**

one membership rather than a 2-space embedding; and `Π_x ⊆ α_x := p_x ∧ K⁴`,
the 3-dimensional **totally singular** α-space of all lines through `q_x`, so
the containment lives in `U ∩ α_x` and nowhere else ((BE-196)). That is what
makes the radical argument's real habitat `U^{(1)} = U ∩ ℓ_j^⊥` rather than
`U` ((BE-199)) — and there it still bites, one rung further: at `|arc_j| = 4`
the quotient `Ū = U^{(1)}/⟨ℓ_j⟩` is a **hyperbolic rank-2 plane**, whose
isotropic cone is exactly **two lines**, so `Π_x` has exactly **two**
candidates — one demanding the collinearity `assert_generic_star` forbids at
`c`, the other forcing

> **`|arc_j| = 4` and `Π_x ⊆ ρ̄_i` ⟹ `q_z ∈ π_x` and `q_x, q_w, q_z, q_y`
> coplanar,**

`q_z ∈ π_x` being **one linear equation** of exactly (BE-193)(i)'s shape at
the arc's second-to-last body ((BE-200)).

**AND ONE COUNT SUBSUMES THE WHOLE LADDER.** Generically

> **`dim(U ∩ α_x) = max(1, min(|arc_j|, 6) − 3)`,**

asserted at every arc length 2–7. Since `Π_x ⊆ α_x` always, the containment
needs `dim(U ∩ α_x) ≥ 2` — **impossible** at a generic arc of length `≤ 4`,
**one linear condition** on the other side-neighbour at length 5, and
**automatic** at length `≥ 6`. So (BE-190) (arc 2), (BE-191)/(BE-193)
(arc 3), (BE-200) (arc 4) and the arc-5 closure are **four cases of one
count** ((BE-201)), the clause closes generically at every arc length `≤ 5`
— **48 of 99** landed configurations, against BRANKV's 15 — and the stop at
`|arc_j| = 6` is **(BE-189)(iii)'s own threshold**: `ρ_i ≤ dist` makes the
clause's conclusion `ρ_i = 6` *unreachable* at `dist ≤ 5`, so **the whole
path-bound family of arguments closes exactly the strata on which the clause
is VACUOUS and provably cannot reach the strata on which it has CONTENT**
((BE-202)/(BE-203)). That is the exact boundary the dispatch asked for, and it
is structural, not a cap.

**THE POINTWISE CLAUSE IS FALSE AT ARC 4 TOO.** BRANKV's (BE-192) witness one
arc-edge longer — three composite peels through `bline.legal_peel`,
configurations from `binduc.flat_config` — gives `c_i(Π_x) = 2` and
`ρ_i = 3` at **24 of 24** fully gated chart points, with `q_z ∈ π_x` at 24 of
24, so (BE-200)'s confinement is **proper and inhabited** rather than empty.
The witness is again **fully planar**, i.e. maximally degenerate, exactly
(BE-192)(iii)'s disclosure ((BE-200)(iv)).

**Nothing else landed is refuted.** (BE-127)(i)'s theorem at side-degree `1`,
(BE-149)–(BE-151), (BE-180)–(BE-187) and (BE-188)–(BE-195) all stand;
(BE-193)(ii)'s arc-`≤ 3` theorem is **subsumed, not corrected** — it is the
`n = 3` case of (BE-201) — and the 99 configurations, 783 points and 120
containments reproduce at the same seeds. What is **sharpened** is
(BE-193)(iv)'s warrant, and what is **corrected** is nobody's claim: the
dispatch's chosen span.

### Standing notation (on top of *Steps BE187–BE194*)

BRANKV's, verbatim — `arc_j`, `|arc_j|`, `W_j`, `rad(U)`, plus BGPROP's `V`,
`M°`, `Γ`, `Γ_Π(p)`, `Ω`, `A`, `A_sharp`, `Π_x`, `Σ_p`, `L_c`, `F`. Three
more, and the first is the one this direction turns on:

> **`α_x := p_x ∧ K⁴`** is the **α-space** at `q_x`: every line of `P³`
> through `q_x`, a 3-dimensional **maximal totally singular** subspace of
> `Λ²K⁴`, and `Π_x ⊆ α_x` for every configuration. **`ℓ_{j'}`** is the hinge
> line to the *other* side-neighbour of `x`, so `Π_x = ⟨ℓ_j, ℓ_{j'}⟩`.
> **`Ū`** is `(U ∩ ℓ_j^⊥)/⟨ℓ_j⟩` with its induced form.

### Step BE195 — (BE-196): the object, corrected — the containment is ONE membership inside the α-space

> **(BE-196)(i)** *(**PROVED**; the reduction)* At `deg_i(x) = 2`,
> `Π_x = p_x ∧ π̂_x = ⟨ℓ_{xc_1}, ℓ_{xc_2}⟩` — the span of the two star lines
> at `x` — which is how (BE-190)(i) itself reads it and how every landed
> driver builds it. Writing `ℓ_j = ℓ_{xc_j}` for the arc's first edge and
> `ℓ_{j'}` for the other, `ℓ_j ∈ Π_x` **identically**, so
>
> > **`Π_x ⊆ U` ⟺ `ℓ_{j'} ∈ U`.**
>
> The containment is a **single membership**, not a 2-space embedding. ∎
> Asserted at **40/40** independent arc-4 draws (both directions of the
> equivalence read, never one).

> **(BE-196)(ii)** *(**PROVED**; the α-space, and it is the load-bearing
> half)* Every nonzero element of `Π_x` is `p_x ∧ u`, a line through `q_x`,
> so `Π_x ⊆ α_x := p_x ∧ K⁴`. `α_x` is 3-dimensional and **totally
> singular** (any two lines through a common point meet), hence a *maximal*
> totally singular subspace of `Λ²K⁴`. Therefore
>
> > **`Π_x ⊆ U` ⟹ `Π_x ⊆ U ∩ α_x`, and `dim(U ∩ α_x) ≥ 2` is NECESSARY.** ∎
>
> Asserted at **144** draws across arc lengths 2–7 (`dim α_x = 3`,
> `rank(B|_{α_x}) = 0`).

> **(BE-196)(iii)** *(**PROVED**; the band, of which (BE-191)(i) is one case)*
> Along any arc, `Q(ℓ_k) = 0` (each generator is a line) and
> `B(ℓ_k, ℓ_{k+1}) = 0` (consecutive hinges share a body). So the Gram matrix
> of `B` on `(ℓ_1, …, ℓ_n)` has a **zero band** on the diagonal and the two
> adjacent off-diagonals, and in particular
>
> > **every consecutive pair `⟨ℓ_k, ℓ_{k+1}⟩` spans a totally singular
> > 2-space** — the pencil at the shared body in the plane of the three. ∎
>
> **CONSTRUCTED over the whole pair family, not sampled:** asserted at
> **225/225** consecutive pairs over **75/75** arcs of lengths 2–6, with
> `dim(span) = 2` and `rank(B|_{pair}) = 0` at each. (BE-191)(i)'s single
> off-diagonal entry is the `n = 3` instance of this band, and `dim U` is
> `min(n, 6)` at every generic draw (15 draws per length).

### Step BE196 — (BE-197): the dispatch's question — `rank(B|_U) ≤ 2` is NOT forced at arc 4

> **(BE-197)(i)** *(**PROVED**; the Gram matrix and its determinant)* Let
> `arc_j = (x, c, w, z, y)` and `U = ⟨ℓ_1, ℓ_2, ℓ_3, ℓ_4⟩`. By (BE-196)(iii)
> the band vanishes, so with `a := B(ℓ_1, ℓ_3)`, `b := B(ℓ_1, ℓ_4)`,
> `c := B(ℓ_2, ℓ_4)`,
>
> > **`G = [[0,0,a,b], [0,0,0,c], [a,0,0,0], [b,c,0,0]] = [[0, Y], [Yᵗ, 0]]`,
> > `Y = [[a,b],[0,c]]`,**
>
> whence **`det G = (det Y)² = (ac)²`** and **`rank(B|_U) = 2·rank(Y)`**. In
> particular the rank is **always even** — never 3 — and equals **4** exactly
> when `a ≠ 0` and `c ≠ 0`. ∎ Asserted at **60/60** generic draws
> (determinant identity, rank identity, rank ∈ {0,2,4}).

> **(BE-197)(ii)** *(**PROVED**; what the two vanishings MEAN)* `a = 0` says
> `ℓ_1` meets `ℓ_3`, i.e. **`q_x, q_c, q_w, q_z` coplanar**; `c = 0` says
> `ℓ_2` meets `ℓ_4`, i.e. **`q_c, q_w, q_z, q_y` coplanar**. Both are single
> determinantal equations on `Chart(H)`. ∎ Asserted as *equivalences*
> (`(a == 0) ⟺ rank[p_x,p_c,p_w,p_z] = 3`, likewise for `c`) at **60/60**.

> **(BE-197)(iii)** *(**THE ANSWER**, and it is NO)* `rank(B|_U) = 4` at
> **60 of 60** generic arc-4 draws, and `rank(B|_U) ≤ 2` is therefore a
> **proper closed** condition — the union of two coplanarity determinants —
> **not a forced one**. So (BE-191)(ii)'s radical argument has no radical to
> work with on `U`, exactly as (BE-193)(iv) predicted. ∎

> **(BE-197)(iv)** *(**the named TELL, and it FAILS**)* The dispatch named
> the one thing that would reverse this: *a graph-side constraint keeping the
> form degenerate at every legal chart point regardless of arc length*. There
> is none. `assert_generic_star` forbids **collinearity** at a body
> (`q_v, q_u, q_w` for hinges `vu`, `vw`) — strictly stronger than, and
> logically independent of, the **coplanarity of four consecutive bodies**
> that `a = 0` / `c = 0` require; `(CH-1)` is a hypothesis on the *graph*
> (`hcard`, min degree, girth) and constrains no plane; `bline.legal_peel`
> adds terminal-degree and `rnode_shaped` conditions, also purely
> combinatorial. **MEASURED corroboration:** on the landed population every
> arc-4 configuration realizes `dim U = 4` at all **165** of its points
> (census `(4, 4): 165`), so the degenerate branch is not where the chart
> lives. The path bound (BE-189)(ii) is a *ceiling*, not a degeneracy
> forcer — which is why it constrains `dim U` and not `rank(B|_U)`.

### Step BE197 — (BE-198): (BE-193)(iv)'s warrant, made UNCONDITIONAL — the arc supplies its own hyperbolic splitting

> **(BE-198)(i)** *(**PROVED**; the splitting)* By (BE-196)(iii),
> `⟨ℓ_1, ℓ_2⟩` and `⟨ℓ_3, ℓ_4⟩` are **both totally singular** 2-spaces, and
> at `dim U = 4` they are complementary. So
>
> > **`U = ⟨ℓ_1, ℓ_2⟩ ⊕ ⟨ℓ_3, ℓ_4⟩` is a HYPERBOLIC 4-space over ANY field —
> > Witt index 2, no discriminant condition — whenever `rank(B|_U) = 4`.** ∎
>
> Asserted at **30/30** nondegenerate draws (both summands totally singular,
> the sum direct, `rad(U) = 0`).

> **(BE-198)(ii)** *(**the correction to a WARRANT, not to a conclusion**)*
> (BE-193)(iv) reads *"a **nondegenerate** rank-4 form on a 4-space **does**
> admit totally singular 2-spaces (the hyperbolic case)"*. Over `ℚ` that is
> true **only if** hyperbolic — a rank-4 form of Witt index 1 (e.g.
> `x² + y² + z² + w²`) admits none — so as stated the sentence carried an
> undischarged side condition. (i) discharges it from the arc's own
> incidences. **The conclusion (BE-193)(iv) drew is therefore right, and now
> for a complete reason.** This is a *strengthening* of a landed step, not a
> refutation, and it is recorded as such.

> **(BE-198)(iii)** *(**CONSTRUCTED**; the two rulings)* Normalize to
> `e_1 = ℓ_1`, `e_2 = ℓ_2`, `e_3 = ℓ_3`, `e_4 = aℓ_4 − bℓ_3`; then `B` pairs
> `e_1 ↔ e_3` (by `a`) and `e_2 ↔ e_4` (by `ac`) and nothing else, so
> `Q/2 = a(xz + c·yw)` and `U` is the space of `2×2` matrices with
> `Q = det`. Its totally singular 2-spaces are exactly the **fixed-column**
> and **fixed-row** families of rank-`≤ 1` matrices — **two `P¹`-rulings**:
>
> > `A(u) = ⟨u_0e_1 + u_1e_2, \; c\,u_1e_3 − u_0e_4⟩`, &nbsp;
> > `B(u) = ⟨c\,u_0e_1 − u_1e_4, \; u_0e_2 + u_1e_3⟩`.
>
> **300 members BUILT** (5 parameters × 2 rulings × 30 draws), each asserted
> 2-dimensional, totally singular and inside `U`; two members of *different*
> rulings meet in a line at **150/150**. **This is the constructed family the
> discipline requires** — a claim about *which* subspaces exist, tested by
> building them, never by drawing random 2-spaces (which are never
> isotropic: the defect BRANKV self-caught at (BE-191)(ii) and
> `RESEARCH-ARC.md` §4's exact shape). The **isotropic 2-plane the dispatch
> asked to see exhibited** is the arc's own `⟨ℓ_1, ℓ_2⟩`.

### Step BE198 — (BE-199): the perp-reduction — the radical's habitat is `U ∩ ℓ_j^⊥`, not `U`

> **(BE-199)(i)** *(**PROVED**)* `ℓ_j ∈ Π_x` ((BE-196)(i)) and `Π_x` is
> totally singular, so every element of `Π_x` is `B`-orthogonal to `ℓ_j`
> (geometrically: two lines through `q_x` meet). Hence
>
> > **`Π_x ⊆ U^{(1)} := U ∩ ℓ_j^⊥`, and `ℓ_j ∈ rad(U^{(1)})` for free.** ∎
>
> Asserted at **40/40** draws on four independent elements of `Π_x` each, and
> `α_x ⊆ ℓ_j^⊥` too, so `U ∩ α_x = U^{(1)} ∩ α_x`.

> **(BE-199)(ii)** *(**PROVED / MEASURED**; the dimensions)* For `n ≥ 3` the
> first Gram row `(0, 0, g_{13}, …, g_{1n})` is generically nonzero, so
> `dim U^{(1)} = n − 1` and `dim Ū = n − 2` for `Ū := U^{(1)}/⟨ℓ_j⟩`; at
> `n = 2` the whole span is totally singular, `U^{(1)} = U` and
> `dim Ū = 1`. At `n = 4`: `dim U^{(1)} = 3`, `rad(U^{(1)}) = ⟨ℓ_j⟩`
> exactly, `rank(B|_{U^{(1)}}) = 2` — asserted at **40/40**; `dim Ū` asserted
> at `min(n,6) − 2` for every `n` in 3–7 (24 draws each).

> **(BE-199)(iii)** *(the reading)* **This is why the dispatch's span was the
> wrong object.** (BE-191)(ii)'s mechanism is *"every totally singular
> 2-space of a rank-2 3-space contains its radical"*, and at `n = 3` the
> 3-space it is applied to happens to be `U` itself. At `n ≥ 4` the space
> `Π_x` actually lives in is `U^{(1)}`, one dimension smaller, and it comes
> with `ℓ_j` in its radical **automatically**. The radical mechanism did not
> die at arc 4; it was pointed at `U`.

### Step BE199 — (BE-200): the ARC-4 THEOREM — exactly two candidates, and the survivor forces `q_z ∈ π_x`

> **(BE-200)(i)** *(**PROVED**; the candidate list is EXACTLY TWO)* At
> `|arc_j| = 4`, `dim U = 4` and `ac ≠ 0`, take the lift
> `Ū = ⟨ℓ̄_2, v̄⟩` with `v := aℓ_4 − bℓ_3`. Then `B(ℓ_1, v) = ab − ba = 0`,
> `Q(v) = 0` and `B(ℓ_2, v) = ac ≠ 0`, so
>
> > **`Ū` is a HYPERBOLIC rank-2 plane, `Q(αℓ̄_2 + γv̄) = 2ac·αγ`, and its
> > isotropic cone is exactly `{αγ = 0}` — TWO lines.**
>
> Every totally singular 2-space of `U^{(1)}` contains `rad(U^{(1)}) = ⟨ℓ_j⟩`
> ((BE-191)(ii) applied to `U^{(1)}`), and `Π_x` contains `ℓ_j` anyway, so the
> 2-spaces to check are exactly `⟨ℓ_j, αℓ_2 + γv⟩` over `(α:γ) ∈ P¹`. Hence
>
> > **`Π_x ∈ {⟨ℓ_j, ℓ_{cw}⟩, ⟨ℓ_j, v⟩}`.** ∎
>
> **ENUMERATED, not sampled:** the cone equivalence `singular ⟺ αγ = 0` is
> asserted at **30 points of `P¹` per draw, 40/40 draws**, and the resulting
> candidate count is asserted to be **exactly 2** at each. The `P¹` sweep is
> a complete enumeration because `⟨ℓ_j, w + λℓ_j⟩ = ⟨ℓ_j, w⟩` — the `λ`
> freedom does not change the space.

> **(BE-200)(ii)** *(**PROVED**; candidate 1 is FORBIDDEN)*
> `Π_x = ⟨ℓ_j, ℓ_{cw}⟩` requires `ℓ_{cw} ∈ Π_x`, i.e. the line `q_c ∨ q_w`
> passes through `q_x`, i.e. **`q_x, q_c, q_w` collinear** — precisely the
> coincidence `assert_generic_star` forbids at body `c` (its own docstring:
> *"two hinges `vu`, `vw` coincide iff `p_v, p_u, p_w` are COLLINEAR"*). ∎
> Asserted at **40/40** as a *non*-membership at non-collinear draws.

> **(BE-200)(iii)** *(**PROVED**; candidate 2 forces the incidence)*
> `v = aℓ_4 − bℓ_3 = p_z ∧ (a\,p_y + b\,p_w)` — asserted as an identity at
> **40/40** — so `v` is a **line through `q_z`**. If `Π_x = ⟨ℓ_j, v⟩` then
> some `w = v + λℓ_j ∈ Π_x` is a line through `q_x`; that line contains
> `q_z` as well (or `v` degenerates, forcing `q_w, q_z, q_y` collinear, which
> `assert_generic_star` forbids at body `z`), hence equals `q_x ∨ q_z`, hence
> lies in `π_x`. Therefore
>
> > **`|arc_j| = 4` and `Π_x ⊆ ρ̄_i` ⟹ `q_z ∈ π_x`, and `q_x` lies on
> > `q_z ∨ [a\,q_y + b\,q_w]`, so `q_x, q_w, q_z, q_y` are COPLANAR.** ∎
>
> `q_z ∈ π_x` is **one linear equation** `n_x · (q_z − q_x) = 0` in the
> tower's own coordinates — **exactly (BE-193)(i)'s shape**, at the arc's
> second-to-last body instead of at `y`. The "candidate 2 passes through
> `q_x` ⟺ the collinearity" equivalence and the coplanarity consequence are
> asserted at **40/40**.

> **(BE-200)(iv)** *(**PROVED + CONSTRUCTED**; the confinement is PROPER and
> INHABITED, and the pointwise clause is FALSE at arc 4 too)* **Proper:**
> `dim(U ∩ α_x) = 1 = ⟨ℓ_j⟩` at **40/40** generic arc-4 draws, so the
> containment locus over the second star point is **empty** there — asserted
> at **960/960** swept second star points, which is a sweep of the very
> quantifier the claim is about rather than one draw (`RESEARCH-ARC.md` §4's
> sharpening). **Inhabited:** BRANKV's (BE-192) plant one arc-edge longer —
> the cycle `x—c₁—w—z—y—b₁—⋯—c₂—x` with `|arc₁| = 4` and `|arc₂| ∈ {4,5,6}`
> (total `≥ 8`, off (BE-40)'s `≤ 6`-cycle rigidity), glued by
> `bline.legal_peel` into a composite peel on the `K33` skeleton at profile
> 3, with `(CH-1)`'s `hcard` / min-degree-2 / girth-`≥ 4` on `H`, `x ≁ y`,
> both terminals hubs and side 2 `rnode_shaped` all checked **before** any
> measurement, and configurations from `binduc.flat_config` (whose docstring
> states it is *"a legal pencil configuration at EVERY graph"* and which
> asserts `assert_generic_star` and `verify_pencil_witness` itself, the
> latter re-asserted here) — gives, at **24 of 24** gated chart points over
> **3** peels,
>
> > **`c_i(Π_x) = 2` and `ρ_i = 3`, with `q_z ∈ π_x` at 24 of 24.**
>
> So the **pointwise** clause is false at arc 4 as well, `q_z ∈ π_x` is
> confirmed as the forced incidence, and (BE-200)(iii)'s locus is a *proper
> inhabited* closed condition rather than an empty one. **CAP, stated:** the
> witness is again **fully planar**, i.e. maximally degenerate, on one
> skeleton at 3 peels / 24 points — (BE-192)(iii)'s disclosure verbatim, and
> a less degenerate arc-4 witness is **not found and not excluded**.

### Step BE200 — (BE-201): ONE COUNT subsumes the ladder — `dim(U ∩ α_x) = max(1, min(|arc|,6) − 3)`

> **(BE-201)(i)** *(**PROVED / MEASURED**; the invariant)* `U` has dimension
> `min(n, 6)` generically, `α_x` has dimension 3, both contain `ℓ_j`, and the
> ambient is 6-dimensional, so the generic intersection is
>
> > **`dim(U ∩ α_x) = max(1, min(n, 6) − 3)`,**
>
> the lower bound `1` coming from `ℓ_j` and the count from
> `dim U + 3 − dim(U + α_x)` with `dim(U + α_x)` generically `6`. ∎
> **Asserted at every arc length 2–7, 24 draws each — census
> `(2,1): 24, (3,1): 24, (4,1): 24, (5,2): 24, (6,3): 24, (7,3): 24`** — and
> independently on the landed population, where `dim U = min(|arc_j|, 6)`
> holds at **783/783** points (census
> `(2,2): 69, (3,3): 48, (4,4): 165, (5,5): 96, (6,6): 165, (7,6): 96,
> (8,6): 96, (9,6): 48`).

> **(BE-201)(ii)** *(**THE THEOREM**, and it is four landed cases plus two
> new ones in one line)* `Π_x ⊆ α_x` always ((BE-196)(ii)), so `Π_x ⊆ U`
> requires `dim(U ∩ α_x) ≥ 2`. With (i):
>
> > **`|arc_j| ≤ 4`: the containment is IMPOSSIBLE at a generic chart point**
> > — the bad locus sits inside the proper closed
> > `{rank([ℓ_1,…,ℓ_n] ++ α_x) ≤ n + 1}`, a condition on the arc's own bodies
> > and `q_x` that does **not** mention the other side-neighbour;
> > **`|arc_j| = 5`: the containment is ONE linear condition** — `U ∩ α_x` is
> > a 2-space (a pencil at `q_x` in a determined plane) and the containment
> > says `ℓ_{j'}` lies in it, i.e. `q_{c_{j'}}` lies in that plane;
> > **`|arc_j| ≥ 6`: the containment is AUTOMATIC**, `U ∩ α_x` being all of
> > `α_x`.
>
> Hence, with (BE-123)(i)/(ii)/(iii)/(iv) and the bridge (BE-180) verified —
> `Chart(H)` irreducible, the bad locus constructible and inside a proper
> closed subset —
>
> > **(PENCIL-SATURATES-CHART) HOLDS ON A DENSE OPEN at every `k = 2` peel
> > whose side has an `x`–`y` arc of length `≤ 5` through a side-neighbour of
> > `x`,** identically at arc 2 (hypothesis unreachable, (BE-190)). ∎
>
> **PROPERNESS WITNESSED, not assumed:** `ℓ_{j'} ∈ U` fires at **0 of the
> 378** arc-`≤ 5` points of the landed population, so its complement is
> inhabited at all 378; over all 783 points it fires at **405**, which is
> *exactly* the 405 points with `dist ≥ 6` — the `dim U = 6` régime, where
> (BE-201)(ii) says it must be automatic.

> **(BE-201)(iii)** *(what this does to the landed steps)* (BE-190) is the
> `n = 2` case (`dim(U ∩ α_x) = 1` with `dim U = 2`, so `Π_x = U` would need
> the collinearity); (BE-191)/(BE-193)(ii) is the `n = 3` case;
> (BE-200)(iii) is the `n = 4` case, where the invariant is refined from
> *"impossible generically"* to a **named** incidence. **Nothing is
> refuted** — (BE-193)(ii) is *subsumed*, and its own radical proof remains
> the sharper statement at `n = 3` because it names the habitat
> (`{q_y ∈ π_x}`) rather than only its codimension.

### Step BE201 — (BE-202): TWO mechanisms, TWO exact boundaries — and the stop is (BE-189)(iii)'s own threshold

> **(BE-202)(i)** *(**CONSTRUCTED**; the radical mechanism stops at 4)* The
> quotient mechanism confines `Π_x` to a **finite** candidate list exactly
> while `dim Ū ≤ 2`, i.e. `n ≤ 4`. The census, with the cone counted in
> closed form (`0`/`1` dimensional cases decided by inspection, the binary
> case by the discriminant `B² − AC` and an exact rational-square test — no
> sampling anywhere):
>
> | `n` | `dim U` | `dim(U ∩ α_x)` | `dim Ū` | isotropic locus of `Ū` | verdict |
> |---|---|---|---|---|---|
> | 2 | 2 | 1 | 1 | 1 line | containment impossible ((BE-190)) |
> | 3 | 3 | 1 | 1 | 1 line, forbidden | `q_y ∈ π_x` ((BE-191)) |
> | 4 | 4 | 1 | 2 | **2 lines** | `q_z ∈ π_x` ((BE-200)) |
> | 5 | 5 | 2 | 3 | **a CONIC** | no confinement from this mechanism |
> | 6, 7 | 6 | 3 | 4 | a quadric 3-fold | none |
>
> 24 draws per row, every cell asserted. At `n = 5` the claim *"the candidate
> locus is not finite"* is **CONSTRUCTED**: `Ū` is a nondegenerate ternary
> form with the rational point `ℓ̄_2` (a hinge line, hence isotropic), and the
> standard secant parametrization `t = −2B(v_0, d)/Q(d)` produces **≥ 5
> distinct** further rational points at every draw, each yielding a totally
> singular 2-space of `U` asserted to be 2-dimensional, isotropic and inside
> `U`. ∎

> **(BE-202)(ii)** *(**PROVED**; the α-space mechanism stops at 5, and why
> that is the LAST rung)* By (BE-196)(i) the bad locus sits inside
>
> > **`Z_n := {rank[ℓ_1, …, ℓ_n, ℓ_{j'}] ≤ n}`,**
>
> a determinantal **closed** condition, which is **proper** exactly when rank
> `n + 1` is achievable — i.e. exactly when `n + 1 ≤ 6`, i.e. **`n ≤ 5`**.
> At `n ≥ 6`, `dim U = 6 = Λ²K⁴` and `ℓ_{j'} ∈ U` is **vacuous**. ∎
> Asserted as a rank census: `rank[ℓ_1..ℓ_n, ℓ_{j'}] = n + 1` at `n = 2,3,4,5`
> and `= 6` at `n = 6,7` (24 draws each), with the containment verdict itself
> asserted to flip **exactly** at `n = 6`
> (`contains(U, Π_x) == (n ≥ 6)`, 144/144).

> **(BE-202)(iii)** *(**PROVED**; the boundary coincides with (BE-189)(iii)'s
> threshold, and that is the finding)* (BE-189)(ii) proves `ρ_i ≤ dist`, so
> at `dist ≤ 5` the clause's conclusion `ρ_i = 6` is **unreachable** and the
> clause is *equivalent to the containment never happening*. (BE-201)(ii)
> says the containment does not happen generically there. Conversely the path
> bound carries information only while `dim U < 6`, i.e. while `|arc_j| ≤ 5`.
> Therefore
>
> > **the path-bound family of arguments — (BE-150)(i)'s bound and everything
> > built on it, (BE-190) / (BE-191) / (BE-193) / (BE-200) / (BE-201) —
> > closes exactly the strata on which the clause is VACUOUS, and provably
> > cannot reach the strata on which it has CONTENT.** ∎
>
> **This is a structural stop, not a cap**, and it is the exact boundary the
> dispatch asked for. **CONSEQUENCE FOR THE BOARD:** *"try arc length 6"* is
> **not** a live successor, and neither is any further sharpening of the arc
> span. **MEASURED corroboration:** all **120** containments on the landed
> population sit at `dist ∈ {8: 72, 9: 48}`, none below 8 — a gap of three
> even below the `dist = 6` boundary, so the population is consistent with
> the theorem and does not touch it.

### Step BE202 — (BE-203): the closure priced, the board, §8, the successor, the E-rider

> **(BE-203)(i)** *(**the price**, measured and not hidden)* On the same
> 99-configuration / 783-point population BARCH's `side_row` builds and
> BGPROP/BRANKV measure — reproduced here at the same seeds, with the
> per-configuration `dist` census identical
> (`{2: 9, 3: 6, 4: 21, 5: 12, 6: 21, 7: 12, 8: 12, 9: 6}`) —
>
> > **arc `≤ 3` (BRANKV): 15 of 99. Arc `≤ 4` ((BE-200)): 36 of 99. Arc
> > `≤ 5` ((BE-201)(ii)): 48 of 99.**
>
> `dist(x, y) = min_j |arc_j|` is **asserted** at every configuration, not
> assumed — the reading (BE-195)(i)(e) flagged — and the arc through a
> *specific* `c_j` is computed by `brankv.arc_through`, i.e. by deleting the
> other `x`-edges. So **51 of 99 remain untouched**, and by (BE-202)(iii)
> they are **exactly** the ones this method class cannot reach.

> **(BE-203)(ii)** *(**the board**, four items and no more)* **1.** Half (B)'s
> item 0(a) at side-degree `≥ 2` is **CLOSED GENERICALLY on the arc-`≤ 5`
> strata** ((BE-201)(ii)), **48 of 99** measured, **OPEN** on the other 51.
> **2.** The **pointwise** form is **FALSE at arc 3 and at arc 4**
> ((BE-192)/(BE-200)(iv)); no further pointwise attempt is authorized.
> **3.** The arc / path-bound method class is **EXHAUSTED** on this clause
> ((BE-202)(iii)) — it reaches `dist ≤ 5` and provably no further. **4.** The
> live successors are therefore **not** arc-length ones: §8's **rank 2**
> ((BE-E4′)), a *less degenerate* (BE-192)/(BE-200) witness, and the `V^k`
> graph at `k ≥ 3`.

> **(BE-203)(iii)** *(**the §8 consequence**, recorded in §8 as its own rule
> requires)* Rank 1's slot is **spent as a method class**, not merely as a
> target: the finding is that the standing *"compute the Klein form's radical
> on the span the path bound hands you"* method — three landed instances
> ((BE-172)/(BE-182)/(BE-191)) plus this direction's fourth — has a
> **computable ceiling**, `|arc| ≤ 5`, coinciding with the strata where the
> clause is vacuous. The generalizable lesson is one level up: **a path bound
> gives a subspace, and a subspace argument dies exactly when the subspace
> fills the ambient** — so before ranking a span-based route, compute
> `dim(span)` against `dim(ambient)` first and read off the reachable strata.
> That is a two-line calculation and it would have priced this whole rung in
> advance.

> **(BE-203)(iv)** *(**what did NOT move**)* (BE-14), S-mark, half (β) at and
> outside the window, (BE-E4′), cross-pair welding, class uniformity, the 12
> unwitnessed blocks, `⟨M⟩`'s emptiness at 93 rows, (BE-101)(iii), the flag
> base, `Γ`-properness (still **FALSE** as a class-uniform statement,
> (BE-184)), (GR-10), (GR-15), (OC-8), (K-res), W4, `hbareSplit`.
> **Side-degree `≥ 3` is untouched**, the `V^k` graph is untouched, and the
> 51 long-arc configurations are untouched. **Not a PENCIL event.**

> **(BE-203)(v)** *(**the price**, itemized)* **(a)** Everything is at
> `k = 2` and at side-degree exactly **2**. **(b)** (BE-201)(ii) covers arc
> length `≤ 5` only, **48 of 99** on this population, and the population is
> BLINE's long-core library plus BARCH's cycle-7/8 corner — **not** a habitat
> census. **(c)** The arc-4 refuting witness is **fully planar**, on **one**
> skeleton (`K33`, profile 3) at **3** peels / **24** chart points; a less
> degenerate one is **not found and not excluded**. **(d)** (BE-201)(i)'s
> invariant is a **generic** identity: it is asserted at 144 constructed
> draws and at 783 population points, and it *fails* on the degenerate loci
> by design — which is exactly why (BE-201)(ii)'s conclusion is *generic* and
> is stated so. **(e)** The `≥ 5`-member conic families at `n = 5` are
> constructed from **one** rational point per draw by a secant sweep of
> **6·(d−1)(d−2)** directions; *"the locus is infinite"* is a statement about
> the conic's geometry, and what is *measured* is *"more than two members
> exist, constructed"*. **(f)** `q_z ∈ π_x` is shown **necessary** at arc 4,
> not sufficient — the 24 gated violations are fully planar, so they satisfy
> far more than that one equation.

> **(BE-203)(vi)** *(**the E-rider**)* **No E-condition fires.** E1/E2/E3 are
> §(K-grid) objects, untouched; **§(K-bare-ext) (E4)** stays refuted
> ((BE-160)) and **(BE-E4′)** is untouched — this direction is about half
> (B)'s item 0(a)'s own clause, not the two-sided arithmetic. `hbareSplit` is
> **untouched**.

### Verification (direction BLONGARC)

| claim | evidence |
|---|---|
| (BE-196)(i) `Π_x ⊆ U ⟺ ℓ_{j'} ∈ U` | **PROVED** from `Π_x = ⟨ℓ_{xc_1}, ℓ_{xc_2}⟩`, the form (BE-190)(i) and every landed driver use; asserted 40/40 |
| (BE-196)(ii) `Π_x ⊆ α_x`, `α_x` maximal totally singular | **PROVED**; asserted at 144 draws (`dim α_x = 3`, `rank(B|_{α_x}) = 0`) |
| (BE-196)(iii) the band, every consecutive pair totally singular | **PROVED**; **CONSTRUCTED** over the whole pair family, 225/225 pairs on 75/75 arcs of lengths 2–6 |
| (BE-197)(i) `det(B\|_U) = (ac)²`, `rank = 2·rank(Y)`, rank even | **PROVED**; asserted 60/60 |
| (BE-197)(ii) `a = 0` / `c = 0` are the two consecutive coplanarities | **PROVED** as equivalences; asserted 60/60 |
| (BE-197)(iii) **the dispatch's question: NO** | **PROVED + MEASURED**; rank 4 at 60/60 generic draws, `dim U = 4` at 165/165 arc-4 population points |
| (BE-197)(iv) the named tell FAILS | **VERIFIED AT SOURCE** — `assert_generic_star`, `legal_peel` and (CH-1) opened; collinearity ≠ four-body coplanarity |
| (BE-198)(i) the unconditional hyperbolic splitting | **PROVED**; asserted 30/30, `rad(U) = 0` at each |
| (BE-198)(ii) (BE-193)(iv)'s warrant was conditional | **VERIFIED AT SOURCE** — (BE-193)(iv) read at its own proof site; strengthening, not refutation |
| (BE-198)(iii) the two `P¹`-rulings | **CONSTRUCTED**: 300 members built, each asserted totally singular and inside `U`; cross-ruling intersection dim 1 at 150/150 |
| (BE-199)(i)/(ii) the perp-reduction and its dimensions | **PROVED**; asserted 40/40 at `n = 4` (`dim U^{(1)} = 3`, `rad = ⟨ℓ_j⟩`, rank 2) and `dim Ū = min(n,6) − 2` at 24 draws per `n` |
| (BE-200)(i) exactly TWO candidates at arc 4 | **PROVED**; **ENUMERATED** over 30 points of `P¹` per draw, 40/40, cone asserted `= {αγ = 0}` |
| (BE-200)(ii) candidate 1 needs the forbidden collinearity | **PROVED**; `assert_generic_star`'s docstring read at source; asserted 40/40 |
| (BE-200)(iii) candidate 2 forces `q_z ∈ π_x` + coplanarity | **PROVED**; the identity `aℓ_4 − bℓ_3 = p_z ∧ (a p_y + b p_w)` and both consequences asserted 40/40 |
| (BE-200)(iv) the confinement is proper AND inhabited; pointwise FALSE at arc 4 | **PROVED** (proper: `dim(U ∩ α_x) = 1`, 40/40; empty over 960/960 second star points) + **MEASURED** (24/24 gated composite chart points, `ρ_i = 3`, `q_z ∈ π_x` 24/24). **CAP: fully planar, one skeleton, 3 peels** |
| (BE-201)(i) `dim(U ∩ α_x) = max(1, min(n,6) − 3)` | **PROVED + MEASURED**; asserted at 24 draws per `n` in 2–7 and `dim U = min(\|arc\|, 6)` at 783/783 population points |
| (BE-201)(ii) the arc-`≤ 5` generic closure | **PROVED** from (i) + (BE-123)(i)–(iv) + (BE-180); properness **WITNESSED** (`ℓ_{j'} ∈ U` at 0/378 arc-`≤ 5` points, 405/783 overall = exactly the `dist ≥ 6` points) |
| (BE-202)(i) the radical mechanism stops at 4 | **CONSTRUCTED**; cone counted in closed form at `dim Ū ≤ 2` (exact rational-square discriminant test) and the `n = 5` conic built with ≥ 5 members per draw, 24 draws |
| (BE-202)(ii) `Z_n` proper exactly at `n ≤ 5` | **PROVED**; rank census `n+1` at `n ≤ 5`, `6` at `n ≥ 6`, and the containment verdict flips exactly at `n = 6`, 144/144 |
| (BE-202)(iii) the boundary IS (BE-189)(iii)'s threshold | **PROVED** from (BE-189)(ii) + (BE-201)(i); corroborated by the 120 containments sitting at `dist ∈ {8,9}` |
| (BE-203)(i) 15 → 36 → 48 of 99 | **MEASURED** on BARCH's own population; `dist = min_j \|arc_j\|` **asserted** at every configuration |
| (BE-203)(ii)–(vi) the board, §8, the price, the E-rider | **stated**, with every cap named |

**Reproduce.**

```
python3 notes/scripts/w4/blongarc.py form      # (BE-196)-(BE-198)
python3 notes/scripts/w4/blongarc.py perp      # (BE-199)/(BE-200), incl. the gated arc-4 witness
python3 notes/scripts/w4/blongarc.py ladder    # (BE-201)/(BE-202)
python3 notes/scripts/w4/blongarc.py pop       # (BE-203) on the landed 99/783 population
python3 notes/scripts/w4/blongarc.py validate  # all four
```

**WHICH CONJUNCTS ARE TESTED** — the discipline BGPROP's landing earned, since
`barch.run_cert`'s own `BAD` silently omitted its `ρ_i ≤ 5` conjunct. The
clause at `k = 2` is `c_i(Π_x) = 2 ⟹ ρ_i = 6`, and `pop` reads **both**:
`c_i(Π_x) = 2` as `contains(ρ̄_i, Π_x)` **and** `ρ_i` from
`bimage.rho_bar_of`, never dropped — reporting the containment count (120),
the violation count (containment **and** `ρ_i ≤ 5`: **0**) and the `dist`
distribution of each separately. `perp`'s gated witness reads both conjuncts
too (`c_i(Π_x) = 2` at 24, `ρ_i = 3` at 24). The (BE-189)(ii) ceiling is
re-asserted at every population point, so the population identity with
BRANKV's is checked rather than claimed.

**THE SAMPLER'S SUPPORT, AND WHICH GENERATOR PARAMETERS MOVED.** `form`,
`perp` and `ladder` draw arc bodies as uniform integer points in
`[−9, 9]³ ⊂ 𝔸³` with a general-position filter (pairwise distinct, no three
consecutive collinear), and the parameter they **vary is the one this
question is about**: the **arc length**, swept `2, 3, 4, 5, 6, 7` — which is
`RESEARCH-ARC.md` §4's second-instance rule (*enumerate the generator's
parameters and say which the evidence varied*) applied to the axis BRANKV's
`short_library` held at 3. `arc4_library` is BRANKV's `short_library` with
the **short arc one edge longer** and the long arc swept over `{4, 5, 6}`, so
the composite-peel axis moves too. What is **NOT** varied: the skeleton
(`K33` only) and its profile (3 only) in the gated witness — BRANKV's own
limitation, unchanged — the field (`ℚ` throughout), and the side-degree (2
only). `pop` does not sample at all in the shape direction: it runs BARCH's
`library()` × `side_row` population and BARCH's own fibre seed formula
verbatim, so its 99 configurations and 783 points are **the same population**
(BE-151), (BE-181) and (BE-189) measure.

**EVERY CAP, AS "NOT FOUND UNDER CAP C".** *(a)* A less degenerate (partially
planted) arc-4 violation is **not found under** the cap *"3 peels × 8
`flat_config` draws on the `K33`/profile-3 composite"* — and it is **not
excluded**; the chart's hub-planarity at `y` and at side 2's hubs is the same
unsolved system (BE-192)(iii) records. *(b)* At `n = 5` the conic's members
are **not exhaustively enumerated**: `≥ 5` per draw are **found under** the
cap *"secant directions with two nonzero coordinates, `k ∈ [−3, 3]`"*, which
is all (BE-202)(i) claims. *(c)* The `P¹` candidate sweep at `n = 4` is
**30 points**, but it is not a cap on the *claim*: the cone equivalence
`singular ⟺ αγ = 0` is asserted pointwise and *proves* the count is two.
*(d)* The rank-4 genericity at arc 4 is **60/60 under** the cap
*"integer coordinates in `[−9, 9]`"*; the degenerate branch is reached by
**construction** in (BE-200)(iv)'s plant, not by hoping a sampler lands on
it. *(e)* No claim in this landing rests on a *"not found, therefore absent"*
reading: every negative statement is either a proved determinantal properness
or is labelled with its cap here.

**WHAT DID NOT MOVE, restated at the harness level.** No landed figure moved:
`pop` reproduces 99 / 783 / 120 and the `dist` censuses BGPROP and BRANKV
recorded, and the (BE-189)(i)/(ii) ceilings still hold at every point.

**`validate` FITS** — **51 s** against the 600 s foreground ceiling — so this
landing adds **no** over-ceiling case to `notes/scripts/README.md` §0. Mode
times: `form` 0.3 s, `perp` 1.0 s, `ladder` 0.6 s, `pop` 49 s.

**Figure-invariance gate, discharged.** This landing **adds** a harness driver
and modifies **none**: `git diff --name-only -- 'notes/scripts/*.py'
'notes/scripts/*.m2'` is **empty** and `git status --porcelain
notes/scripts/` shows only the **addition** of `w4/blongarc.py`, so *No
tracked driver modified* discharges the gate and §3 is not baselined.
`brankv.py` (from which `arc_through`, `gram`, `gram_rank` and `hinge` are
imported), `barch.py`, `bline.py`, `binduc.py`, `bproper.py`, `bdegtwo.py`,
`bimage.py`, `bunif.py`, `pitch.py`, `exactcore.py` and `kbare_common.py` are
**imported, not edited**. Reproducibility spot-check: `validate` run twice at
`PYTHONHASHSEED=0` is byte-identical modulo each mode's timing line.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bimage.pt_in` is called **only** on the width-4 fibre basis
`bdegtwo.fibre_k` returns — its intended use — and no `Λ²`-side draw goes
through it. **No width-12 object is built at all**, so `bimage.span`/`dim`/
`isect`'s rank-triggered width-6 special case is unreachable rather than
merely avoided; the one width-4 incidence test (`q_z ∈ π_x` in `pop`) goes
through `exactcore.rank` **instead of** `span`/`contains`, which is exactly
the recorded defect's shape. `bwin` is **not imported**; the one
dehomogenization goes through `barch._aff3`, which returns a **tuple**.

**ONE DOC DEFECT FOUND IN A LANDED DRIVER, RECORDED AND NOT FIXED.**
`w4/brankv.py`'s header docstring states, in its first `(BE-191)` paragraph,
that *"`Pi_x` is totally singular and 2-dimensional, so it embeds in `U` only
if `rank(B|_U) <= 1`"* — which is the **refuted first-draft inference**
(BE-191)(ii) itself corrects two paragraphs later, presented there without a
flag. The *conclusion* (`β = 0`) is correct and correctly proved in the
workbook and in the driver's code; only that one docstring sentence still
states the refuted linear-algebra step as if it were a fact. It is **not
edited here**: editing a tracked driver forfeits the *No tracked driver
modified* one-line discharge of the figure-invariance gate and would require
baselining `brankv.py`'s whole import closure. Recorded as a harness-debt
doc item instead.
