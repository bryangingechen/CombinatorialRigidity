## §(K-bare-ext) — continuation (direction BOPEN): **(PENCIL-SATURATES-CHART) IS A THEOREM AT EVERY SIDE-DEGREE-`1` TERMINAL, AND (BE-69) — THE CITATION HALF (B) HAS LEANED ON SINCE BSATUR — IS BOTH THE WRONG ONE AND NOT NEEDED** — its locus is the **attainment** locus `A₁ ∩ A₂ ∩ GP`, cut out by rank **LOWER** bounds, and the saturation locus is an **UPPER** bound on an intersection dimension, so (BE-69)(i)'s openness proof does not transport; what the genericity half actually needs is only that the bad locus be **CONSTRUCTIBLE** — it is a finite union of rank strata — on an **IRREDUCIBLE** chart, and then *proper on the fibres of one dominating family* already yields a **DENSE OPEN** good locus. Both remaining inputs are then **PROVED, not measured**: the `p_x`-**sweep** falls out of §(K-chart)'s own tower, because the **only** equation tying `q_x` to a fixed core is `n_c · (q_x − q_c) = 0`, so `p_x` ranges over the whole plane `π_c` when `c` is a hub and over **all of `𝔸³`** when it is not, with side 2 **rebuilt** rather than perturbed (**102/102** targets realized as full legal chart points, both gates); and **`a_i = 0` generically IS (BE-69)(i)'s own open locus `A_i`**, whose nonemptiness is **(BE-14) for the side** — the 2-cut induction's own hypothesis, not a new obligation. The step that makes (BE-116) the right locus after all is new and is **pointwise**: rotating the flag plane `π_x` through the line `p_x ∨ p_c` **fixes `ρ̄_i`** and sweeps `Σ_x`, so a bad chart point that is bad on any *open* set is bad at **every** flag, which is exactly `Σ_x ⊆ ρ̄_i` — and a fixed-flag argument would **not** do, since a constructed `A` makes the whole `p_x`-plane bad while `Σ_x ⊆ ρ̄_i` holds at a **single point**. `Chart(H)`'s irreducibility at a **piece** — BPROPER's own escape item 2 — is settled by inheritance in two lines: degrees only drop, so a hub of `H` is a hub of `G` and `d_h(H) ≤ d_h(G) ≤ 2`. **Half (B)'s item 1 CLOSES at every side-degree-`1` terminal, so (BE-101)(i)/(ii) and the `14 → 12` drop stand at a generic chart point**; what is **left** is the side-degree-`≥ 2` instances, where the clause reduces to a two-part condition `(∗)` on one **fixed line**, certified exactly at **91/91** but not proved. **Nothing is refuted**: (BE-116) is true as stated and is used verbatim; the price is paid **down** — `margin ≤ 0` at `Π_x`, `Π_y` and `⟨M⟩` at **54** further rows, `0` shortfalls, so `notes/Phase39.md` item 0(c) is **untouched and still open**

### Standing notation (on top of *Steps BE113–BE120*)

BPROPER's, verbatim: `x, y` the peel's terminals, `deg_i(v)` the degree of `v`
**inside** `side_i`, `core := side_i − x`, `A := ρ̄(core; c, y)`,
`ℓ := p_x ∧ p_c`, `Σ_p = p ∧ K⁴`, `π_v` the flag plane through
`closedNbhd(v)`. Two more, both read at source this pass:

> **`Π_x := p_x ∧ π_x`**, the 2-dimensional space of lines through `p_x`
> inside `π_x` (`bimage.pencil_space`, whose docstring names it *"the
> workbook's `Π_v := p_v ∧ π_v`"*; it is BUNIF's block, `bunif.py:129`).
> **`𝒜(H)`** is §(K-chart) *Step CH1*'s upstairs ambient — coordinates
> `(q, n)` = body points and hub panel normals — and `Chart(H)` its
> downstairs image. `hub` means degree `≥ 3` **in `H`**; since `c ∉ {x, y}`
> all of `c`'s neighbours lie in `side_i`, so `c` is a hub **iff**
> `deg_i(c) ≥ 3`, which is exactly BPROPER's (BE-116) case split.

**The clause under discussion, quoted from (BE-112)(iii) and not paraphrased:**
*at a generic point of `Chart(H)` of an internal R-node peel in the generic
flag regime, `c_i(Π) = 2 ⟹ ρ_i = 6`, at `Π = Π_x` and at `Π = Π_y`.* Since
`dim Π_x = 2`, `c_i(Π_x) = 2` is `Π_x ⊆ ρ̄_i`, so the **bad locus** is

> **`B := {z ∈ Chart(H) : Π_x(z) ⊆ ρ̄_i(z) and ρ_i(z) ≤ 5}`**, and
> **`B_str := {Σ_x ⊆ ρ̄_i, ρ_i ≤ 5}` ⊆ `B`** is the locus (BE-116) proves
> proper. **They are not equal** — (BE-125)(iii) exhibits the gap — and the
> whole of *Step BE124* is about why that does not matter.

### Step BE121 — (BE-122): (BE-69) read at source, and why it does not transport

> **(BE-122)(i)** *(**the ambient, reported before anything is done with
> it** — the forced job)* (BE-69)(i) is stated over **`Chart(H)`**, the same
> ambient this clause lives in, so the citation is **not** a category error
> and this is **not** `RESEARCH-ARC.md` §7's *INAPPLICABLE* shape. What
> differs is the **locus**. (BE-69)(i)'s subject is
>
> **`Good(H; x, y) = A ∩ GP`, `A := A₁ ∩ A₂`, `A_i = {rank R_i ≥ 6|V_i| − 6 − f_i}`,**
>
> the locus at which **the peel attains**; `GP` is
> `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂, 6)`. Its proof is, in its own words, *"plain
> rank **lower** bounds, never a codimension inference"*: `A_i` is a minor
> non-vanishing, and on `A` the coranks are constant, so `ρ̄₁ + ρ̄₂` is the
> image of a bundle and `dim(ρ̄₁+ρ̄₂)` is **lower** semicontinuous.

> **(BE-122)(ii)** *(**PROVED**; why that proof cannot be reused here)* The
> saturation good locus is
>
> **`Good_sat = {ρ_i = 6} ∪ {dim(ρ̄_i ∩ Π_x) ≤ 1}`,**
>
> a union of a rank **lower** bound (open) with an **upper** bound on an
> **intersection** dimension. Intersection dimension is upper
> semicontinuous **only on a locus where `ρ_i` is constant**, and `ρ_i` is
> merely lower semicontinuous on `A_i` — `ρ̄_i` is the *image* of the
> constant-rank bundle `M_i`, not the bundle. So `Good_sat` need not be
> open and `B` need not be closed, and **both failures are real**: `ρ_i` can
> drop from `6` to `5` in a limit that lands inside `B` (good → bad), and
> `ρ̄_i` can drop off `Σ_x` in a limit that leaves it (bad → good).
> **(BE-69)(i) therefore does not transport, and quoting it for this locus
> cannot be repaired by quoting it more carefully.**

> **(BE-122)(iii)** *(**the reading**, stated against BSATUR's, BSIGMA's and
> BPROPER's use of the citation)* All three landings wrote *"the good locus
> is Zariski-open on the irreducible `Chart(H)` and hence dense or empty
> ((BE-69))"*. For **their** conclusion — that the arc may work at a generic
> chart point — the load-bearing half of that sentence is **irreducible**,
> not **open**; the openness is what (BE-69) supplies for *its own* locus
> and is neither available nor needed for this one. So the landings' use is
> **sound in its conclusion and wrong in its warrant**, and *Step BE122*
> replaces the warrant. **No landed measurement moves, and no theorem is
> refuted.**

### Step BE122 — (BE-123): what the genericity half actually needs — CONSTRUCTIBILITY, and irreducibility at a PIECE

> **(BE-123)(i)** *(**PROVED**; `B` is constructible)* Stratify `Chart(H)`
> by the pair `(rank R_i, ρ_i)`. Each stratum is locally closed; on it
> `M_i = ker R_i` is a bundle of constant rank, `ρ̄_i` is its image under a
> morphism of bundles of constant rank, hence a **subbundle**, and both
> `Π_x ⊆ ρ̄_i` and `ρ_i ≤ 5` are closed conditions there. Finitely many
> strata, so
>
> **`B` is a finite union of locally closed sets — CONSTRUCTIBLE.** ∎
>
> The same argument applies verbatim to `B_str` and to `Π_y`.

> **(BE-123)(ii)** *(**PROVED**; the dichotomy that replaces (BE-69)(i))*
> Let `X` be irreducible and `C ⊆ X` constructible. Write
> `C = ⋃_k (U_k ∩ Z_k)` with `U_k` open and `Z_k` closed. If
> `closure(C) = X` then `closure(U_k ∩ Z_k) = X` for some `k`; that closure
> lies in `Z_k`, so `Z_k = X` and `U_k ∩ Z_k = U_k` is a **nonempty open
> subset of `X` contained in `C`**. Contrapositively,
>
> **if `C` contains no nonempty open subset of `X`, then `C` is nowhere
> dense and `X ∖ closure(C)` is a DENSE OPEN.** ∎
>
> **This is strictly weaker than what (BE-69)(i) proves and is exactly what
> "generic" needs.** It is why *Step BE122*'s negative result costs the arc
> nothing.

> **(BE-123)(iii)** *(**PROVED**; irreducibility at a **piece** — BPROPER's
> escape-clause item 2, which (BE-121)(iii) promoted to the residual)*
> (BE-65)(ii) already cites (CH-1)(a) for a piece's chart; the open question
> it left is whether (CH-1)'s three hypotheses are available at an arbitrary
> peel piece, in particular at a **non-path** side. They are, by
> inheritance, and the argument is two lines. Let `H ⊆ G` be a piece whose
> terminals have degree `≥ 3` in `H` ((BE-70)(i)). **Girth**: `H` is a
> subgraph, so `girth(H) ≥ girth(G) ≥ 4`. **Min degree 2**: interior
> vertices keep their `G`-degree and the terminals have degree `≥ 3`.
> **`hcard`**: `deg_H ≤ deg_G`, so a hub of `H` is a hub of `G` and
> `N_H(h) ⊆ N_G(h)`, whence `N_{Λ(H)}(h) ⊆ N_{Λ(G)}(h)` and
> `d_h(H) ≤ d_h(G) ≤ 2`. **All three inherit, with no reference to the
> side's topology at all.** ∎ Checked at **9/9** constructed peels
> (`bopen.py hyp`: `hcard` true, min degree `2`, girth `7–10`), and the
> terminals asserted to be hubs at every one.

> **(BE-123)(iv)** *(**PROVED**; the transfer between the two ambients)*
> `Φ : 𝒜(H) → Chart(H)` is dominant with `Φ(𝒜(H))` containing a dense open
> ((CH-1)(c)), and both are irreducible ((CH-1)(a)). If a constructible
> `C ⊆ Chart(H)` contains a nonempty open then so does `Φ^{-1}(C)`; and if
> `Φ^{-1}(C)` contains a nonempty open `V`, then `V` is dense in `𝒜(H)`, so
> `Φ(V) ⊆ C` is constructible and dense in `Chart(H)`, hence contains a
> nonempty open by (ii). **So `B` is nowhere dense downstairs iff
> `Φ^{-1}(B)` is nowhere dense upstairs** — and every fibration below is
> built **upstairs**, where the tower's equations live. ∎

### Step BE123 — (BE-124): the `p_x`-sweep, DISCHARGED by the tower

> **(BE-124)(i)** *(**PROVED**; the equations `q_x` appears in, listed
> exhaustively)* Read off §(K-chart) *Step CH3*'s tower — which
> (BE-65)(ii) states **is** (BE-64)(ii)'s parametrization, stage for stage —
> the defining equations of `𝒜(H)` are, for every hub `h` and every
> neighbour `u` of `h`,
>
> **`n_h · (q_u − q_h) = 0`**
>
> (stage 2 when `u` is a hub, stage 4 when it is not: the same equation).
> `q_x` therefore occurs in exactly two families: `n_h · (q_x − q_h) = 0`
> for the hubs `h ∼ x`, and `n_x · (q_u − q_x) = 0` for the neighbours `u`
> of `x`. Since `deg_i(x) = 1`, **`c` is `x`'s only side-`i` neighbour**, so
> with the whole core held fixed the equations that couple `q_x` to fixed
> data are
>
> - **`n_c · (q_x − q_c) = 0`, i.e. `q_x ∈ π_c`** — present **iff `c` is a
>   hub**, i.e. iff `deg_i(c) ≥ 3`;
> - **`n_x · (q_c − q_x) = 0`, i.e. `p_c ∈ π_x`** — a condition on `n_x`,
>   which is **not** core data.
>
> Every other equation involving `q_x` or `n_x` names a **side-2** vertex.
> **One structural proviso, and it is the peel's own:** `x ≁ y`, so `q_x`
> does not appear in `y`'s equations. That is (BE-118)(i)'s non-adjacency,
> which `bpeel.rnode_shaped` already forces. ∎

> **(BE-124)(ii)** *(**PROVED**; the fibre is exactly BPROPER's two
> ambients)* Fix a point of `𝒜(H)` and fix the core's points **and** its
> normals. Given a target `q_x'`, complete it to a point of `𝒜(H)` by
> solving the tower's equations in the order: `n_x'` (any plane through
> `q_x' ∨ q_c`, a pencil, nonempty), then side 2's hub points — placing in
> `π_x'` those adjacent to `x` — then side 2's normals (`ker A_h ≠ 0` by
> **`hcard`**, and the row `q_x' − q_h` of `A_h` is *itself* the equation
> `q_x' ∈ π_h`, so it costs nothing), then side 2's non-hub points (an
> intersection of hub planes, an affine subspace). Side 1 is untouched and
> `y`'s normal is kept, so its side-1 equations still hold and its side-2
> neighbours are placed in `π_y`. Hence
>
> **the `q_x`-fibre through a chart point, with the core fixed, contains a
> dense open subset of `π_c` (`c` a hub) resp. of `𝔸³` (`c` not a hub).**
>
> **And the completion is RATIONAL in the target, which is what (BE-127)(i)
> uses.** Every choice above is a linear solve — a section of the pencil
> `{n : n · (q_c − q_x') = 0}`, points of `Π(q_x', n_x')`, kernels of the
> `A_h(q)`, intersections of hub planes — so fixing one such choice gives a
> **rational map** `ψ : π_c ⇢ 𝒜(H)` (resp. `𝔸³ ⇢ 𝒜(H)`) with
> `q_x ∘ ψ = id`, regular on a dense open `W` containing the base point's
> own `q_x`. The open conditions `U_H`, `N°` hold at the base point, hence
> on a nonempty open of `W`, and `𝒫(H)` is dense open in `𝒜(H)`
> ((CH-1)(b)); shrink `W` to sit inside both. ∎
>
> **What this discharges, exactly.** (BE-116)(iii)(a) — *"that the fibre is
> genuinely swept … is **not proved here**"* — **is proved here**, and in
> **both** of (BE-116)(i)'s cases, with the ambient unchanged. BPROPER's
> `bproper.run_proper` swept `p_x` over a **claimed** freedom on a *side*
> draw and could not test chart-legality at all; here every target is
> rebuilt into a **full piece**.
>
> Measured, as an adversarial control on the construction rather than as
> the statement: **102/102** targets over **18** free peel draws on **9**
> composites realized as legal chart points, both gates
> (`assert_generic_star` **and** `verify_pencil_witness`), with the core
> asserted **unchanged as a placement**, `A` asserted **unchanged as a
> subspace**, and (BE-114)(i)'s identity re-asserted at the new `p_x`
> (`bopen.py fibre`). **14** of the 18 rows are the `c`-a-hub fibre and
> **4** the `𝔸³` one.

> **(BE-124)(iii)** *(**the one case not covered, named**)* The completion
> above chooses side 2's hub points freely. If `x` has a **side-2 hub
> neighbour** whose own `Λ`-component is a **cycle**, the greedy walk can
> over-constrain; BBASE's (BE-90)/(BE-91) settle exactly that object — the
> flag base is free on every component of cyclomatic number `≤ 1`, and
> `B_real` is a **forest at 78 564/78 564** class-tier peel pieces
> ((BE-93)'s population). **In this direction's own population `x` has NO
> hub neighbour at all** — `0/9` composites and `0` at all **91**
> `deg_i(x) ≥ 2` rows — so the sub-case is **unexercised here**, and that is
> disclosed rather than smoothed.

### Step BE124 — (BE-125): the flag rotation, and why (BE-116)'s locus is the right one after all

> **(BE-125)(i)** *(**PROVED**; the rotation fibre)* Fix a chart point and
> fix **all** of side 1, points and normals. Let `n_x` vary in
> `{n : n · (q_c − q_x) = 0}`, a 2-dimensional space, i.e. let `π_x` range
> over the **pencil of planes through the line `p_x ∨ p_c`** — precisely
> BSATUR's *legal pencil* ((BE-105)(i)) — and rebuild side 2 by (BE-124)(ii).
> Along that family `q_x` and the whole core are constant, hence
>
> **`ρ̄_i = ⟨ℓ⟩ + A` is CONSTANT**, and `Π_x = p_x ∧ π_x` varies.
>
> The family is a rational curve `σ : 𝔸¹ ⇢ 𝒜(H)` with `σ(0) = z`: `n_x(t)`
> is affine in `t`, side 2's hub points and normals are **constant** (their
> equations `n_h · (q_x − q_h) = 0` do not involve `n_x`), and the only
> stage-4 points that move — `x`'s side-2 neighbours — lie in an
> intersection of planes depending affinely on `t`, so Cramer gives a
> rational section. Asserted: `ρ̄_i` unchanged **as a subspace** and `p_x` unchanged,
> at every rotation of every row (`bopen.py slide`).

> **(BE-125)(ii)** *(**PROVED**; the collapse, and it is POINTWISE)* On a
> rotation fibre the bad condition `p_x ∧ π ⊆ ρ̄_i` is **closed** in `π`
> (`ρ̄_i` being constant), and `⋃_{π ⊇ p_x ∨ p_c} (p_x ∧ π) = Σ_x`, since
> every `t ∈ P³` lies in some plane of the pencil. Hence *bad at every `π`
> of the pencil* ⟺ **`Σ_x ⊆ ρ̄_i`** — which is (BE-105)(i)'s trichotomy
> re-derived from the fibration rather than from the pencil count. Now let
> `U ⊆ B` be a nonempty open of `𝒜(H)` and take `z ∈ U`. The rotation curve
> `σ` through `z` meets `U` in a nonempty open of `𝔸¹`, hence in a cofinite
> set; the bad set is closed along `σ`; so **every** `π` of the pencil is
> bad at `z`, i.e. `z ∈ B_str`. Therefore
>
> **`U ⊆ B` open ⟹ `U ⊆ B_str`, at every point of `U`.** ∎
>
> Both halves asserted: at **16/16** planted rows with `Σ_x ⊆ ρ̄₁`, **every**
> one of 10 rotations is bad; at **20/20** free rows with `Σ_x ⊄ ρ̄₁`, **no**
> sampled rotation is bad, and the `dim(ρ̄₁ ∩ Σ_x)` census over those rows is
> `{1: 16, 2: 4}`. At the **4** rows with `dim = 2` the **unique** bad plane
> is **CONSTRUCTED** — `q^{-1}(ρ̄₁ ∩ Σ_x)` — and asserted to be bad **and**
> to contain `p_c`, i.e. to lie in the legal pencil. *No sampled rotation
> ever meets it*, which is (BE-105)(iii) firing again and is why the middle
> case is built rather than drawn.

> **(BE-125)(iii)** *(**the control that makes (ii) load-bearing** — a
> CONSTRUCTED witness, `RESEARCH-ARC.md` §4 / README §4 convention 6)* A
> reader may ask why the flag rotation is needed when BPROPER already sweeps
> `p_x`. Because **at a FIXED flag the bad locus can be dense in the
> `p_x`-plane while `B_str` is a single point.** Take
> `π = ⟨e₁,e₂,e₃⟩`, `A = ⟨e₁∧e₃, e₂∧e₃, e₃∧e₄⟩` (so `dim A = 3`),
> `p_c = e₁`, `z = e₃`. Then `A ∩ Λ²π = z ∧ π` exactly, so for `p ∈ π`
>
> **`Π_p ∩ (⟨ℓ⟩ + A) = ⟨ℓ⟩ + ⟨p ∧ z⟩`, which is all of `Π_p` unless `z`
> lies on the line `p ∨ p_c`.**
>
> So the bad set is the **complement of one line** of `π` — it contains a
> nonempty open — while `{p : Σ_p ⊆ ⟨ℓ⟩+A}` is the **single point `p = z`**.
> Asserted as an **iff** on a 160-point grid, together with `nsat` hitting
> only `p = z` (`bopen.py weak`). **(BE-116)'s properness alone therefore
> does not give the chart clause; (BE-125)(ii) is what does.**

### Step BE125 — (BE-126): `a_i = 0` at a generic point is (BE-69)(i)'s own locus

> **(BE-126)(i)** *(**PROVED**; the identification, read at source)*
> `bunif.measure_row` returns `a_i = dim M_i − 6 − f_i` with
> `f_i = def₃(side_i)` (`bdecor.d3`), and (BE-22)(ii)'s partition cap gives
> `dim M_i ≥ 6 + f_i` **at every configuration**. Hence `a_i ≥ 0` always,
> and
>
> **`{a_i = 0} = {dim M_i = 6 + f_i} = {rank R_i ≥ 6|V_i| − 6 − f_i} = A_i`,**
>
> which is **verbatim** (BE-69)(i)'s `A_i` — the minor non-vanishing that
> clause proves **open**. ∎

> **(BE-126)(ii)** *(**PROVED**; hence generic, on the induction's own
> hypothesis)* `A_i` is open; `A_i ≠ ∅` is **(BE-14) for the side**, which
> (BE-69)(iii) already identifies as *"the 2-cut induction's own hypothesis,
> not a new obligation"*; `Chart(H)` is irreducible ((BE-123)(iii)). A
> nonempty open of an irreducible variety is dense, so
>
> **`a_i = 0` at a generic point of `Chart(H)`, for each side, PROVED.** ∎
>
> This discharges (BE-116)(iii)(c) and BPROPER's price (b) second half.
> **It is not a new theorem about body-hinge counts** — it is the
> observation that the arc's own `a_i` and (BE-69)(i)'s own `A_i` are the
> same object, which no landing had made.

> **(BE-126)(iii)** *(**MEASURED**, and disclosed as a signature only)* Over
> BSIGMA's **29**-topology side library, 5 blind draws each: `a_i ≥ 0` at
> every draw (the cap, asserted), the generic `a_i` is `0` at **29/29**, and
> the **first** draw attains the minimum at **29/29** — (BE-69)(iii)'s own
> openness signature, read for `a_i` rather than for `reach`
> (`bopen.py amax`). **This is a statement about one side's own chart, one
> quantifier away from `Chart(H)`**, which is why (ii) proves it rather than
> quoting these rows.

### Step BE126 — (BE-127): the assembly, and the side-degree-`≥ 2` half

> **(BE-127)(i)** *(**THE THEOREM**)* Let `H` be an internal R-node peel at
> `{x, y}` with `x ≁ y`, satisfying (CH-1)'s hypotheses, and let `side_i`
> have `deg_i(x) = 1`. Then
>
> **`{z ∈ Chart(H) : c_i(Π_x) = 2 and ρ_i ≤ 5}` is NOWHERE DENSE, so
> `c_i(Π_x) = 2 ⟹ ρ_i = 6` holds on a DENSE OPEN subset of `Chart(H)`.**
>
> *Proof.* Work upstairs ((BE-123)(iv)). `B` is constructible ((BE-123)(i)),
> so by (BE-123)(ii) it suffices that `B` contain no nonempty open. Suppose
> `U ⊆ B` is one. By (BE-125)(ii), **`U ⊆ B_str` pointwise**. Pick
> `z ∈ U ∩ 𝒫(H)` and let `ψ : W ⇢ 𝒜(H)` be (BE-124)(ii)'s **rational**
> completion through `z`, with `W` a dense open of `π_c` (resp. of `𝔸³`) and
> `ψ(q_x(z)) = z`. Then `ψ^{-1}(U)` is **open and nonempty** in `W`, hence
> **dense**, and every `q_x'` in it has `ψ(q_x') ∈ U ⊆ B_str`, i.e. is BAD
> for `Σ`. So `{q_x' : Σ_{q_x'} ⊆ ⟨q_x' ∧ p_c⟩ + A}` is **dense** in `π_c`
> (resp. `𝔸³`) — the core, hence `A` and `p_c`, being constant along `ψ` by
> construction. But by (BE-114)(ii) + (BE-115) that set is a **proper
> closed** subset there: clause (a) for the `ℓ ∈ A` branch, clause (b) for
> the other, with (BE-115)(iii)'s single exception `Λ²π_c ⊆ A` neutralized
> by `p_c ∈ π_c` (resp., in the `𝔸³` case, the exceptional locus being the
> plane `π′`, itself proper in `𝔸³`). Contradiction. ∎
>
> **Symmetrically at `Π_y` when `deg_i(y) = 1`.** So the clause is a theorem
> at **every (side, terminal) instance of side-degree `1`** — which is every
> instance where BSATUR's, BSIGMA's and BPROPER's refutations and repairs
> lived, and the only place the flag carries freedom at all ((BE-105)(iv)).

> **(BE-127)(ii)** *(**PROVED**; the reduction at `deg_i(x) ≥ 2`, and it is
> sharper than (BE-119)(i))* Let `deg_i(x) = k ≥ 2` with side neighbours
> `c₁, …, c_k`. By (BE-105)(iv) `Π_x = ⟨ℓ₁, ℓ₂⟩` and by (BE-114)(iv)
> `ρ̄_i ⊆ ⟨ℓ₁⟩ + A`, `A` the same `p_x`-free core space. So `Π_x ⊆ ρ̄_i`
> forces `ℓ₂ ∈ ⟨ℓ₁⟩ + A`, i.e.
>
> **`p_x ∧ t ∈ A` for some `t` on the FIXED line `L_c := p_{c₁} ∨ p_{c₂}`.**
>
> Let `J := {(p, t) ∈ P³ × L_c : p ∧ t ∈ A}`. Its fibre over `t` is
> `P(q_t^{-1}(A ∩ Σ_t))`, of projective dimension `dim(A ∩ Σ_t)`. Hence the
> bad locus is proper in `p_x` under
>
> > **`(∗)`  `Σ_t ⊄ A` for every `t ∈ L_c`, **and** `{t ∈ L_c : dim(A ∩ Σ_t) ≥ 2}` is FINITE.**
>
> Both halves fail only in ways that are *exactly* certifiable: the first is
> **LINEAR in `t`** (`f(t ∧ e_j) = Σ_k t_k f(e_k ∧ e_j)` for every `f`
> vanishing on `A`), so `{t : Σ_t ⊆ A}` is a computable subspace; the second
> is a Zariski-closed condition on the line, so **one** `t ∈ L_c` with
> `dim(A ∩ Σ_t) ≤ 1` certifies it. This is **stronger** than (BE-119)(i),
> which needed `dim A ≤ 4` and reached only `B_str`. ∎

> **(BE-127)(iii)** *(**MEASURED**; `(∗)` at BPROPER's own population)* Over
> BPROPER's **16**-topology `deg_i(x) ≥ 2` library at its own seeds — **91**
> rows, reproducing (BE-119)(ii)'s count exactly — **both halves of `(∗)`
> are certified EXACTLY at 91/91**, `dim A ∈ {1: 16, 2: 34, 3: 41}`, and `x`
> has **0** hub side-neighbours at every row, so the `p_x` fibre there is all
> of `𝔸³`. The population carries **no bad row at all** (reproducing
> (BE-119)(ii)'s *none found under that cap*), so the reduction's own assert
> **never fired** — disclosed (F13), not counted as evidence
> (`bopen.py degx`). **`(∗)` is a CONDITION, certified here, never proved**,
> and that is what half (B)'s item 1 is left with.

> **(BE-127)(iv)** *(**the consumer**, stated exactly)* Under (i),
> (BE-101)(i)/(ii) hold at a generic chart point **with the clause now a
> theorem rather than a hypothesis at every side-degree-`1` terminal**, so
> the `14 → 12` block drop stands there. (BE-112)(iv)'s warning is
> **unchanged and still binds**: a statement quantified over *every* chart
> point — a closure argument, or a degeneration that lands on a stratum —
> still does not get the clause, because *nowhere dense* is not *empty*, and
> (BE-106)(ii)'s 24 escapees are still the price off the dense open.

### Step BE127 — (BE-128): the price, the board, the reading, the E-rider

> **(BE-128)(i)** *(**MEASURED**; the shortfall control, and item 0(c) is
> untouched)* At **54** further peel rows — **27** planted, **27** free, over
> 9 composites × 3 seeds — **asserted**: `margin ≤ 0` at `Π_x`, at `Π_y` and
> at `⟨M⟩`; and `reach = min(δ₁+δ₂,6) + a₁ + a₂` at every **free** row
> (27/27, so those peels **attain**). Margin histogram at `Π_x`:
> `{−3: 3, −2: 15, −1: 21, 0: 15}`. **0 shortfalls.**
> `notes/Phase39.md` *Hand-off* item 0 sub-item (c) — a `margin > 0` row at
> `Π_x`/`Π_y`/`⟨M⟩` — is **not** exhibited and **stays open**, for the
> fourth direction running.

> **(BE-128)(ii)** *(**the board**)* **What moved.** (PENCIL-SATURATES-CHART)
> is a **theorem** at every side-degree-`1` terminal, so half (B)'s **item 1
> closes there**; the `p_x`-sweep and `a_i = 0` are **PROVED**, not measured;
> (BE-69) is **retired as the warrant** and replaced by constructibility +
> irreducibility; `Chart(H)`'s irreducibility at a piece — BPROPER's escape
> item 2 — is **settled by inheritance**; (BE-119)(i)'s `dim A ≤ 4`
> hypothesis is **replaced** by the sharper `(∗)`, certified 91/91; and the
> `Π_x`-vs-`Σ_x` gap, which no landing had noticed, is **located, exhibited
> and closed**. **What did not move.** `PencilPair K 3 G`, `hbareSplit`,
> `hK`, (GR-15), (BE-14), the 2-cut step, half (B) as a whole, class
> uniformity, cross-pair welding — **all untouched**; **no shortfall is
> exhibited**; the **11** unwitnessed blocks are still unwitnessed; the
> side-degree-`≥ 2` instances are **not** proved; (BE-110)(ii) stands as the
> path theorem it was; and **not one landed measurement is refuted** —
> (BE-116) is used verbatim.

> **(BE-128)(iii)** *(**the coordinator's reading**, classified)* The reading
> was: *"the three gaps are not equally hard, and two of them may be
> corollaries of the pendant reduction … if `Chart(H)` fibres over the core
> with `π_c`-fibres, the sweep input should follow from the chart's own
> construction rather than needing (BE-69) at all; `a_i = 0` generically
> looks like the genuinely separate one."*
>
> - **The main claim is CONFIRMED and load-bearing.** The chart **does**
>   fibre that way, the sweep **does** follow from the tower ((BE-124)), and
>   (BE-69) is indeed **not needed** ((BE-122)/(BE-123)). The prediction
>   named the right mechanism and the right object.
> - **Its second half is REFUTED, with the sign inverted.** `a_i = 0` is not
>   the separate hard one; it is the **cheapest** of the three, being
>   (BE-69)(i)'s own `A_i` ((BE-126)). The one the reading did not name at
>   all — that the clause is stated at `Π_x` and (BE-116) proves properness
>   at `Σ_x` — is where the genuine work sat ((BE-125)).
> - **Expected-wrong item 1** (*the chart may not fibre that way*) —
>   **REFUTED**; it does.
> - **Expected-wrong item 2** (*(BE-69) may be stated for a locus of a
>   different shape, in which case the residue is larger*) — **SPLIT, and it
>   is the informative one**: the **diagnosis is exactly right** (different
>   locus, and the proof does not transport), and the **consequence is
>   inverted** — the residue is **smaller**, because openness was never what
>   "generic" needed. A prediction can be right about a defect and wrong
>   about its cost.
> - **Expected-wrong item 3** (*`a_i = 0` may not be provable at this
>   stratum*) — **REFUTED**.
> - **Tally**: `RESEARCH-ARC.md` §7 stands at **fourteen instances, seven
>   kinds**; this landing is **cited against it and does not increment it**
>   — the coordinator reconciles the counter after the round, per the
>   2026-09-02 finding that a shared monotone counter cannot be concurrently
>   incremented. Offered for that reconciliation: a **CONFIRMED** main
>   reading with one **SPLIT** escape clause, the same half-instance shape
>   BPROPER's SPLIT was recorded as.

> **(BE-128)(iv)** *(classification, mandatory and explicit)* **What is
> proved**: (BE-122)(ii), (BE-123) in full, (BE-124)(i)/(ii), (BE-125)(i)/(ii),
> (BE-126)(i)/(ii), (BE-127)(i)/(ii). **What is measured, not proved**:
> `(∗)` at the side-degree-`≥ 2` instances ((BE-127)(iii)); every count in
> (BE-124)(ii), (BE-125)(ii)/(iii), (BE-126)(iii) and (BE-128)(i), all of
> which are **controls on arguments**, not the arguments. **What is cited**:
> (CH-1)(a)/(b)/(c) and (CH-2) (proven-informally in §(K-chart)); (BE-114),
> (BE-115), (BE-116), (BE-105)(i)/(iv), (BE-114)(iv), (BE-22)(ii),
> (BE-69)(i)/(iii), (BE-70)(i), (BE-65)(ii) — all landed. **What is
> refuted**: nothing — one **warrant** is replaced ((BE-122)(iii)) and one
> **hypothesis** is weakened ((BE-127)(ii) vs (BE-119)(i)). **What is NOT
> refuted**: `PencilPair K 3 G`; `hbareSplit`; (BE-14); half (B); (BE-116);
> (BE-110)(ii); (BE-101); **any** landed measurement. **One question is
> CLOSED** (item 1 at side-degree `1`) and **one is narrowed** (item 1
> becomes `(∗)` at side-degree `≥ 2`). **Not a PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 1 — the target CLOSES at every side-degree-`1` terminal.**
  (PENCIL-SATURATES-CHART) is a **THEOREM** there ((BE-127)(i)), so half
  (B)'s item 1 is closed at every instance where the clause has ever
  failed, and `14 → 12` stands generically.
- **HIT shape 2 — both of BPROPER's measured inputs are PROVED.** The
  `p_x`-sweep from the tower ((BE-124)); `a_i = 0` generically as
  (BE-69)(i)'s own `A_i` ((BE-126)).
- **HIT shape 3 — the forced job answers NEGATIVELY and that is a full
  result.** (BE-69) is the **wrong citation** for this locus, and it is
  **not needed** ((BE-122)/(BE-123)) — a citation retired without a
  measurement moving.
- **HIT shape 4 — a gap no landing had noticed, located and closed.** The
  clause is at `Π_x`; (BE-116) proves properness at `Σ_x`; the two differ,
  demonstrably ((BE-125)(iii)), and the flag rotation closes the difference
  **pointwise** ((BE-125)(ii)).
- **HIT shape 5 — BPROPER's escape item 2 is SETTLED** ((BE-123)(iii)), by
  inheritance and in two lines.
- **The coordinator's reading: CONFIRMED**, with escape item 2 **SPLIT**
  ((BE-128)(iii)).
- **NOT HIT** — **half (B) is not discharged**, and the clause is **not**
  proved at side-degree `≥ 2`, where it rests on `(∗)`: certified 91/91,
  **not proved**. *(**SUPERSEDED 2026-09-02, direction BLINE**: `(∗)` is
  DECIDED — a theorem below `dim A = 3`, FALSE from `dim A = 5`, so this
  route is DEAD and the 91/91 was a COROLLARY, not evidence
  ((BE-129)–(BE-132)). The clause itself is still OPEN here.)*
- **The price, stated as a price.** **(a)** `(∗)` is a **condition**, not a
  theorem; its two halves are exactly certifiable and were certified at 91
  rows of a **16**-topology constructed library, never a census.
  **(b)** (BE-124)(ii)'s completion chooses side 2's hub flags freely; a
  side-2 hub neighbour of `x` whose `Λ`-component carries a cycle is
  **outside** the construction, and is **unexercised** in this population
  (`0/9`, `0/91`) — BBASE's (BE-90)/(BE-91) are what would cover it.
  **(c)** The theorem is stated at `deg_i(x) = 1` and needs `x ≁ y`; both
  are the peel's own hypotheses ((BE-118)(i)), and neither is new.
  **(d)** Everything downstream of (CH-1)/(CH-2) inherits their
  **proven-informally** status; this direction adds no rigour there.
  **(e)** *Nowhere dense* is not *empty*: (BE-112)(iv)'s warning stands
  verbatim, and the 24 escapees of (BE-106)(ii) are still the price off the
  dense open.
  **(f)** The peel population is **constructed** — 9 composites, 2
  skeletons, one branch profile (all 3s) — and every "N/N" above is a
  statement about it under seed `20260902`.
  **(g)** Exact ℚ only; the proofs are characteristic-free, the numerics are
  not.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py hyp        #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py weak       #    0.1 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py amax       #   20.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py fibre      #   47.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py slide      #   76.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py degx       #   31.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py price      #  105.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py support    #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bopen.py validate   #  281.1 s (all eight)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single
seed is `20260902` (`bunif.SEED`), printed by every mode; `validate` fits
the 600 s foreground budget. Every headline is an `assert`, not a report:
(CH-1)'s three hypotheses and the terminals' hub-ness at 9/9 peels; the
`weak` control as an **iff** on 160 points with `B_str` asserted to be the
single point `p = z`; `a_i ≥ 0` at every draw and the first-draw minimum at
29/29; the full rebuild at 102/102 targets with the core asserted unchanged
and `A` asserted the same subspace; `ρ̄₁` asserted constant along every flag
rotation, with *every* rotation bad at 16/16 planted rows, *no* rotation bad
at 20/20 free rows, and the constructed bad plane asserted bad and legal at
the 4 rows where one exists; both halves of `(∗)` at 91/91; and
`margin ≤ 0` at the three 2-blocks plus attainment at every free row, 54
rows.

### Caps, disclosed rather than smoothed — with the denominator named

1. **(BE-122), (BE-123), (BE-124)(i)/(ii), (BE-125)(i)/(ii), (BE-126)(i)/(ii)
   and (BE-127)(i)/(ii) need no cap** — they are proofs; the driver can only
   falsify them.
2. **The rebuild population is 9 composites × 2 free draws × 6 targets.**
   *"102/102 realized"* is a statement about those targets under seed
   `20260902`; it is evidence that the construction of (BE-124)(ii) runs,
   not a rate.
3. **The rotation population is 10 planes per row over 36 rows.** A sampled
   rotation **cannot** meet the unique bad plane at a `dim = 2` row — which
   is why that case is **constructed**; *"20/20 free rows, no bad rotation"*
   is therefore evidence about the generic flag only.
4. **`(∗)` at 91 rows over 16 topologies**, BPROPER's own library and seeds;
   `dim A ≥ 5` and any bad row are **not found under that cap**, never
   *"cannot happen"*. Only the lexicographically first retained pendant edge
   `c₁` is exercised.
5. **`a_i = 0` at 29 library sides, 5 draws each** — a **side** chart, one
   quantifier away from `Chart(H)`. (BE-126)(ii) is what covers the gap;
   the rows are a signature.
6. **The shortfall control is 54 constructed rows**, one branch profile, two
   skeletons. *"0 shortfalls"* is about those rows and is not a census.
7. **Everything inherits `bearcase.sample_piece_config`'s shape guard** and
   `bpeel.rnode_shaped`'s disclosed stand-in, unchanged from BSIGMA and
   BPROPER.
8. **`x` has no hub neighbour anywhere in this population** (`0/9`, `0/91`),
   so (BE-124)(iii)'s named sub-case is **unexercised**.

### Harness note — the `w4/` sibling-import set gains a consumer, and `bproper`'s peel constructors reach their SECOND

`w4/bopen.py` imports `bproper`, `bsigma`, `bsatur`, `bunif`, `bdecor`,
`bpeel`, `bimage`, `exactcore` and `kbare_common` read-only and reimplements
none of them: no `ρ̄`, no deficiency oracle, no block decomposition, no row
measurement, no margin arithmetic, no planter and no peel constructor.
**A NEW, UNPAID debt item is created and disclosed**: `bproper.composite`,
`bproper.plant_peel`, `bproper.free_peel`, `bproper.degx_library`,
`bproper.plant_side`, `bproper.reduction_data`, `bproper.core_of`,
`bproper.side_named` and `bproper.PEELJOBS` now have a **second** consumer,
which by `notes/scripts/README.md` §2 rule 2 is the signal to move the peel
constructors down — **no move made**, deliberately: they are one direction
old, and a move-down would re-baseline BPROPER's eight recorded figures for
no mathematical gain. Recorded in that file's *Harness debt*.

**No divergence is created.** `bopen.slide` and `bopen.chart_data` are new
devices, not variants of existing ones; `bopen.bad_plane` is the
**constructive** inverse of (BE-105)(i)'s `q`, which no driver had.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-122)(i) (BE-69)'s ambient and locus, read at source | **VERIFIED AT SOURCE** — the clause opened, not paraphrased |
| (BE-122)(ii) the openness proof does not transport | **PROVED** (semicontinuity directions), with both failure modes exhibited in prose |
| (BE-123)(i) `B` is constructible | **PROVED** (finite rank stratification) |
| (BE-123)(ii) constructible + irreducible ⟹ dense-or-nowhere-dense | **PROVED** (elementary; stated in full) |
| (BE-123)(iii) (CH-1) inherits at a piece | **PROVED**; checked 9/9 — BPROPER escape item 2 CLOSED |
| (BE-123)(iv) upstairs/downstairs transfer | **PROVED** from (CH-1)(a)/(c) + Chevalley |
| (BE-124)(i) the equations `q_x` occurs in | **PROVED** from the tower, read at source |
| (BE-124)(ii) the fibre is `π_c` resp. `𝔸³` | **PROVED**; construction exercised 102/102 |
| (BE-124)(iii) the uncovered sub-case | **NAMED**, unexercised (0/9, 0/91) |
| (BE-125)(i) the rotation fibre | **PROVED**; `ρ̄₁` asserted constant at every rotation |
| (BE-125)(ii) the pointwise collapse | **PROVED**; both halves asserted, 16/16 and 20/20 |
| (BE-125)(iii) the fixed-flag control | **CONSTRUCTED**, asserted as an iff on 160 points |
| (BE-126)(i) `{a_i = 0} = A_i` | **PROVED** (definition + (BE-22)(ii)), source-read |
| (BE-126)(ii) hence generic | **PROVED**, given (BE-14) for the side |
| (BE-127)(i) the clause at side-degree `1` | **PROVED**, modulo (CH-1)/(CH-2)'s proven-informally status |
| (BE-127)(ii) the `deg_i(x) ≥ 2` reduction + `(∗)` | **PROVED**; strictly sharper than (BE-119)(i) |
| (BE-127)(iii) `(∗)` at BPROPER's library | **MEASURED**, 91/91 exactly certified; reduction assert **never fired** (disclosed) |
| (BE-128)(i) no shortfall at the 2-blocks | **MEASURED + ASSERTED**, 54 rows; item 0(c) stays OPEN |
| (BE-128)(iii) the reading | **CONFIRMED**, escape item 2 **SPLIT** |

### What would change this

- **A proof of `(∗)`, or a side with `deg_i(x) ≥ 2` violating it.** That is
  now the whole of item 1, and it is a statement about **one fixed line**
  against **one fixed subspace** — smaller than anything item 1 has carried.
- **A peel with `x` adjacent to a side-2 hub on a cyclic `Λ`-component**,
  where (BE-124)(ii)'s completion is not built and BBASE's (BE-90)/(BE-91)
  would have to be invoked.
- **A `margin > 0` row at `Π_x`, `Π_y` or `⟨M⟩`** — still item 0(c), still
  unexhibited after 54 further rows, and still outranking this direction's
  target if it appears.
- **Anything that needs the clause at EVERY chart point** rather than at a
  generic one — (BE-112)(iv)'s warning, unchanged.
- **A defect in (CH-1) or (CH-2)**, on which everything here stands.

## TERMINATION check (E1/E2/E3) — read at source, decided explicitly

Read at `notes/Pencil-fanout-archive.md` (the ledger's own statement, not by
analogy), each decided:

- **(E1)** — *a g-flank: a `D = 0` shape whose every admissible colouring is
  binding, refuting per-shape (GR-15)*. **DOES NOT FIRE.** This direction is
  on the `(K-bare)` line and exhibits no colouring object at all; (GR-15) is
  untouched.
- **(E2)** — *the target is refuted or unprovable-as-posed **and** no ledger
  entry is left open-with-a-named-dispatchable-attack*. **DOES NOT FIRE**,
  on both conjuncts: the target is a **HIT** at side-degree `1`, and the
  residue — `(∗)` at side-degree `≥ 2` — is a named, dispatchable attack.
- **(E3)** — *the target is **proven** and every remaining ledger entry is
  adjudication-gated rather than dispatchable*. **DOES NOT FIRE, and the
  first conjunct is worth stating carefully**: half (B)'s **item 1** is
  proven at side-degree `1`, but *the target* in E1–E3 is the **arc's**
  (`61e046a6`: emptying one lane's list does not fire it), and (BE-14),
  `hbareSplit` and `hK` are all untouched. Dispatchable entries remain —
  `(∗)`, the 11 unwitnessed blocks, cross-pair welding, the `hK` lane's
  (GR-138) successors.

**Per the "otherwise" clause the natural next step is a further direction**;
this landing does not prep one. See `notes/Phase39.md` *Hand-off*.
