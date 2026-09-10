## §(K-bare-ext) — continuation (direction BUNIF): **`reach` IS A FUNCTION OF TWO PER-SIDE PROFILES, AND BOTH DIRECTIONS OF THE LAW ARE PROVED** — the flag pair `(ϕ_x, ϕ_y)` has a **5-dimensional stabilizer** `S(ϕ) ⊆ PGL₄` which, by (BE-70)(ii), acts on **each side's achievable family separately**; in the generic flag regime the screw space splits `S(ϕ)`-canonically as `Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩ ⊕ Π_y` of dimensions `(2,1,1,2)`, whose **16 sums are exactly the `S(ϕ)`-stable subspaces**. Against those 16 the modular law gives a **CAP** on `dim(ρ̄₁+ρ̄₂)` written entirely in per-side data, and degenerating each side independently along a 1-PS of `S(ϕ)` gives a matching **LOWER BOUND** — so where the two agree (**121 of 122** measured peel rows, **393/400** abstract pairs) `reach` is **PINNED BY TWO PROOFS** and (BE-71)(ii)'s explicitly-unclaimed completeness is **CLOSED at that row**: the mechanism list is not merely long enough, it is *the lattice of stable subspaces*, with two-sided (P) the `U = core₁ ∩ core₂` instance and two-sided (Z) the `U = Π_x ⊕ Π_y` one. The cap is **ATTAINED by a group move at 400/400** abstract pairs. So **(BE-67)(iii) at a peel becomes 14 numerical inequalities `c₁(U) + c₂(U) ≤ dim U + max(0, δ₁+δ₂−6)`, each side's `c_i(U) = dim(ρ̄_i ∩ U)` computed on ITS OWN**, which is the *"statement about ONE piece, not about two pieces in relative position"* (BE-22)(vi) named as the successor's target. Measured: the violation margin is `0` at **92/92** rows — never positive, so **no shortfall** — and `Π_x` is the **ONLY** block at which BOTH sides exceed the generic profile (12 of 92), where they sit at `c₁ = c₂ = 1 = dim Π_x / 2` and the class statement survives by **EXACTLY ZERO MARGIN**, tight at **8** rows. That is the whole residue, and it is (BE-45)'s dichotomy read at both ends of one peel. The law is stated for the **generic flag regime only**: at `π_x = π_y` the four blocks collapse (`Π_x + Π_y = Λ²π`, `Π_x ∩ Π_y = ⟨M⟩`, both asserted), the cap survives because it is the modular law, and (BE-71)(i)'s two-sided (Z) at `dim Z = 3` is **exhibited losing dimension outright at 24 of 60** constructed ear pairs

**Direction BUNIF** (ordinal 63, `notes/pencil/fanout.md` §"BUNIF"), 2026-09-02.
Driver `notes/scripts/w4/bunif.py`; labels **(BE-94)–(BE-98)**, *Steps BE93–BE97*.
Read against *Steps BE68–BE72* (BPEEL), which this continues, and *Steps
BE63–BE67* (BDECOR), whose (BE-67)(iii) is the target.

### Standing notation

`H` an internal R-node piece with a peel at `{x, y}` (a virtual edge of a
simple 3-connected skeleton, so `xy ∉ E(H)`), sides `H₁, H₂` with
`V(H₁) ∩ V(H₂) = {x, y}`. `Λ²K⁴` is the 6-dimensional screw space,
`ρ̄_i ⊆ Λ²K⁴` the side's relative screw space ((BE-22)(i)), `ρ_i = dim ρ̄_i`,
`δ_i = f_i − g_i`, `a_i = dim M_i − 6 − f_i` ((BE-86)(i)). At a flag pair
`ϕ = ((p_x, π_x), (p_y, π_y))`:

- **`Π_z := p_z ∧ π_z`** — the pencil of hinge lines at `z`, 2-dimensional and
  totally singular ((BE-30)(ii));
- **`M := p_x ∨ p_y`** and **`L := π_x ∩ π_y`**, each a line of `P³`, i.e. a
  **point** of the Klein quadric, so `⟨M⟩` and `⟨L⟩` are 1-dimensional;
- **`E := Π_x + Π_y`**, `Σ_z := p_z ∧ K⁴` (the star of lines through `p_z`),
  `Λ²π_z` (the lines inside `π_z`).

**The GENERIC flag regime** is `π_x ≠ π_y`, `p_x ∉ π_y`, `p_y ∉ π_x` —
equivalently `(p_x, e₁, e₂, p_y)` is a basis of `K⁴` for any basis `e₁, e₂`
of `L`. It is BE-22(v)'s regime **(β)**. The complement is *Step BE96*.

### Step BE93 — (BE-94): the flag pair's stabilizer, and the four blocks

> **(BE-94)(i)** *(proven; **the stabilizer, computed**)* In the generic
> regime put `e₀ = p_x`, `e₃ = p_y` and `e₁, e₂` a basis of `L`. Then
> `π_x = ⟨e₀, e₁, e₂⟩` and `π_y = ⟨e₁, e₂, e₃⟩`, and
>
> **`S(ϕ) := Stab_{PGL₄}(p_x, π_x, p_y, π_y) = {diag(λ, A, μ) : A ∈ GL₂}/K^×`,
> of dimension 5.**
>
> *Proof.* `g` fixes `e₀` and `e₃` up to scale. Preserving `π_x` forces
> `g(e₁), g(e₂) ∈ ⟨e₀,e₁,e₂⟩`; preserving `π_y` forces them into
> `⟨e₁,e₂,e₃⟩`; the intersection is `L`. So `g` is block-diagonal, with
> `1 + 4 + 1 − 1 = 5` parameters. ∎ This **recovers (BE-22)(v)(β)'s count**
> (*"residual gauge group dimension 5"*) with the group itself named, and it
> **contains the maximal torus** of `PGL₄` in this frame — which is what the
> degeneration of *Step BE95* needs and a bare dimension count does not give.

> **(BE-94)(ii)** *(proven from (BE-70)(ii); **it acts on EACH SIDE
> SEPARATELY**, and that is the load-bearing clause)* `Achieve_i(ϕ)` — side
> `i`'s achievable `ρ̄_i` at the fixed flag pair — is **`S(ϕ)`-invariant**, and
> the two sides may be moved **independently**:
>
> **for `g ∈ S(ϕ)` and `(V₁, V₂)` achievable at `ϕ`, so is
> `(Λ²g·V₁, V₂)` — modulo `G`.**
>
> *Proof.* A configuration `c` of `H_i` with terminal flags `ϕ` is carried by
> `g` to a configuration with terminal flags `g·ϕ = ϕ`; every hinge line goes
> to `Λ²g` of itself and the body-hinge kernel transports, so
> `ρ̄_i(g·c) = Λ²g·ρ̄_i(c)`. Independence of the two sides is (BE-70)(ii): no
> topological branch crosses the 2-cut, the branch index set splits `B₁ ⊔ B₂`,
> and at fixed `ϕ` the achievable pairs are the full product modulo `G`. ∎
>
> Measured (`bunif.py equiv`), and **every line an assert**: at **30/30**
> (piece, peel, draw) rows a constructed `g ∈ S(ϕ)` fixes `p_x, π_x, p_y, π_y`
> **as spaces**, carries **both** `ρ̄₁` and `ρ̄₂` to `Λ²g` of themselves **as
> spaces**, and — applied to **side 1's interior vertices only** and reglued —
> passes `assert_generic_star` **and** `verify_pencil_witness` with `ρ̄₁`
> moved and `ρ̄₂` **unchanged as a space** at **30/30**. That one-sided
> regluing is (BE-70)(ii) **in group form**, and it is the measurement the
> whole direction stands on.

> **(BE-94)(iii)** *(proven; **the four blocks**, and the lattice)* As an
> `S(ϕ)`-module,
>
> **`Λ²K⁴ = Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩ ⊕ Π_y`, of dimensions `(2, 1, 1, 2)`,**
>
> with `Π_x ≅ λ ⊗ W`, `Π_y ≅ μ ⊗ W`, `⟨M⟩ ≅ λμ`, `⟨L⟩ ≅ det W` for `W` the
> standard `GL₂`-module. The four blocks carry **pairwise distinct** characters
> of the maximal torus, and `Π_x, Π_y` are `GL₂`-irreducible with **different**
> torus weights, so
>
> **the `S(ϕ)`-stable subspaces of `Λ²K⁴` are EXACTLY the 16 sums of blocks.**
>
> Among them: `E = Π_x ⊕ Π_y`, `Σ_x = Π_x ⊕ ⟨M⟩`, `Λ²π_y = Π_y ⊕ ⟨L⟩`,
> `Σ_y = Π_y ⊕ ⟨M⟩`, `Λ²π_x = Π_x ⊕ ⟨L⟩`. Asserted as a **direct sum** at
> every row of `equiv` and `law` (**152** rows), and the four-block spans are
> checked against `bimage.pencil_space` / `lam2` rather than rebuilt.
>
> **Why this is the right index set.** `c_i(U) := dim(ρ̄_i ∩ U)` is
> `S(ϕ)`-invariant exactly when `U` is stable, and only then is it an
> invariant of the *family* `Achieve_i(ϕ)` rather than of a chosen member.
> That is what turns the next step's inequality into **per-side data**.

### Step BE94 — (BE-95): the block cap, and the two located mechanisms as instances

> **(BE-95)(i)** *(proven; **the cap** — one line, and it is the modular law)*
> For every subspace `U`,
> `dim(ρ̄₁ ∩ ρ̄₂) ≥ dim((ρ̄₁∩U) ∩ (ρ̄₂∩U)) ≥ c₁(U) + c₂(U) − dim U`. Hence
>
> **`dim(ρ̄₁ + ρ̄₂) ≤ blockcap := min over the 16 stable `U` of
> `ρ₁ + ρ₂ − max(0, c₁(U) + c₂(U) − dim U)`.** ∎
>
> The `U = Λ²K⁴` term is `min(ρ₁+ρ₂, 6)`, so the cap **contains** the trivial
> bound; the `U = 0` term is vacuous. Fourteen terms are new.

> **(BE-95)(ii)** *(proven; **(BE-71)'s two mechanisms are instances**, which
> is the reason to believe the list)* `core_i(ϕ) := ⋂ Achieve_i(ϕ)` is
> `S(ϕ)`-invariant, hence by (BE-94)(iii) a **sum of blocks**. So:
>
> - **two-sided (P)**, `loss ≥ dim(core₁ ∩ core₂)`, is the cap's
>   `U = core₁ ∩ core₂` instance, where `c_i(U) = dim U`;
> - **two-sided (Z)** at `Z = E` (the `π_x ≠ π_y` case of (BE-71)(i)) is the
>   `U = Π_x ⊕ Π_y` instance verbatim.
>
> **(BE-71)(iii)'s Klein-ruling candidate is likewise inside**: it collapses
> into two-sided (Z), and (Z) is a cap term. So the direction's contribution to
> (BE-71)(ii) is not *"we looked for a third mechanism"* — it is that **the
> whole mechanism question is a question about ONE inequality family**.

### Step BE95 — (BE-96): the block law — the cap is ATTAINED, so `reach` is per-side data

> **(BE-96)(i)** *(proven; **the degeneration lower bound**)* Let `V_i` be a
> generic member of `Achieve_i(ϕ)`. For a 1-PS `λ(t) = diag(t^a, 1, 1, t^b)` of
> the **central** torus of `S(ϕ)` the four blocks are weight spaces, with
> weights `(a, a+b, 0, b)` on `(Π_x, ⟨M⟩, ⟨L⟩, Π_y)`; write
> `β^σ(V) ∈ Z^4_{≥0}` for the block dimensions of `lim_{t→0} λ(t)·V`, the
> associated graded, which are read off the profile by
> `β_{σ(j)} = c(F_{≥j}) − c(F_{>j})`. Then
>
> **`reach(H; x, y) ≥ blockdeg := max over pairs (σ, τ) of realizable
> orderings of `Σ_b min(β^σ_b(V₁) + β^τ_b(V₂), cap_b)`, `cap = (2,1,1,2)`.**
>
> *Proof.* `dim(V + W)` is **lower** semicontinuous on `Gr × Gr`, so for
> generic small `(t, s)`,
> `dim(lim λ(t)V₁ + lim μ(s)V₂) ≤ dim(λ(t)V₁ + μ(s)V₂)`, and the right-hand
> pair is achievable at `ϕ` by (BE-94)(ii) (the two sides move independently),
> hence `≤ reach`. Both limits are **adapted** to the four blocks, so the sum's
> dimension is `Σ_b dim(A_b + B_b)` with `A_b, B_b ⊆ block_b`. In the two
> 1-dimensional blocks that is `min(β+β', 1)`. In `Π_x` (and `Π_y`), if both
> graded pieces are lines they may coincide — but the `GL₂` factor
> **commutes** with the central torus, preserves every profile and every block
> dimension, and acts transitively on the lines of `Π_x` and of `Π_y`; a
> generic `A ∈ GL₂` therefore separates both pairs at once (two proper closed
> conditions), giving `min(β+β', 2)`. ∎
>
> **Realizable orderings: 8 of 24**, because the weights obey
> `w_M = w_x + w_y − 2 w_L`, so `⟨M⟩` and `⟨L⟩` cannot be separated freely from
> `Π_x, Π_y`. The bound quantifies over exactly those 8 per side (64 pairs);
> a finer 1-PS with `a₁ ≠ a₂` splits `Π_x` and `Π_y` and would only strengthen
> it. **Enumerated in the driver, not assumed.**

> **(BE-96)(ii)** *(**the law**: measured where the two bounds meet, and there
> `reach` is pinned by two proofs)* By (i) and (BE-95)(i),
> `blockdeg ≤ reach ≤ blockcap`, both computed from `(ρ₁, ρ₂, c₁, c₂)` alone.
> Wherever **`blockdeg = blockcap`**,
>
> **`reach(H; x, y) = blockcap(c₁, c₂, ρ₁, ρ₂)` — a THEOREM at that peel,**
>
> and (BE-67)(iii) there is the arithmetic question *is that number
> `min(δ₁+δ₂, 6)`?*
>
> Measured (`bunif.py law`), with `blockdeg ≤ measured ≤ blockcap` **asserted**
> at every row (the left inequality is also a genericity check on the draw, in
> the (BE-69)(iii) sense):
>
> | population | rows | `cap = deg` | binding `U` **proper** | shortfall |
> |---|---|---|---|---|
> | **A** — BDECOR's 7 R-node pieces + BPEEL's nested piece, 3 draws | **32** | **32** | 24 | **0** |
> | **B** — subdivided 3-connected skeletons (`bpeel.constructed_tier`) | **90** | **89** | **90** | **0** |
>
> A **proper** binding `U` means the cap is doing work no dimension count does
> — the row is *not* in general position and `reach` is still exactly what the
> two per-side profiles say. The one exception is disclosed:
> `K4(2,3,3,3,3,3)` at peel `(A,B)` has `deg 4 < measured 5 = cap`, i.e. the
> **degeneration bound is not sharp there** and the row is settled by the
> measurement, not by the law.

> **(BE-96)(iii)** `[ASSERTED]` *(the abstract half — **the cap is ATTAINED**, 400/400)*
> The peel population can only report the pairs pieces happen to realize, so
> the law's own question is asked off the graphs (`bunif.py abst`): for random
> `V₁, V₂ ⊆ Λ²K⁴` in the standard flag frame — generic, block-adapted, or
> confined to a stable subspace, dimensions `1…5` —
>
> **`max_{g ∈ S(ϕ)} dim(V₁ + Λ²g·V₂) = blockcap` at 400 / 400,**
>
> with `blockdeg = blockcap` at **393 / 400** and `blockdeg ≤ best ≤ blockcap`
> asserted throughout; the profile of `Λ²g·V₂` is **asserted equal** to that of
> `V₂` at every group draw, which is (BE-94)(iii) in use.
>
> **F27, stated exactly.** *"Attained"* is a **witness** (400 of them, one
> group element each); the group sweep is 60 draws per pair, so a *failure* to
> attain would read *none found under the cap*, never *not attained*. The
> **proved** half is the bracket.

> **(BE-96)(iv)** *(**THE REDUCTION** — HIT shape 2, stated so it can be
> attacked)* Combining (i)–(iii) with (BE-69)(iii): at a generic-regime flag
> pair, and with `c_i(U)` the **generic** (= minimal, by upper semicontinuity)
> value of `dim(ρ̄_i ∩ U)` over side `i`'s own family,
>
> **(BE-67)(iii) holds at `H` at this peel ⟺ for every one of the 14
> non-trivial `S(ϕ)`-stable `U`,
> `c₁(U) + c₂(U) ≤ dim U + max(0, δ₁ + δ₂ − 6)`.**
>
> **⟹ is a THEOREM** ((BE-95)(i)): a violation *is* a shortfall, not evidence
> of one. **⟸ is the law** ((BE-96)(i)/(ii)), a theorem wherever the two
> bounds meet and a measurement otherwise. Both sides of the criterion are
> **per-side**: `c_i(U)` is computed from side `i` and the flag pair alone.
> That is exactly the shape (BE-22)(vi) asked its successor for — *"a statement
> about ONE piece and its welding, not about two pieces in relative
> position"* — with the welding half folded in as the `U = Λ²K⁴` term
> (`ρ_i = δ_i` is (BE-22)(iii)(a)).
>
> **What it does NOT do.** It does not prove the 14 inequalities, at any piece
> or on any class. It replaces one unbounded question (*is the mechanism list
> complete?*) by a **bounded** one (*can two sides of one peel be
> simultaneously non-generic at one block, by enough?*) — the same conversion
> (BE-70)(iii) performed one level up, now with the mechanisms indexed rather
> than enumerated.

### Step BE96 — (BE-97): which block can bite, and the one place it is tight

> **(BE-97)(i)** *(**the arithmetic does NOT triage the list**, and a landed
> reading is corrected)* Enumerating every `(δ₁, δ₂, c₁, c₂)` the block caps
> and `ρ_i ≤ δ_i` allow, **14 of the 16 stable `U` can host a violation**;
> only `U = 0` and `U = Λ²K⁴` die. In particular the tempting clause
> *"`Π_x` can never bite"* is **FALSE as an arithmetic statement** — it needs
> *"`c_i(Π_x) = 2` forces `ρ_i = 6`"*, which is (BE-38)(iii)'s **measured**
> third clause over 37 pieces, not a theorem. *(**And that clause is FALSE**,
> refuted 2026-09-02 by (BE-104); the surviving form is
> **(PENCIL-SATURATES-GEN)**, at a **generic flag**. The conclusion of this item
> — the arithmetic does not triage — is unchanged and strengthened again.)* **This direction nearly wrote it
> down as one and the enumeration refused it** (F11). What (BE-44)(ii) *does*
> prove is a per-side **structural price**: `c_i(Π_x) = 2` forces **every**
> `x–y` path of side `i` to span 6, hence `dist_i(x, y) ≥ 6`.
>
> > **Two corrections, 2026-09-02, direction BDOUBLE.** (1) **The
> > denominator.** The enumeration bounds `c_i ≤ min(dim U, δ_i)`; the true cap
> > is `c_i ≤ ρ_i = δ_i + a_i`, so *"14 of 16 live"* is an **`a₁ = a₂ = 0`
> > statement**. Off it **15 of 16** are live — only `U = ∅` still dies, and
> > `U = Λ²K⁴` **joins** the list. The conclusion (*the arithmetic does not
> > triage*) is unchanged and strengthened ((BE-101)(iii)). (2) **The price is
> > weaker than it reads.** `dist_i ≥ 6` gives **no** lower bound on `ρ_i` or
> > `δ_i`: (BE-30) bounds `ρ` by `dist` from **above**, and two measured sides
> > sit at `dist = 6` with `ρ = δ = 1` ((BE-102)(i)). Moreover the step
> > *`c_i(Π_x) = 2 ⟹ every path spans 6`* is the contrapositive of
> > (BE-44)(ii)'s **converse**, which is the **per-shape** half (BE-46)
> > discharges, not the proved `= 6` half ((BE-102)(iii)).

> **(BE-97)(ii)** *(measured; **the violation margin is `0`, never positive**)*
> Define `margin := max over the 16 stable U of
> `c₁(U) + c₂(U) − dim U − max(0, δ₁+δ₂−6)`; by (BE-95)(i) `margin > 0` is
> **exactly** a shortfall. Over **92** rows of populations A and B
> (`bunif.py bind`), the histogram is **`{0 : 92}`** — `margin ≤ 0`
> **asserted** at every row, so **0 shortfalls**, and never `< 0` either: the
> class statement is **saturated at every measured peel**.

> **(BE-97)(iii)** *(**the one place it is tight**, and it is (BE-45) read at
> both ends)* Which `U` is responsible:
>
> | statistic | result |
> |---|---|
> | `U` at which **BOTH** sides exceed the generic profile | **`Π_x` only** — 12 of 92; every other `U`: **0** |
> | rows where `margin = 0` at a **proper nonempty** `U` | `Π_x` **8**; `Π_x⊕Π_y` **2**; `Σ_x⊕Π_y` **2**; `Λ²π_x⊕Π_y` **2** |
> | largest per-side `c_i(Π_x)` / `c_i(Π_y)` seen | **2** / **2** (the block cap) |
>
> So the entire two-sided interaction the class statement has to survive lives
> at **one 2-dimensional block**, where both sides carry `c_i = 1` — which is
> precisely (BE-45)'s dichotomy, **(M1)** a series end at `x` or **(M2)** path
> saturation `δ_i = d_min`, firing on **both** sides of one peel. There
> `c₁ + c₂ = 2 = dim Π_x` and the margin is **exactly `0`**: one more unit on
> either side is a shortfall.
>
> **THE NAMED SUCCESSOR CONDITION, and it is strictly smaller than
> (BE-67)(iii):**
>
> > **(NO-DOUBLE-PENCIL).** At no internal R-node peel does one side have
> > `dim(ρ̄_i ∩ Π_x) = 2` while the other has `dim(ρ̄_j ∩ Π_x) ≥ 1` — and the
> > same at `Π_y`.
>
> Its two clauses are already priced by landed results: the first by
> (BE-44)(ii) (*every `x–y` path of side `i` spans 6*), the second by (BE-45)
> (*series end, or path-saturated*). **Neither clause has been shown
> incompatible with the other**, and that — not a search over configurations —
> is what half (B) now needs.
>
> > **REFUTED 2026-09-02 by (BE-99), direction BDOUBLE — read *Steps
> > BE98–BE102* with this clause.** The two clauses are not incompatible: **one
> > landed lemma produces both.** (BE-45)(ii)'s own **vacuous corner**
> > `d_min = 6` gives `ρ̄_i = ⟨P⟩ = Λ²K⁴`, hence `c_i(Π_x) = c_i(Π_y) = 2`, and
> > (BE-45)(i)/(ii) at the other side gives `c_j(Π_x) ≥ 1` — realized at **2 of
> > the 92 rows measured here**, `K4 + th(6,6,6)/ab + ear4/ua` at peel `(a,b)`,
> > `c = (1,2)` at both 2-blocks. **The measurements in this step are
> > untouched**: the census counts blocks where both sides *exceed the generic
> > profile*, and a side at `ρ_i = 6` sits at `c_i = 2` **generically**, so the
> > pair `(1,2)` is invisible to that statistic ((BE-99)(iv)). What is wrong is
> > only the named condition, and it was **strictly stronger than the `Π_x`
> > inequality it stood in for** — the exhibited pencil has `δ₁+δ₂ = 8` and
> > margin `−1` ((BE-100)). The residue is now the **per-side**
> > **(PENCIL-SATURATES)** (= (BE-38)(iii)'s third clause), under which `Π_x`
> > and `Π_y` are **implied by the `U = Λ²K⁴` inequality** and drop out of the
> > fourteen ((BE-101)).

> **(BE-97)(iv)** *(the honest scope of (iii))* *"`Π_x` only"* is a statement
> about 92 rows of two constructed populations, **not** a theorem. The other 13
> live blocks are unwitnessed rather than excluded; a population reaching
> `c_i(⟨M⟩) = 1` on both sides — *both* sides' relative screw spaces containing
> the virtual edge's own line `p_x ∨ p_y` — would put a second block in play
> at once, and nothing here rules it out.

### Step BE97 — (BE-98): the regime boundary, jobs 2 and 3, and the board

> **(BE-98)(i)** *(**the coincident regime**, where the law is NOT stated)* At
> `π_x = π_y = π` the four-block sum **degenerates**: `⟨L⟩` is no longer a line
> of the screw space, and — **asserted** at 12/12 constructed flag draws
> (`bunif.py coin`) —
>
> **`Π_x + Π_y = Λ²π` (dimension 3) and `Π_x ∩ Π_y = ⟨M⟩`.**
>
> The four blocks then span 3, not 6; `S(ϕ)` is 8-dimensional and its stable
> subspaces form a filtration rather than a direct sum. So **(BE-96) is stated
> for the generic regime only**. The **cap survives**, because it is the
> modular law and needs no decomposition: checked against the named list
> `{Π_x, Π_y, ⟨M⟩, Λ²π}` at **60/60** ear pairs, **0 failures**, of which
> **24** lose dimension outright — (BE-71)(i)'s **two-sided (Z) at
> `dim Z = 3`, EXHIBITED**, on (BE-30)(iii)(b)'s own confinement.
> **CAP DISCLOSED:** the coincidence here is **constructed**
> (`bimage.sample_flags(…, 'equal')`), not **forced** — BGENUINE (BE-85)(i)
> records that the branch sampler cannot draw a forced witness's chart at all.
> The forced family is BGENUINE's **392/392 with shortfall 0** ((BE-86)(ii)),
> **cited here and not re-run**; this step adds only that the obstruction half
> of the law is not violated where the arc's own located enemy lives.

> **(BE-98)(ii)** *(**job 2** — the standing inventory verdict, run per-arc on
> this section's own citations)* The verdict — *the arc inventories landed
> **conclusions** and mis-reads landed **hypotheses*** — **fires here, on a
> citation this direction itself was about to consume**. §(K-bare-ext) cites
> (BE-38)(iii)'s third clause, *"never `2` below `ρ₁ = 6`"*, by the role it
> played when first needed (a summary of a table), and (BE-45)(iii) records it
> as **standing**; its landed signature is a **measurement over 37 pieces**.
> Reading it as a law is what produced this direction's first draft of
> (BE-97)(i) (*"`Π_x` can never bite"*), and the arithmetic enumeration
> **refused** it. **Stress-tested rather than merely flagged**: over 112 rows,
> **4** sides reach `c_i(Π) = 2`, and **0** of them have `ρ_i < 6` — so the
> clause **survives under this cap**, and is now a measurement with a second,
> independent population behind it, still not a theorem. The same read applied
> to this section's other borrowings finds them cited by signature:
> (BE-69)(iii)'s `A_i ≠ ∅` is explicitly *the 2-cut induction's own
> hypothesis*, (BE-70)(ii) is carried **with its `G`**, and (BE-65)(ii)'s
> `Chart(H)` irreducibility is cited with (CH-1)'s three hypotheses named.

> **(BE-98)(iii)** *(**job 3** — what (BE-14) is left with, precisely)* **If**
> `reach` uniformity lands — it has **not**; it is *reduced*, (BE-96)(iv) —
> half (B) is discharged and (BE-14)'s open half is exactly:
>
> 1. **The ear case's (β) side, at the window — UNCONDITIONAL since
>    2026-09-03**: §(K-bare-ext) *Steps BE141–BE147* (direction BSCOND)
>    **decided both** of (BE-57)(iv)'s conditions — **(S1)** *some
>    `δ₁`-attaining middle has `p_{w₁} ≠ p_{w₂}`* is **REMOVABLE** from the
>    statement ((BE-148)(i)) and **(S2)** *no middle forces an algebraic
>    relation between its boundary flags other than equality of the boundary
>    planes* is **half a theorem, half REFUTED-then-CLOSED** ((BE-145)–
>    (BE-147)): the relation exists and is `p_{w₁} = p_{w₂}` itself. **Their
>    landed reading — vacuous at every drawn piece, neither a theorem — is
>    superseded.** (The token *"window conditions"* has three
>    owners in the corpus — these; §(SAFE-RES′)'s (S1)–(S5) in
>    `notes/pencil/workbook/W4.md`, which disambiguates itself inline; and the
>    §(K-slide) (W1)–(W4) family — so it is qualified here.) Outside the
>    window, (β)'s discharge is **per-shape** ((BE-45)(iv), (BE-58)).
> 2. **Cross-pair welding** ((BE-28)(i)), untouched.
>
> Everything else in the (BE-14) decomposition is closed: the base
> ((BE-20)/(BE-23)), 1-cut composition ((BE-18)), the `def₃` law
> ((BE-21)/(BE-73)(ii)), the rigid-side collapse ((BE-22)(vi)), the flag base
> ((BE-89)–(BE-93)).

> **(BE-98)(iv)** *(the board, reported and not acted on)* **What moved.**
> (BE-71)(ii)'s *"that they are the only ones is NOT proved and is not
> claimed"* is **answered in the generic flag regime**: the mechanisms are the
> `S(ϕ)`-stable subspaces, 16 of them, and both located ones are instances.
> (BE-67)(iii)'s two failure modes are **merged into one inequality family**,
> the welded half becoming the `U = Λ²K⁴` term. Half (B)'s residue is
> **unchanged in count** — still the one item — but its **content** is now
> (NO-DOUBLE-PENCIL), a two-clause condition on `ρ̄_i ∩ Π_x`, both clauses
> already priced by landed results. **What did not move.** No class statement
> is proved; no shortfall is exhibited; `hbareSplit` is untouched; the
> coincident regime keeps only the cap.

### Verdict, classification, and the price

- **HIT shape 2** — *reduced to a named checkable condition strictly smaller
  than (BE-67)(iii)*: the 14 inequalities of (BE-96)(iv), and — after the
  measurement — the single condition **(NO-DOUBLE-PENCIL)** of (BE-97)(iii).
- **NOT HIT shape 1** — `reach` uniformity is **not** proved class-uniformly.
  The reduction is per-peel; nothing here quantifies over pieces.
- **NOT HIT shape 3** — **no shortfall**: margin `0` at 92/92, shortfall `0`
  at 122/122. So the third-mechanism question of (BE-71) gains an *index set*,
  not a witness.
- **HIT shape 4** — job 2's verdict fires, on this section's own citation, and
  is stress-tested rather than only flagged ((BE-98)(ii)).
- **HIT shape 5** — job 3 answered precisely, with the three-owner token
  qualified ((BE-98)(iii)).
- **The coordinator's reading (1) is REFUTED AS STATED.** *"The class
  statement is now entirely the general-position half"* is wrong as a
  decomposition: (BE-96)(iv) shows the welded half is **not a separate half at
  all** — it is the `U = Λ²K⁴` term of the same inequality family, and
  dropping it changes the criterion. The reading's *evidence* (the welded half
  free at 30/30 theta children and 392/392) is untouched; what fails is the
  two-halves framing it inherits from (BE-67)(iii).
- **The coordinator's reading (2) is CONFIRMED IN SHAPE and CORRECTED IN ITS
  EXPECTED FAILURE POINT.** (BE-70) does make `reach` a function of the flag
  pair, and that *is* the shape of a class argument — but the operative
  structure is not the *base* the flags live in (BBASE's object): it is the
  flag pair's **stabilizer**. And the proviso `G` is **not** inherited as a
  hypothesis: it is carried exactly as (BE-64)(ii)/(BE-70)(ii) carry it, and
  the statement quantifies over **internal R-node pieces**, not over
  (CH-1)'s class — the class only enters through (BE-65)(ii)'s irreducibility,
  which (BE-69) already needed.
- **The price, stated as a price.** (a) The lower bound uses only the **8**
  realizable central-torus orderings; at one measured row it is not sharp, and
  a finer 1-PS would be needed. (b) *"The cap is attained"* is a **witness
  count** (400/400 group draws, 60 tries each), never a proof of attainment in
  general. (c) The law is **generic-regime only**; the coincident regime keeps
  the cap and loses the attainment half. (d) `c_i(U)` is read off **one
  exact-ℚ draw per side**, generic by (BE-69)(i)'s semicontinuity, and the
  `blockdeg ≤ measured` assert is the only check that the draw was generic.
  (e) Populations A and B are **constructed**, not censuses — see *Caps*.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py equiv      # 41.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py law        # 48.4 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py bind       # 30.4 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py coin       #  0.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py abst       # 103.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bunif.py validate   # 66 s (reduced tiers, all five)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single seed
is `20260902`, printed by every mode. Every headline is an `assert`, not a
report: the four-block direct sum, the flag fixity and `Λ²g`-equivariance, the
one-sided regluing through both gates, `blockdeg ≤ measured ≤ blockcap`,
`margin ≤ 0`, the profile's `S(ϕ)`-invariance, and the coincident-regime
identities.

### Caps, disclosed rather than smoothed — with the denominator named

1. **Population A is BDECOR's constructed R-node battery** — 7 pieces plus
   BPEEL's nested two-level piece, at 3 draws each, giving **32** peel rows.
   It is the **same** population behind (BE-67)(i)'s 28/28 and (BE-69)(iii)'s
   16/16, so those figures and these are **not independent evidence**.
2. **Population B is `bpeel.constructed_tier(maxlen=3, nsamp=60)`**, filtered
   to peels its own R-node stand-in accepts with both `δ_i > 0`, first **90**
   that draw. `constructed_tier` is *K4 exhaustive at branch lengths `1..3`
   plus 60 seeded prism/K33 profiles* — a **construction, not a census**, and
   `rnode_shaped` is disclosed by BPEEL as a **stand-in** for *"`xy` is a
   virtual edge of a simple 3-connected SPQR skeleton"*, not an SPQR
   implementation.
3. **Neither population exhausts "every internal R-node piece".** The target
   is a `∀` over an infinite class; **A** has `|V| ≤ 28` and **B** branch
   lengths `≤ 3` on three skeletons. Every *"0 shortfalls"* here reads **none
   found under these caps**.
4. **`bind`'s 92 rows and `law`'s 122 rows are different sweeps** of the same
   two populations (tier budget 60 vs 90); they are not one figure quoted
   twice, and neither subsumes the other.
5. **`abst`'s 400 pairs are random subspaces, not achievable ones.** They test
   the *group-theoretic* half of the law and say nothing about which profiles a
   piece can realize. The 60-draw group sweep is the cap on *"attained"*.
6. **`coin`'s coincidence is CONSTRUCTED**, 12 flag draws × 5 ear-length pairs
   = 60 pairs. It does **not** reach a forced coincidence; that is BGENUINE's
   392, cited.
7. **`c_i(U) = 2` is rare in these populations** — 4 sides of 112 rows — so
   (BE-98)(ii)'s stress test of (BE-38)(iii)'s third clause has a **small
   denominator**, and its `0` is a none-found at that scale.

### Harness note — the `kbare/` sibling-import set gains its TWENTIETH consumer

`bunif.py` imports `bdecor` / `bpeel` / `bimage` / `binduc` / `bwin` /
`kbare_common` (and `exactcore`) **read-only** and reimplements nothing: `ρ̄`
from `bimage.rho_bar_of`, the pencil and `Λ²` spans from
`bimage.pencil_space` / `lam2`, the flag regimes from `bimage.sample_flags`,
the sampler and the deficiency oracle from `bdecor.sample_by_branches` /
`d3` / `weld_d3`, the peel split from `bpeel.peel_sides` /
`binduc.split_at_pair`, and the R-node tier from `bpeel.constructed_tier`. The
chain is **eighteen** deep (`… → boneone → bgenuine → bbase → bunif`).
The only genuinely new primitives are the four-block frame, `Λ²g`, and the two
bounds. **No move made**, per the standing rule; the *interface decision*
recorded at (BE-83)(iii) remains a coordinator/user call.

### Confidence verdicts, per claim

| claim | verdict |
|---|---|
| (BE-94)(i) `S(ϕ) = diag(λ, A, μ)`, dimension 5 | **proven** (elementary; recovers (BE-22)(v)(β)'s count) |
| (BE-94)(ii) each side's family is `S(ϕ)`-invariant, sides move independently | **proven** from (BE-70)(ii); asserted 30/30 incl. the one-sided regluing |
| (BE-94)(iii) the four blocks; the 16 stable subspaces | **proven** (distinct characters); direct sum asserted 152/152 |
| (BE-95)(i) the block cap | **proven** (modular law) |
| (BE-95)(ii) (BE-71)'s (P) and (Z) are cap instances | **proven** (`core_i` is `S(ϕ)`-stable) |
| (BE-96)(i) the degeneration lower bound | **proven**, over the **8** realizable orderings only |
| (BE-96)(ii) `reach = blockcap` where the bounds meet | **proven at those rows**; 121/122 measured |
| (BE-96)(iii) the cap is attained | **measured**, 400/400 witnesses, 60-draw sweep |
| (BE-96)(iv) the reduction (⟹ theorem, ⟸ the law) | **proven-informally**, with (ii)'s scope |
| (BE-97)(i) the arithmetic triage leaves 14 live | **proven** (exhaustive enumeration) |
| (BE-97)(ii) margin `0`, no shortfall | **measured**, 92/92 asserted, cap-bounded |
| (BE-97)(iii) `Π_x` the only doubly-non-generic block; (NO-DOUBLE-PENCIL) | **measured** (12/92, tight at 8); the condition itself is a **statement**, not a theorem |
| (BE-98)(i) the coincident degeneration; the cap survives | **proven** (identities asserted 12/12); (Z) exhibited 24/60 |
| (BE-98)(ii) job 2's verdict fires; the clause survives the stress test | **verdict** + **measurement** (0 of 4, small denominator) |
| (BE-98)(iii) what (BE-14) is left with | **verdict**, with the three-owner token qualified |
| reading (1) refuted as stated; reading (2) confirmed-in-shape | **verdicts** |

### What would change this

- **A peel with `c_i(Π_x) = 2` on one side and `c_j(Π_x) ≥ 1` on the other.**
  That is a **shortfall by (BE-95)(i)**, hence a refutation of (BE-67)(iii) at
  that piece and a third mechanism in (BE-71)'s sense. The first place to look
  is a side all of whose `x–y` paths have length `≥ 6` ((BE-44)(ii)) glued to a
  **series end** ((BE-45)(i)) — the two clauses are individually cheap and have
  never been sought together.
- **A peel with `⟨M⟩ ⊆ ρ̄₁ ∩ ρ̄₂`.** Both sides' relative screw spaces
  containing the virtual edge's own line is a violation at `U = ⟨M⟩` with
  `δ₁+δ₂ ≤ 6`. Unwitnessed here; `xy ∉ E(H)` at an R-node peel removes the
  obvious source.
- **A row where `blockdeg < measured < blockcap`.** None occurred; it would
  show the *cap* is not attained at a realizable profile pair and would put
  (BE-96)(iii)'s 400/400 in a different light.
- **(BE-38)(iii)'s third clause failing** — a side with `c_i(Π) = 2` and
  `ρ_i < 6`. Then (BE-97)(i)'s price disappears and the `Π_x` block becomes
  much easier to break.
- **The forced-coincidence family meeting a generic-regime peel.** The law is
  generic-regime only; a piece whose chart forces `π_x = π_y` at an R-node peel
  is exactly BONEONE's 392, and there only the cap is available.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/pencil/fanout-archive.md`, with the
2026-09-02 correction (`61e046a6`) in force: **"the target" in E1–E3 is the
ARC's target, `PencilPair K 3 G`**, never a direction's local obligation. The
corpus carries **two** E3 texts; **this reading is `:1700`'s two-conjunct
form**, with `:2098`'s deliberate one-conjunct deviation noted and **not**
used. The wrinkle WGROW recorded and BBASE confirmed holds: **E2's letter says
"the direction's target"** (`:1697`) while **E3's says "the target"**
(`:1700`).

- **E1** — a g-flank, a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: nothing here touches colourings or `D`, and no
  g-flank was exhibited.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on either
  conjunct**: `PencilPair K 3 G` is neither, and this landing **names** a
  dispatchable attack ((NO-DOUBLE-PENCIL), (BE-97)(iii)).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct**: the target is not
  proven, and (NO-DOUBLE-PENCIL) is dispatchable, not gated. Under `:2098`'s
  one-conjunct text it still does not fire, since the first conjunct is the
  one that fails.

**F11**, the central rider here **because the target is itself a uniformity
claim.** Every figure this section owns is a measurement on a **constructed**
piece population, and *"for every internal R-node piece"* exhausts none of
them: **32** rows over BDECOR's 7 pieces + the nested one (population A, the
same pieces behind 28/28 and 16/16 — **not independent**), **90** over
subdivided `K4`/prism/`K33` skeletons with branch lengths `≤ 3` (population B,
an exhaustive `K4` profile sweep plus 60 seeds, i.e. a *construction*),
**92** rows for `bind`, **400** random subspace pairs for `abst` (not
achievable ones), **60** constructed coincident ear pairs for `coin`. A sweep
here reports **"none found under cap C"**, and what a new sweep adds over
BRNODE's 24/24, BDECOR's 28/28 and BPEEL's 16/16 is **population B** — the
first R-node-peel population in this sub-arc that is not the R-battery — plus
the **index set**, which is what makes a future sweep able to report *where*
rather than only *whether*. **The one claim that is not a sweep** is
(BE-96)(iv)'s ⟹ direction, which is the modular law.

**F12** is paid at source: (BE-67)(iii) and (BE-68)(ii) item 2 are annotated
where they stand, and (BE-71)(ii)'s *"not proved and not claimed"* gains its
forward pointer. **F21**: the `(K-bare)` gap-map row is **recomputed to a
target**, with label preservation verified by a scripted set-diff.

**Reservation, and what is returned.** Labels **(BE-94)–(BE-98)** and
***Steps BE93–BE97*** were reserved and are **consumed in full**; nothing is
returned. The driver `w4/bunif.py` landed at the reserved path. One new
configuration-level object is named, in prose per the reservation's own
preference: the **block profile** `c_i(U)` of a side at a flag pair, and the
condition **(NO-DOUBLE-PENCIL)**.
