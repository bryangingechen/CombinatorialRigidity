## §(K-bare-ext) — continuation (direction BEFOURP): **(BE-E4′) ADMITS A ROUTE, AND IT IS NOT A `δ₂` LADDER.** The arithmetic decomposes **exactly** into two per-side pieces on a five-member frontier `f + g ≥ 6`; the firing side's piece is graded by **(BE-110)(i)'s corank identity** into four rungs — and `α_x` **is** `Σ_x`, so **(BE-201)(i) and (BE-110)(i) are one theorem read on two subspaces**; the frontier member with landed predecessors on *both* halves is **REFUTED** by a landed witness whose side 2 is measured here for the first time; and the clause now survives its **two sharpest tests only by the generic-flag-regime gate** — (BE-110)(iv)'s own gate, arriving at the two-sided clause (*Steps BE203–BE208*)

### Step BE203 — (BE-204): the dispatch's first check, answered at source — and the coverage verdict, which holds for a **different reason**

> **(BE-204)(i)** *(**VERIFIED AT SOURCE**; the tell does NOT fire as stated)*
> The dispatch's named refutation-tell was *"`e_i` turns out to be defined
> through `dist` or the side's topology"*. It does not. (BE-153)(v) defines
>
> > **`e_i = ρ_i − c_i(Π_x)`, with `ρ_i = δ_i + a_i`,**
>
> and `barch.e4`/`barch.all_tuples` implement exactly that — `e_i` is a
> function of the side's own deficiency, its `a`-value and the intersection
> dimension `dim(ρ̄_i ∩ Π_x)`, and **no** arc, distance or side-topology datum
> appears in it. Opened at the definition body, not at the prose that cites
> it.

> **(BE-204)(ii)** *(**PROVED**; the tell fires in a weaker form, and this is
> the real finding)* `dist` does bind, but only as a **ceiling**. Combining
> (BE-189)(ii)'s proved `ρ_i ≤ dist_{side_i}(x, y)` with (BE-E4′)'s conclusion
> at a firing side (`c_i(Π_x) = 2`, so `e_i = ρ_i − 2`):
>
> > **`e₁ + e₂ ≥ 4` ⟹ `ρ₁ + ρ₂ ≥ 6 + c_j(Π_x)` ⟹
> > `dist₁(x, y) + dist₂(x, y) ≥ 6 + c_j(Π_x) ≥ 6`.**
>
> So (BE-E4′) carries a **necessary combinatorial condition** of exactly
> (BE-189)(iii)'s kind — provable or refutable off the graph, no configuration
> — and it is the **two-sided** analogue of it. ∎ The direction the ceiling
> runs is also why it cannot be used to *prove* the clause: it bounds `e_i`
> from **above**, and (BE-153)(v)'s *no landed lemma bounds `e_i` from below*
> is unchanged.

> **(BE-204)(iii)** *(**PROVED by exhaustion**; and the condition is a **SUM**,
> which is why coverage holds)* Over all 6 400 tuples, the **1 835**
> hypothesis-firing both-flexible tuples that satisfy (BE-E4′) have
> `min(ρ₁ + ρ₂) = 6` — asserted — but
>
> > **`min max_i ρ_i = 3`**, witnessed at `(δ, a, ρ, c) = (1,1 | 2,2 | 3,3 |
> > 0,2)`: `e = (3, 1)`, sum exactly 4.
>
> So (BE-189)(iii)'s threshold, which is **`dist_{side_i} ≥ 6` on the firing
> side**, does **not** transfer: (BE-E4′) needs only `dist_i ≥ 3` **on each
> side**. **The structural boundary that exhausted the arc / path-bound family
> ((BE-202)(iii)) therefore does not apply to (BE-E4′)** — its content is not
> confined to the 51, and it is not confined off them either.

> **(BE-204)(iv)** *(**PROVED by exhaustion**; where the conclusion is free)*
> At the **540** firing both-flexible tuples with `ρ_i = 6` at *every* firing
> side, `e_i = 4` exactly — asserted — so (BE-E4′) is **automatic** there.
> That is the whole content of (PENCIL-SATURATES) ⟹ (E4) ((BE-153)(ii)) read
> as a statement about *where the clause has nothing to do*.

> **(BE-204)(v)** *(the correction to the dispatch, stated because the
> reasoning mattered more than the verdict)* The spec's promotion of §8's rank
> 2 was argued as *"nothing in a statement about `δ` and `e` looks
> arc-dependent"*. **The verdict is right and that argument is not**: the
> ceiling does reach `e_i`, and a route that ignored it would have inherited
> (BE-202)(iii)'s boundary. What actually saves the clause is that the
> inherited condition is a **sum over the pair** where (BE-189)(iii)'s is
> **per side** — i.e. the two-sidedness that made (E4) hard to *refute*
> ((BE-153)(iii)) is the same property that makes (BE-E4′) reach strata the
> per-side family cannot. Coverage is a **consequence of the two-sidedness**,
> not of arc-independence.

### Step BE204 — (BE-205): the arithmetic decomposes into exactly TWO per-side pieces, and the frontier has FIVE members

> **(BE-205)(i)** *(**PROVED by exhaustion**; (BE-162)(iii) reproduced and
> classified)* Over the 6 400 tuples, **245** violate (BE-E4′) — reproduced.
> Every one has `min(δ₁, δ₂) ≥ 1`, asserted, and the censuses are:
> `min δ_i` `{1: 170, 2: 68, 3: 7}`; `ρ_i` at the **firing** side
> `{2: 120, 3: 108, 4: 72, 5: 30}`; `e_j` at the **other** side
> `{0: 84, 1: 108, 2: 90, 3: 48}`; `(c₁, c₂)` at `Π_x`
> `{(0,2): 25, (1,2): 55, (2,0): 25, (2,1): 55, (2,2): 85}`; and `e₁ + e₂`
> `{0: 8, 1: 30, 2: 71, 3: 136}`.

> **(BE-205)(ii)** *(**PROVED by exhaustion**; and the obvious route is dead
> before it is tried)* Every violation has `ρ_i ≤ 5` at **every** firing side
> (asserted, the maximum being exactly 5), so
>
> > **a (BE-E4′) violation is a (PENCIL-SATURATES) violation on its firing
> > side**, and (PENCIL-SATURATES) ⟹ (BE-E4′) at **0** escapes.
>
> **But (PENCIL-SATURATES) restricted to the both-flexible zone is already
> REFUTED**: (BE-104)(i)'s witness `(5,3 | 0,0 | 5,3 | 2,0)` has `δ₁, δ₂ ≥ 1`,
> violates it, and **satisfies (BE-E4′)** — all three asserted. So *"prove
> (PENCIL-SATURATES) where both sides are flexible"* is **not** the route, and
> the strict weakening is load-bearing rather than cosmetic.

> **(BE-205)(iii)** *(**PROVED by exhaustion**; the frontier, ENUMERATED not
> guessed)* Write, for the firing side `i` and the other side `j`,
>
> > **`(BE-F_f)`: `c_i(Π_x) = 2 ⟹ ρ_i ≥ f`.  `(BE-G_g)`: `c_i(Π_x) = 2 ⟹ e_j ≥ g`.**
>
> The residual-escape grid over `f ∈ 2..6`, `g ∈ 0..4` is
>
> | `f` \ `g` | 0 | 1 | 2 | 3 | 4 |
> |---|---|---|---|---|---|
> | **2** | 245 | 165 | 78 | 28 | **0** |
> | **3** | 129 | 105 | 30 | **0** | 0 |
> | **4** | 42 | 24 | **0** | 0 | 0 |
> | **5** | 10 | **0** | 0 | 0 | 0 |
> | **6** | **0** | 0 | 0 | 0 | 0 |
>
> so the minimal sufficient pairs are **exactly** `(2,4)`, `(3,3)`, `(4,2)`,
> `(5,1)`, `(6,0)` — the frontier is **`f + g ≥ 6`**, five members, and
> **neither piece suffices alone** (`(BE-F_5)` alone leaves 10, `(BE-G_1)` alone
> leaves 165). ∎ **`(6,0)` is (PENCIL-SATURATES), struck by (ii).**

> **(BE-205)(iv)** *(**the `δ₂`-ladder question, ANSWERED: NO**)* The dispatch
> asked whether (BE-E4′) decomposes by a `δ₂` ladder the way (BE-161)(i)'s did.
> It does not. (BE-161)(i) walked `δ₂` at a **fixed** `δ₁ = 5` and a fixed
> adversarial flag, so its rungs are a *slice*, not a decomposition; the
> violating set is live at `min δ_i` up to **3** ((i)), and `δ` enters the
> arithmetic only through `ρ_i = δ_i + a_i` — the same `a_i` the ladder held at
> 0. **The grading that does decompose it is (BE-206)'s**, and it is a
> dimension count on the firing side's reach, not a deficiency count.
> **BSTEER's `δ₂ = 1` is the SMALLEST rung of the old ladder, not the only
> one**, and what BSTEER actually closed is a piece of `(BE-G_1)`, not a rung.

### Step BE205 — (BE-206): the ladder is the CORANK one — and `α_x` **is** `Σ_x`, so (BE-201)(i) and (BE-110)(i) are ONE theorem

> **(BE-206)(i)** *(**PROVED + ASSERTED**; two names, one space)* BLONGARC's
> **α-space** `α_x := p_x ∧ K⁴` ((BE-196)(ii)) and BPROPER/BSATUR's
> **`Σ_x`** (`bsatur.sigma_at`, *"`Σ_x = p ∧ K⁴`, the 3-dimensional space of
> lines through `p`"*) are the **same subspace**. Built here BLONGARC's way —
> three wedges of `p_x` against independent configuration points — and
> asserted equal to `sigma_at(p_x)` at every row of `peel`, because the next
> item rests on it.

> **(BE-206)(ii)** *(**PROVED**; the two invariants are one)* (BE-110)(i)'s
> corank identity is stated *"for any subspace `ρ̄`"* and its proof only uses
> `ker(ω ↦ ω ∧ p_x) = Σ_x`. Read on the arc span `U` it gives
> `dim(U ∩ α_x) = dim U − dim(U ∧ p_x)`, which **is** (BE-201)(i)'s master
> invariant; read on `ρ̄_i` it gives the grading below. ∎ **So BLONGARC's count
> and BPROPER's corank identity are the same theorem on two different
> subspaces**, and the reason the arc reading has a `|arc|` in it is that `U`
> is the object the *path bound* hands you, while `ρ̄_i` is the object the
> *clause* is about.

> **(BE-206)(iii)** *(**PROVED**; the grading, and it is exact)* Suppose
> `Π_x ⊆ ρ̄_i`. Then `Π_x ⊆ ρ̄_i ∩ Σ_x` (since `Π_x = p_x ∧ π̂_x ⊆ Σ_x`), so
> `2 ≤ dim(ρ̄_i ∩ Σ_x) ≤ 3`, and by (i)/(ii)
>
> > **`e_i = ρ_i − 2 = dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i]`,
> > with `dim(ρ̄_i ∧ p_x) ∈ {0, 1, 2, 3}`.**
>
> ∎ Asserted at 21/21 firing sides of `peel`, together with (BE-110)(i)
> itself. So the firing side's whole contribution to `e₁ + e₂` is **the
> dimension of the side's reach seen from `p_x`**, plus one bit, and
> **`(BE-F_5)` is the top rung** (`dim(ρ̄_i ∧ p_x) = 3`, the generic value).

> **(BE-206)(iv)** *(the geometric reading of the four rungs)* `dim(ρ̄_i ∧ p_x)`
> is the dimension of the span of the side's **projected** hinge lines in the
> quotient plane `P³/p_x`, a space of lines of dimension 3. So
> `dim(ρ̄_i ∧ p_x) ≤ 2` says exactly that **the projected hinge lines are
> CONCURRENT** (a 2-dimensional subspace of the lines of `P²` is a pencil),
> and `≤ 1`/`= 0` are the two degeneracies (BE-110)(ii)'s proof already kills
> at a **path** side by `assert_generic_star`. **The route's open content is
> therefore one statement about one configuration-side, in (BE-110)(i)'s own
> variables.**

> **(BE-206)(v)** *(**why no BLONGARC bar is crossed**, stated because the
> object is adjacent to one)* BLONGARC's bars are: no arc-length-6 attempt, no
> further sharpening of the **arc span**, no further **pointwise** target for
> item 0(a)'s clause, no further **properness sweep** on the (BE-181)
> population. This grading is on **`ρ̄_i`**, not on `U`; it has **no arc-length
> parameter at all** ((BE-204)(i)); its target is **(BE-E4′)**, which
> *replaces* item 0(a)'s clause in (BE-101) rather than being a target for it;
> and nothing here sweeps properness. **Recorded rather than assumed**, since
> the bars were set one landing earlier by the direction whose invariant this
> re-reads.

### Step BE206 — (BE-207): `(BE-F_5)` IS FALSE **in the regime**, by a landed witness — and side 2 is measured there for the first time

> **(BE-207)(i)** *(**MEASURED**; the frontier's `(5,1)` member is dead)*
> (BE-118)(ii)'s construction, re-run verbatim (`bproper.plant_peel`, 7
> composites × 3 seeds, **21** rows), carries at **21/21**: `Σ_x ⊆ ρ̄₁` with
> `dim(ρ̄₁ ∩ Σ_x) = 3`, hence `c₁(Π_x) = 2`; `ρ₁ = 4`; `flag_frame` **non-None**
> (asserted, so **in** the generic flag regime); side 2 `rnode_shaped`. By
> (BE-206)(iii) the grading there is `dim(ρ̄₁ ∧ p_x) = 1` at 21/21 and
> `e₁ = 1 + 1 = 2`, asserted. Hence
>
> > **`(BE-F_5)` is FALSE, in the regime, at a landed witness** — and so is
> > `(BE-F_6)`, which is (BE-205)(ii)'s restatement of the same fact.
>
> **So the one frontier member whose *both* halves had landed predecessors —
> (BE-110)(ii)'s `ρ_i ≥ 5` floor and BSTEER's `e_j ≥ 1` — is struck**, and by
> the *floor* half. (BE-110)(ii) remains a **path** theorem, untouched
> ((BE-118)(ii)'s own reading); what fails is its extrapolation off paths, and
> at `Π_x` rather than at `Σ_x`.

> **(BE-207)(ii)** *(**MEASURED**, and it is new: side 2 at those rows)*
> Neither BPROPER nor any successor measured side 2 there. It is
> **constant**: `ρ₂ = 3`, `c₂(Π_x) = 0`, `e₂ = 3` at **21/21**. Hence
>
> > **`e₁ + e₂ = 5` and (BE-E4′) HOLDS at 21 of 21, with margin `+1`.**
>
> The tightest row: `2 pendants + cycle(8) at distance 4` on `K33` profile 3,
> `ρ = (4, 3)`, `c = (2, 0)`, `δ = (4, 3)`, `a = (1, 0)`.

> **(BE-207)(iii)** *(the reading, and it is the route's shape)* At these rows
> the clause survives **entirely on piece `(G)`**: the firing side supplies
> `e₁ = 2` (two short of the conclusion) and side 2 supplies `e₂ = 3` because
> **`c₂(Π_x) = 0`**. So the live frontier member is
>
> > **`(BE-F_4) ∧ (BE-G_2)`**,
>
> whose halves are: `e_i ≥ 2` on the firing side — i.e. (BE-206)(iii)'s bottom
> **two** rungs excluded, `dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i] ≥ 2` — and `e_j ≥ 2`
> on the other side, which under `c_j(Π_x) = 0` is `ρ_j ≥ 2`. `(BE-F_4)` holds at
> 21/21 here, measured; `(BE-G_2)` holds with one to spare.

### Step BE207 — (BE-208): the two landed pointwise-refutation families are the sharpest test (BE-E4′) has — and it survives them **only** by the flag-regime gate

> **(BE-208)(i)** *(**MEASURED**; and the numbers are bad)* BRANKV's
> **(BE-192)** gated arc-3 family and BLONGARC's **(BE-200)(iv)** gated arc-4
> family both sit at `c₁(Π_x) = 2` with `ρ₁ = 3`, so `e₁ = 1` and (BE-E4′)
> needs `e₂ ≥ 3`. **Side 2 was never measured at either.** Re-running both
> constructions verbatim — `bline.legal_peel` + `binduc.flat_config`, 3 peels
> × 8 draws each, 24 gated chart points each — and measuring **both** sides:
>
> > **`ρ = (3, 3)`, `c(Π_x) = (2, 2)`, `e = (1, 1)`, `e₁ + e₂ = 2`, margin
> > `−2`, at 24/24 and 24/24** — and `(δ₁, δ₂)` `{(1,3), (2,3), (3,3)}` at
> > arc 3 and `{(2,3), (3,3), (4,3)}` at arc 4, so **both sides are flexible
> > at every one of the 48**.
>
> **A SCOPE CHECK RUN BEFORE THE MEASUREMENT, because side 2 needs one that
> side 1 did not:** `bline.legal_peel` calls `bproper.composite` with exactly
> the arguments this measurement re-issues, so side 2's edge set must be the
> peel's other side — asserted, not inferred, by checking that the two edge
> sets **partition** `H` and that `bpeel.delta_pair`'s own split of `H` at
> `(x, y)` **reproduces** them.

> **(BE-208)(ii)** *(**the gate, and it is the whole reason this is not a
> refutation**)* `flag_frame` is **None at 48 of 48** — asserted. The 14
> per-side inequalities (BE-97)/(BE-101) that (E4) and (BE-E4′) exist to thin
> are stated **in the generic flag regime** ((BE-98)), so at these rows the
> object (BE-E4′) is about is **not defined**. Hence
>
> > **the 48 rows are REPORTED, never a refutation** — the same disposition
> > (BE-110)(iv) gave its own `ρ_i = 4` hit, for the same reason, one gate
> > earlier in the thread.
>
> A **second, independent** reason: `a = (3, 12)` at these rows, so
> `ρ_i ≠ δ_i + a_i` — the identity (BE-86) records as needing the welded side
> at generic rank — and the rows are therefore **outside the 6 400-tuple
> space** `barch.all_tuples` enumerates as well.

> **(BE-208)(iii)** *(**the honest status**, and it is the price the route
> pays)* (BE-E4′)'s two sharpest tests are now on the board and **both are at
> or below zero margin**: (BE-207)(ii) at `+1` in the regime, and these 48 at
> `−2` off it. Both are neutralized by **one** hypothesis. So
>
> > **the generic flag regime is now LOAD-BEARING for (BE-E4′)** in a way it
> > was **not** for BSTEER's `δ₂ = 1` closure, whose obstruction was a degree
> > count valid at every configuration ((BE-175)(iii)).
>
> This is a genuine weakening of the clause's standing, recorded as such:
> (BE-177)(ii) called `δ₂ = 1` *closed to attack*; the 48 rows show that the
> **`(2,2)` corner** is not closed to attack by any mechanism, only by the
> regime.

> **(BE-208)(iv)** *(**the dominant violating shape, named**)* `c₁ = c₂ = 2` —
> **both** sides containing `Π_x` — is **85 of the 245** arithmetic violations
> ((BE-205)(i)), the largest class, and **48 of 48** of the measured rows. It
> is (BE-97)'s **(NO-DOUBLE-PENCIL)** `(2, ≥1)` corner reached from a new
> direction; (BE-99)/(BE-100) settled that corner as **slack, not a
> shortfall**, and nothing here disturbs that — at these rows `c₁ + c₂ = 4`
> with `slack = 0`, but the `Π_x` **margin** is a `row_of` quantity and
> `row_of` is undefined off the regime, so **no margin is claimed and item
> 0(b) [MARGIN] stays unexhibited**.

### Step BE208 — (BE-209): the route, the smallest first slice, the method verdict, the board, §8, the E-rider

> **(BE-209)(i)** *(**the route**, three pieces, each with its status)* At an
> internal R-node peel in the generic flag regime with `δ₁, δ₂ ≥ 1`,
> **(BE-E4′) follows from `(BE-F_4) ∧ (BE-G_2)`**, which splits as
>
> 1. **`(BE-F_4)`** — `Π_x ⊆ ρ̄_i ⟹ dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i] ≥ 2`, i.e. the
>    firing side's projected hinge lines are **not concurrent, or `Σ_x` is
>    swallowed too**. **OPEN.** Object: (BE-110)(i)'s projection `q̂`.
>    Measured true at 21/21 in the regime ((BE-207)(i)), false at 48/48 off it
>    ((BE-208)(i)).
> 2. **`(BE-G_2a)`** — `c_j(Π_x) = 0` on the **other** side. **PROVED at
>    `ρ_j = 1`** by BSTEER's degree count at `x` ((BE-175)/(BE-177)); measured
>    `0` at BSTEER's 56 R-node rows ((BE-176)(ii)) and at 21/21 here.
> 3. **`(BE-G_2b)`** — `ρ_j ≥ 2`. (BE-177)(i)'s pendant count already proves
>    `δ₂ ≥ 2` on the habitat it covers (72 constructed peels, census
>    `{2: 36, 3: 36}`, minimum 2), and `ρ_j ≥ δ_j` at generic welded rank.
>
> **Neither piece alone suffices** ((BE-205)(iii)), and the arithmetic is
> exhaustive, so **no third piece is needed and none is available**.

> **(BE-209)(ii)** *(**THE SMALLEST FIRST SLICE**, and it is the one piece
> whose proof is already in the tree)* **Lift (BE-175)(i)/(ii) off its
> `ρ₂ = 1` hypothesis to the statement `c_j(Π_x) = 0`.** (BE-175)(i) already
> concludes *"`dim(ρ̄_i ∩ Π_x) ≥ 1` **always** at a series end at `x`"* — a
> statement about the **containment mechanism**, with no `ρ_j` in it — and
> (BE-175)(ii)/(iii) exclude the series end at `x` on side 2 by `rnode_shaped`
> and by the determined flag. **Neither step mentions `dim ρ̄_j`.** So the
> slice is: restate the conclusion as `c_j(Π_x) = 0`, carry (BE-175)(iii)'s
> own residual cap (*no other mechanism makes `ρ̄_j` meet `Π_x`*), and **add
> the generic-flag-regime hypothesis**, which (BE-208)(iii) shows is now
> needed and which BSTEER's version did not carry.
>
> **The slice's own kill condition, and it is cheap:** (BE-176)(i) already
> measured `c₂(Π_x) = 1` at 9/9 rows of an **S-node** peel, and (BE-208)(i)
> measures `c₂(Π_x) = 2` at 48/48 rows of an **R-node-shaped** side 2 off the
> regime. So the lift is **false without both** the `rnode_shaped` and the
> flag-regime hypotheses — a hunt for a **third** mechanism at an
> R-node-shaped side 2 *inside* the regime either finds one (and `(BE-G_2a)`
> dies, taking the whole frontier with it, since `g = 0` is sufficient only at
> `f = 6`) or does not.

> **(BE-209)(iii)** *(**the method verdict** — the dispatch's question 3)* The
> arc's standing finding at three instances ((BE-172)/(BE-182)/(BE-191)) was
> *compute the Klein form's radical on the span the path bound hands you*.
> **The method has an object here, and (BE-206)(ii) says what it is:** not the
> radical of `Q|_U`, but the **projection `q̂ = (· ∧ p_x)` whose kernel is
> `Σ_x = α_x`** — the same machine, applied to `ρ̄_i` instead of to `U`.
> (BE-203)(iii)'s generalizable lesson (*a subspace argument dies when the
> subspace fills the ambient*) is what selects the object: `dim U` grows with
> `|arc|` and fills `Λ²K⁴`, which is why the arc reading has a ceiling;
> `dim(ρ̄_i ∧ p_x)` is capped at **3** by the ambient `Λ²(K⁴/p_x)` **for every
> side, at every arc length**, so the corresponding reading has **no**
> arc-length ceiling. **And (BE-E4′)'s pair character is not an obstruction:**
> the decomposition (BE-205)(iii) is into two **per-side** statements, so the
> method never has to speak about a pair.

> **(BE-209)(iv)** *(**the board**)* **1.** (BE-E4′) **ADMITS a route**, and it
> is `(BE-F_4) ∧ (BE-G_2)` ((BE-209)(i)) — **not** a `δ₂` ladder ((BE-205)(iv)).
> **2.** Its coverage reaches the 51 **and** the 48 ((BE-204)(iii)); the
> boundary that exhausted the arc family does **not** transfer. **3.** The
> frontier's `(5,1)` member — the only one with landed predecessors on both
> halves — is **REFUTED in the regime** ((BE-207)(i)). **4.** The clause
> survives its two sharpest tests, but the second **only** by the flag-regime
> gate, which is now **load-bearing** ((BE-208)(iii)). **5.** The first slice
> is the BSTEER lift ((BE-209)(ii)); it is a re-statement plus two added
> hypotheses, not new mathematics. **6.** `(BE-F_4)` **is** new mathematics, and
> it is the route's real cost.

> **(BE-209)(v)** *(**the §8 consequence**, recorded in §8 as its rule
> requires)* Rank 2 is **not** spent: it is **decomposed**, with a costed
> first slice and one genuinely open lemma. §8's bar gains three entries.
> *(a)* **No further `δ₂`-ladder attempt on (BE-E4′)** — (BE-161)(i)'s ladder
> is a slice at fixed `δ₁`, not a decomposition ((BE-205)(iv)). *(b)* **No
> attempt at `(BE-F_5)`/`(BE-F_6)` or at (PENCIL-SATURATES) on the both-flexible
> zone** — both refuted at landed witnesses ((BE-205)(ii)/(BE-207)(i)).
> *(c)* **No reading of the 48 gated rows as a refutation** — they are off the
> regime by two independent measurements ((BE-208)(ii)). The **ranking**
> consequence: rank 2 stays first, now with a slice rather than as *open
> mathematics*; and the alternatives after it are unchanged.

> **(BE-209)(vi)** *(**the price**, itemized)* **(a)** Everything measured is
> at `k = 2` and side-degree exactly **2**, on the `K33` skeleton at profile 3
> for the gated families and BPROPER's seven composites for the in-regime
> rows. **(b)** `arith` is **exhaustive and exact** over the 6 400 tuples, but
> the tuple space assumes `ρ_i = δ_i + a_i`, which (BE-207)(ii)'s rows satisfy
> only up to `−1` on side 1 and (BE-208)'s rows violate outright — so the
> frontier is a statement about the **arithmetic**, and each piece still needs
> its geometry. **(c)** `(BE-G_2b)`'s `ρ_j ≥ δ_j` is at **generic welded rank**,
> which (BE-86) records as a measured identity, not a theorem. **(d)** The
> BSTEER lift is **not run here**: (BE-209)(ii) is a costing, and its residual
> cap is (BE-175)(iii)'s own. **(e)** A third containment mechanism at an
> R-node-shaped side 2 inside the regime is **not found under** the cap *"21
> in-regime rows over 7 composites × 3 seeds, plus BSTEER's 56"* — and is
> **not excluded**. **(f)** `(BE-F_4)` is measured true at 21 in-regime rows and
> is **not** proved; **no** claim here upgrades it.

> **(BE-209)(vii)** *(**the E-rider**)* **No E-condition fires.** E1/E2/E3 are
> §(K-grid) objects, untouched — no g-flank, no rank computed, and this
> direction exhibits a decomposition rather than a class-uniform positive.
> **What did NOT move:** `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`,
> (BE-14), **S-mark**, half (β) at and outside the window, cross-pair welding,
> class uniformity, the 12 unwitnessed-not-excluded blocks ((BE-97)(iv),
> `⟨M⟩` empty at 93 rows), item 0(b) **[MARGIN]** (still **unexhibited**,
> (BE-208)(iv)), (BE-101)(iii), the flag base, `Γ`-properness (still FALSE as
> a class-uniform statement, (BE-184)), item 0(a)'s **48 of 99** generic
> closure and its **51** open, (GR-10), (GR-15), (OC-8), (K-res), W4.
> **Side-degree `≥ 3` untouched; the `V^k` graph untouched. No `.lean` opened;
> the 2026-08-05 hold untouched. NOT a PENCIL event**, and the arc's standing
> result is unchanged: **`hK` is not closer**.

### Verification (direction BEFOURP)

| claim | evidence |
|---|---|
| (BE-204)(i) `e_i = ρ_i − c_i(Π_x)`, no `dist`/arc/topology datum | **VERIFIED AT SOURCE** — (BE-153)(v)'s definition and `barch.e4`/`all_tuples` opened, not the prose citing them |
| (BE-204)(ii) `e₁+e₂ ≥ 4 ⟹ dist₁+dist₂ ≥ 6 + c_j` | **PROVED** from (BE-189)(ii) + the definition; the two-sided analogue of (BE-189)(iii) |
| (BE-204)(iii) the condition is a SUM; `min max_i ρ_i = 3` | **PROVED by exhaustion** over 6 400 tuples, asserted, witness printed |
| (BE-204)(iv) `ρ_i = 6` at every firing side ⟹ `e_i = 4` | **PROVED by exhaustion**; 540 tuples, asserted |
| (BE-205)(i) the 245, reproduced and classified | **PROVED by exhaustion**; `min δ_i ≥ 1` asserted at 245/245 |
| (BE-205)(ii) violation ⟹ (PS) violation; (PS) ⟹ (BE-E4′); (BE-104)'s witness | **PROVED by exhaustion** (max firing `ρ_i` = 5; 0 escapes) + the witness's three properties asserted |
| (BE-205)(iii) the frontier is `f + g ≥ 6`, five minimal members | **PROVED by exhaustion**; the 25-cell grid enumerated, `(5,1)` and the two one-sided failures asserted |
| (BE-205)(iv) the `δ₂` ladder is a slice, not a decomposition | **PROVED by exhaustion** ((i)'s `min δ_i` census) + (BE-161)(i) read at its own site |
| (BE-206)(i) `α_x = Σ_x` | **PROVED + ASSERTED** at 21/21 (`dim = 3`, intersection `dim = 3`), built BLONGARC's way |
| (BE-206)(ii) (BE-201)(i) and (BE-110)(i) are one theorem | **PROVED** — (BE-110)(i)'s proof opened; it quantifies over *any* subspace |
| (BE-206)(iii) `e_i = dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i]` | **PROVED**; asserted at 21/21 firing sides together with (BE-110)(i) itself |
| (BE-206)(iv) `dim ≤ 2 ⟺` projected hinge lines concurrent | **PROVED** (2-subspaces of `Λ²` of a 3-space are pencils); the `≤ 1`/`0` cases are (BE-110)(ii)'s own |
| (BE-207)(i) `(BE-F_5)` FALSE in the regime | **MEASURED** at 21/21 (`ρ₁ = 4`, `dim(ρ̄₁ ∩ Σ_x) = 3`, grading 1, `flag_frame` non-None asserted) |
| (BE-207)(ii) side 2 at those rows; (BE-E4′) holds, margin `+1` | **MEASURED**, new: `ρ₂ = 3`, `c₂(Π_x) = 0`, `e₂ = 3` at 21/21 |
| (BE-208)(i) 48 gated rows at `e = (1,1)`, both sides flexible | **MEASURED** at 24/24 + 24/24, with the side-2 **scope check** asserted (partition + `delta_pair` agreement) |
| (BE-208)(ii) `flag_frame` None at 48/48; `ρ_i ≠ δ_i + a_i` | **MEASURED**, asserted; disposition per (BE-110)(iv)'s own precedent |
| (BE-208)(iii)/(iv) the flag regime is load-bearing; `(2,2)` dominant | **stated** from (i)/(ii) + (BE-205)(i); no margin claimed off the regime |
| (BE-209)(i)–(vii) the route, the slice, the method, the board, §8, the price, the E-rider | **stated**, with every cap named in (vi) |

**Reproduce.**

```
python3 notes/scripts/w4/befourp.py arith     # (BE-204)/(BE-205), exhaustive
python3 notes/scripts/w4/befourp.py gated     # (BE-208), side 2 at the 48
python3 notes/scripts/w4/befourp.py peel      # (BE-206)/(BE-207), side 2 at the 21
python3 notes/scripts/w4/befourp.py validate  # all three
```

**WHICH CONJUNCTS ARE TESTED.** (BE-E4′) is *`δ₁ ≥ 1` **and** `δ₂ ≥ 1` **and**
`c_i(Π_x) = 2` for some `i`* ⟹ *`e₁ + e₂ ≥ 4`*. Every mode reads **all four**
separately and never one: `arith` splits the hypothesis into `firing(t)` and
`flexible(t)` and reports the two censuses apart; `gated` and `peel` report
`(δ₁, δ₂)`, `c₁(Π_x)`, `c₂(Π_x)`, `ρ₁`, `ρ₂` and `e₁ + e₂` as separate
censuses and classify each firing row as **HOLDS / FAILS / VACUOUS (a rigid
side)** rather than collapsing the last into either of the first two. `(BE-F_f)`
and `(BE-G_g)` are likewise evaluated per **firing side**, so the `c₁ = c₂ = 2`
corner — 85 of the 245 — is tested on **both** sides and not once.

**THE SAMPLER'S SUPPORT, AND WHICH GENERATOR PARAMETERS MOVED.** `arith` does
not sample at all: it enumerates `barch.all_tuples()` in full and the seed is
printed as **unused**. `gated` and `peel` re-issue their predecessors'
constructions **verbatim** and vary **nothing** — `short_library`,
`arc4_library`, `PEELJOBS`, the seed formulas and the draw counts are the
landed ones — because the point is to measure a **new quantity** (side 2) at
the **same** rows, and moving an axis would forfeit the comparison. What is
therefore **not** varied and is inherited as a cap: the skeleton (`K33`,
profile 3) in `gated`, the seven composites in `peel`, the side-degree (2),
the field (`ℚ`) and `k` (2 throughout).

**EVERY CAP, AS "NOT FOUND UNDER CAP C".** *(a)* A containment mechanism
making `c_j(Π_x) ≥ 1` at an R-node-shaped side 2 **inside** the generic flag
regime is **not found under** the cap *"21 in-regime rows over 7 composites ×
3 seeds, plus BSTEER's 56 R-node rows"* — and is **not excluded**; it is
`(BE-G_2a)`'s residual and (BE-209)(ii)'s kill condition. *(b)* A `(BE-F_4)`
violation in the regime is **not found under** the same cap and is **not
excluded**. *(c)* A *less degenerate* gated witness — one where `flag_frame`
is non-None — is **not found under** the cap *"3 peels × 8 `flat_config` draws
per family"*, which is (BE-192)(iii)'s unsolved hub-planarity system,
unchanged and **not** attacked here. *(d)* No negative statement in this
landing rests on a *"not found, therefore absent"* reading: `(BE-F_5)`'s failure
and the 48 rows' margins are **exhibited**, and the frontier is **exhaustive**.

**WHAT DID NOT MOVE, restated at the harness level.** No landed figure moved.
`peel` reproduces (BE-118)(ii)'s 21 rows with `ρ₁ = 4`,
`dim(ρ̄₁ ∩ Σ_x) = 3` and `c₁(Π_x) = 2`; `gated` reproduces (BE-192)(i)'s
`ρ_i = 3` / `c_i(Π_x) = 2` at 24/24 and (BE-200)(iv)'s at 24/24; `arith`
reproduces (BE-162)(ii)/(iii)'s 158 and 245 and (BE-153)(ii)'s implication
structure. Every one is an `assert`.

**`validate` FITS** — **58 s** against the 600 s foreground ceiling — so this
landing adds **no** over-ceiling case to `notes/scripts/README.md` §0. Mode
times: `arith` 0.1 s, `gated` 10 s, `peel` 47 s.

**Figure-invariance gate, discharged.** This landing **adds** a harness driver
and modifies **none**: `git diff --name-only -- '*.py' '*.m2'` is **empty**,
`--cached` likewise, and `git status --porcelain notes/scripts/` shows only
the **addition** of `w4/befourp.py`, so *No tracked driver modified*
discharges the gate and §3 is not baselined. `barch.py`, `bfour.py`,
`brankv.py`, `blongarc.py`, `bproper.py`, `bline.py`, `bsatur.py`,
`bpeel.py`, `bimage.py`, `bunif.py`, `binduc.py`, `bsigma.py`,
`exactcore.py` and `kbare_common.py` are **imported, not edited**.
Reproducibility spot-check: `validate` run twice at `PYTHONHASHSEED=0` is
byte-identical modulo each mode's timing line.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bimage.pt_in` is **not called anywhere** in this module, so its silent `K⁴`
truncation is unreachable rather than merely avoided. **No width-12 object is
built**, and every `span`/`dim`/`isect` call takes width-6 (`Λ²K⁴`) rows,
which is what `bimage.span`'s rank-triggered `d == 6` branch is for; the one
`K⁴`-side dimension (the independent-point basis for `α_x`) goes through the
width-agnostic `exactcore.rank`, **never** `span`/`dim`, so the width-6
special case is unreachable with a `K⁴` input. `bwin` is **not imported**, so
`dehom`'s list-vs-tuple guard defeat is unreachable, and **every point this
module reads comes from a predecessor's own configuration builder**
(`binduc.flat_config`, `bproper.plant_peel`) rather than being written here —
so `assert_generic_star`'s tuple comparison cannot be defeated from this side.

**THE HARNESS-DEBT ROW THIS LANDING ADDS TO.** `w4/befourp.py` is the next
`w4/` consumer of the same eleven-deep sibling-import chain
(`befourp → blongarc → barch → bdegtwo → bline → bopen → bproper → bsigma →
bsatur → … → kbare_common`), plus a **first** consumer of `bfour.e_row`/
`e4_at`/`side_nums`, a **second** of `brankv.arc_through`/`short_library` and
of `blongarc.arc4_library`, a **sixth** of `bproper.composite` and a **third**
of `bproper.plant_peel`/`PEELJOBS`/`side_named`, and a **fourth** of
`bsigma.wedge3` (its own **OVERDUE** item). **All folded into the standing
sibling-import item, NO MOVE MADE**, by the rule that a dispatch does not move
a landed name. It opens **no new hazard item**. It does **not** fix
BLONGARC's recorded `brankv.py` docstring defect, for the same reason
BLONGARC did not.

### Step BE209 — (BE-210): the AMBIENT CAP already decides most of `(BE-G_2)`, and it needs no hypothesis at all

> **(BE-210)(i)** *(**PROVED**; one line, and it is the whole reason the slice
> is smaller than it looks)* `c_j(Π_x) = dim(ρ̄_j ∩ Π_x) ≤ dim Π_x = 2`, so
>
> > **`e_j = ρ_j − c_j(Π_x) ≥ ρ_j − 2` at every row.**
>
> ∎ No `rnode_shaped`, no flag regime, no residual cap, no degree count —
> `dim Π_x = 2` is asserted by `bimage.pencil_space` itself. Asserted over all
> **6 400** tuples. Hence **`(BE-G_2)` (`e_j ≥ 2`) is a THEOREM at
> `ρ_j ≥ 4`** — 2 124 firing tuples, asserted — and **FALSE at `ρ_j ≤ 1`** —
> 250, asserted — so `(BE-G_2b)`'s `ρ_j ≥ 2` is **necessary**, not a
> convenience.

> **(BE-210)(ii)** *(**PROVED by exhaustion**; the repair, and it is an
> EQUIVALENCE)* `(BE-G_2)` is therefore *exactly*
>
> > **`ρ_j ≥ 2` ∧ (`ρ_j ≤ 3` ⟹ `c_j(Π_x) ≤ ρ_j − 2`)**,
>
> asserted equal to `e_j ≥ 2` at all **3 375** firing tuples — not merely
> sufficient for it, which is what `(BE-G_2a) ∧ (BE-G_2b)` is. So the clause's
> **entire content is the two rungs `ρ_j ∈ {2, 3}`**: `c_j(Π_x) = 0` at
> `ρ_j = 2`, and `Π_x ⊄ ρ̄_j` at `ρ_j = 3`.

> **(BE-210)(iii)** *(the reading, and it relocates the slice)* **BSTEER's
> habitat is `ρ_j = 1`, which is precisely the rung where `(BE-G_2)` cannot
> hold.** The theorem's habitat and the target's content habitat are
> therefore **DISJOINT**, and the lift is not *"carry a theorem to a larger
> habitat"* but *"prove it on two rungs it never touched"*. What BSTEER
> supplies is `(BE-G_1)`, exactly as (BE-207)(i) recorded when it struck
> `(BE-F_5)`.

### Step BE210 — (BE-211): and `(BE-G_2a)` AS STATED is UNSATISFIABLE at `ρ_j ≥ 5` — the ambient is a THIRD mechanism

> **(BE-211)(i)** *(**PROVED**, then **CONSTRUCTED**)* Grassmann in `Λ²K⁴`
> gives `c_j(Π_x) ≥ ρ_j + 2 − 6 = ρ_j − 4`. Sharper, in two elementary steps
> the construction exhibits: `dim(ρ̄_j ∩ Σ_x) ≥ ρ_j − 3` (against the
> **totally singular** 3-space `Σ_x`, asserted totally singular on its basis
> and every pairwise sum), and `c_j(Π_x) ≥ dim(ρ̄_j ∩ Σ_x) − 1` (`Π_x` has
> **codimension 1** in `Σ_x`). Hence the realizable range is **exactly**
>
> > **`max(0, ρ_j − 4) ≤ c_j(Π_x) ≤ min(2, ρ_j)`**,
>
> asserted rung by rung over **23 CONSTRUCTED shapes** — every subspace of
> `Σ_x` up to `(dim, dim ∩ Π_x)`, extended by complement basis vectors, in
> exact ℚ. **Nothing sampled:** a random 2-space is never isotropic, which is
> how a predecessor's assert went vacuous (`RESEARCH-ARC.md` §4 — BRANKV's
> rank-2 draft and one of BEFOURP's own).

> **(BE-211)(ii)** *(the consequence, and it is the first refutation)*
> `c_j(Π_x) = 0` is **realized 0 times at `ρ_j ≥ 5`** and `c_j(Π_x) = 2` is
> **FORCED at `ρ_j = 6`** — both asserted. So
>
> > **`(BE-G_2a)` is not merely unproved off BSTEER's habitat: it is FALSE
> > there, and by the ambient dimension rather than by a mechanism.**
>
> This **is** a third `c_j(Π_x) ≥ 1` mechanism at an R-node-shaped side 2
> inside the regime — the one (BE-209)(ii)'s kill condition asked for — and
> **no hypothesis can exclude it**, because it is a statement about `Λ²K⁴`.
> **20 of the 245** escapes sit at `ρ_j ≥ 5` on the non-firing side.

> **(BE-211)(iii)** *(and why this alone does **not** kill the frontier)* At
> `ρ_j ≥ 5`, `e_j = ρ_j − c_j(Π_x) ≥ 3`, so `(BE-G_2)` **holds with room** at
> exactly the rungs where `(BE-G_2a)` fails. **(BE-209)(ii)'s kill condition
> is therefore MIS-SPECIFIED**: `c_j(Π_x) ≥ 1` is neither necessary nor
> sufficient for the frontier's death. The operative condition is `e_j ≤ 1`,
> i.e. `c_j(Π_x) ≥ ρ_j − 1`, which with `c_j ≤ 2` **requires `ρ_j ≤ 3`** —
> asserted: no firing tuple with `ρ_j ≥ 4` has `e_j ≤ 1`.

### Step BE211 — (BE-212): (BE-206)'s four-rung grading is a TAUTOLOGY where it is verified and FALSE where it is not

> **(BE-212)(i)** *(**VERIFIED AT SOURCE**, the driver rather than the prose)
> `befourp.run_peel` asserts `e_i = dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i]` **only
> inside `if row['cX'][i] != 2: continue`** — i.e. only where `Π_x ⊆ ρ̄_i` —
> and asserts `dsig ≥ 2` in the same block. There `dim(ρ̄_i ∩ Σ_x) ∈ {2, 3}`
> is forced (`≥ 2` by the containment, `≤ 3` by `dim Σ_x`), so the identity
> reduces to `e_i = ρ_i − 2`, which is `c_i(Π_x) = 2` restated. **On the
> branch where it is checked, the grading has no content beyond the firing
> hypothesis itself.**

> **(BE-212)(ii)** *(**CONSTRUCTED counterexamples**; off that branch the
> identity is false)* The identity predicts `c_i(Π_x) = dim(ρ̄_i ∩ Σ_x) −
> [dim = 3]`, i.e. that `ρ̄_i ∩ Σ_x ⊆ Π_x` whenever that dimension is `≤ 2`.
> Since `Π_x` has codimension 1 in `Σ_x`, the *generic* value is one lower.
> Over the 23 constructed shapes the identity **FAILS at 8**, exactly the
> branch `c = dim(ρ̄ ∩ Σ_x) − 1` with `dim(ρ̄ ∩ Σ_x) ≤ 2` (e.g. `ρ = 3`,
> `dim ∩ Σ_x = 1`, `c = 0`: `e = 3`, grading predicts `2`). **Every failure
> has `c < 2`**, asserted — so the identity is sound precisely on the firing
> branch, and precisely there it is a tautology.

> **(BE-212)(iii)** *(the consequence for the route, and it is a demotion)*
> `(BE-F_4)` is stated in (BE-207)(iii) as `dim(ρ̄_i ∧ p_x) + [Σ_x ⊆ ρ̄_i] ≥ 2`.
> Under its own hypothesis `Π_x ⊆ ρ̄_i` that is `ρ_i − 2 ≥ 2`, so
>
> > **`(BE-F_4)` IS the floor `ρ_i ≥ 4`** — which is what `barch.ps_floor`
> > and `befourp.piece_floor` already implement.
>
> The projection `q̂` is therefore a **change of variables on the firing side,
> not a new handle**, and (BE-209)(iii)'s *"the radical method has an object
> here"* is **weaker than recorded**: the object exists, but the grading it
> induces is the corank identity's rank-nullity (a theorem, re-asserted here
> at 23/23) plus a second clause that is only correct where it is empty. This
> does **not** touch (BE-206)(i) (`α_x = Σ_x`, asserted 21/21 and re-asserted
> here) or (BE-206)(ii).

### Step BE212 — (BE-213): the 6 400-tuple space omits the Grassmann floor — 2 800 unrealizable tuples — and the frontier does NOT move

> **(BE-213)(i)** *(**VERIFIED AT SOURCE**, then **MEASURED**)
> `barch.all_tuples`'s own docstring says it enforces `c_i ≤ min(dim Π_x,
> ρ_i)`, and its body does exactly that — the **upper** cap only. It does
> **not** enforce (BE-211)(i)'s floor `c_i ≥ ρ_i − 4`. Consequence:
>
> > **only 3 600 of the 6 400 tuples are geometrically realizable in `Λ²K⁴`**;
> > 2 800 are not, `(0,0,0,0,6,6,0,0)` among them.
>
> This is a defect in the arithmetic space every `(BE-F_f)`/`(BE-G_g)` figure
> from (BE-153) onward is enumerated over, recorded because the space is
> cited as *exhaustive* and it is exhaustive over a **strict superset**.

> **(BE-213)(ii)** *(**PROVED by exhaustion**; and the defect is INERT)* Every
> one of the **245** escapes is floor-legal — asserted — so no escape is an
> artefact, and the 25-cell `(BE-F_f) × (BE-G_g)` grid is **identical** under
> both spaces, asserted cell by cell, with the same five minimal members
> `(2,4)/(3,3)/(4,2)/(5,1)/(6,0)`. Hence
>
> > **(BE-205)(iii)'s frontier is PROTECTED by this check, not corrected by
> > it** — and BEFOURP's `f + g ≥ 6` stands as the arithmetic statement it was.
>
> Applied as a **filter** over `all_tuples()`; **no tracked driver is edited**.

### Step BE213 — (BE-214): THE KILL — `(BE-G_2)` is REFUTED inside the generic flag regime, and the mechanism is (BE-175)(i) ITSELF

> **(BE-214)(i)** *(**CONSTRUCTED and MEASURED**, every habitat gate asserted)
> `bproper.plant_peel` re-run with **one axis moved** — the skeleton profile
> length, which BEFOURP's `PEELJOBS` and `bline.legal_peel` both hardcode at
> **3** — at profile **4** and **5**, side 1 the bucket-A piece
> `2 pendants + theta(3,3,3)`:
>
> > **`ρ = (2, 6)`, `c(Π_x) = (1, 2)`, `e = (1, 4)`, `δ = (2, 6)`,
> > `a = (0, 0)` at 4 of 4** — `K33 (A,B)`, `prism (A,E)`, `K33 (D,E)` at
> > profile 4 and `K33 (A,B)` at profile 5.
>
> Asserted at every one: `hcard_ok`, min degree `2 ≥ 2`, girth `6 ≥ 4`
> (**(CH-1)** on `H`), `x ≁ y`, `deg_H(x) = deg_H(y) = 4 ≥ 3` (both terminals
> hubs), **side 2 `rnode_shaped`**, the two sides **partition** `H`,
> `verify_pencil_witness`, **`flag_frame` NON-None**, and `δ₁, δ₂ ≥ 1`. This
> is the gate set `bline.legal_peel` imposes, which BEFOURP's own 21 in-regime
> rows do **not** all carry.

> **(BE-214)(ii)** *(**MEASURED**; `(BE-G_2)` is FALSE there)* The firing side
> is **side 2** (`c₂(Π_x) = 2`), so the *other* side is side 1, with
> `ρ₁ = 2`, `c₁(Π_x) = 1`, hence
>
> > **`e_j = 1 < 2`: `(BE-G_2)` FAILS, and `(BE-G_2a)` with it, at 4 of 4
> > fully-gated peels INSIDE the regime** — on two skeletons, three hub pairs
> > and two profile lengths.

> **(BE-214)(iii)** *(**MEASURED**; and the mechanism is the lift's own
> theorem)* At every one, `deg_1(x) = 1` — **a series end at `x` on side 1** —
> and `ℓ = p_x ∧ p_c` is asserted to lie **in `ρ̄₁`** and **in `Π_x`**. That
> is **(BE-175)(i) verbatim**: (BE-45)(i)'s leaf collapse puts `ℓ` in `ρ̄₁`,
> (CH-1)'s coplanar closed star puts `p_c` in `π_x`. So
>
> > **the mechanism that refutes the lift is the mechanism (BE-175)(i)
> > PROVES.**

> **(BE-214)(iv)** *(**the diagnosis**, and it is a side-indexing error, not a
> missing hypothesis)* (BE-175)(ii)'s `rnode_shaped` exclusion and
> (BE-209)(ii)'s flag-regime hypothesis are both indexed to **side 2**.
> `(BE-G_g)`'s subject is the **NON-FIRING** side. The two coincide only when
> the firing side is the *non*-R-node one — which is exactly BEFOURP's 21 rows
> ((BE-207)(ii): firing on side 1, `ρ₁ = 4`, side 2 the skeleton) and is
> **not** the general peel. Here the firing side **is** the skeleton side, and
> `deg₂(x) ≥ 2` says nothing whatever about side 1. Hence
>
> > **the two added hypotheses cannot save the lift, because they constrain
> > the wrong side** — and adding *"side `j` is R-node-shaped too"* is not
> > available: `rnode_shaped(side 1)` is asserted **False** at 4/4, and a peel
> > needs a series end somewhere to be a peel at all.

### Step BE214 — (BE-215): so the five-member frontier is EXHAUSTED, not thinned

> **(BE-215)(i)** *(**PROVED by exhaustion**; every surviving member needs
> `(BE-G_2)`)* Of the five minimal members, `(6,0)` needs `(BE-F_6)` =
> (PENCIL-SATURATES), **REFUTED** ((BE-104)/(BE-205)(ii)), and `(5,1)` needs
> `(BE-F_5)`, **REFUTED in the regime** ((BE-207)(i)). The remaining three —
> `(4,2)`, `(3,3)`, `(2,4)` — each carry `g ≥ 2`, and `(BE-G_g)` for `g ≥ 2`
> is asserted to **imply** `(BE-G_2)`. Hence
>
> > **(BE-214)'s witness retires ALL THREE, and with them the whole frontier:
> > BEFOURP's `f + g ≥ 6` has no surviving member.**
>
> **(BE-209)(ii)'s kill condition FIRED.** Its *consequence* was stated
> correctly; its *trigger* was not ((BE-211)(iii)).

> **(BE-215)(ii)** *(the honest scope, stated before the next reader
> over-reads it)* This kills the **route**, not the clause. `(BE-F_f)` and
> `(BE-G_g)` are **sufficient** conditions for (BE-E4′) on the tuple space, so
> a row where `(BE-G_2)` fails and (BE-E4′) still holds is no contradiction —
> and (BE-E4′) **does** hold at all four witnesses, margin `+1`. What is dead
> is the **decomposition**: no member of BEFOURP's frontier is provable,
> because one conjunct of each is false at a landed, fully-gated, in-regime
> row.

### Step BE215 — (BE-216): the replacement is a SUM, it is hypothesis-free, and it is already proved

> **(BE-216)(i)** *(**PROVED**)* At a firing side `c_i(Π_x) = 2`, so
> `e_i = ρ_i − 2` **exactly** (asserted at every firing tuple). With
> (BE-210)(i)'s cap on the other side, `e₁ + e₂ ≥ ρ₁ + ρ₂ − 4`, hence
>
> > **(BE-E4′) ⟸ `ρ₁ + ρ₂ ≥ 8`**, with **no** hypothesis beyond the firing
> > one — asserted at all **1 575** firing both-flexible tuples that satisfy it.

> **(BE-216)(ii)** *(**PROVED by exhaustion**; the open zone is exact)* The
> 245 escapes' `ρ₁ + ρ₂` census is **`{3: 8, 4: 32, 5: 76, 6: 85, 7: 44}`** —
> **maximum 7**, asserted. So
>
> > **the whole open zone is `ρ₁ + ρ₂ ≤ 7`**,
>
> and the condition is a **SUM over the pair**, which is (BE-204)(iii)'s own
> two-sidedness arriving at `ρ` instead of at `dist`. It is also why the four
> kill witnesses survive: `ρ₁ + ρ₂ = 8` at every one.

> **(BE-216)(iii)** *(**MEASURED**; the census the caps are stated over, and
> (BE-E4′) is NOT refuted)* Over **90** rows in-regime with side 2
> R-node-shaped — 2 skeletons × 5 hub pairs × 3 profile lengths × 6 bucket-A
> side-1 pieces, one seed each — the `(ρ, c, e)` census has nine cells,
> `ρ₁ ∈ {2,3,4}` set by the side-1 piece and `ρ₂ ∈ {0,3,6}` set by the
> profile length. **`(BE-G_2)` fails at 5** firing both-flexible rows;
> **(BE-E4′) fails at 0**, asserted. The reason is (BE-210)(i) again: at
> `ρ_i = 6` the firing side alone supplies `e_i = 4`. **The same elementary
> bound that makes `(BE-G_2)` free at `ρ_j ≥ 4` is what saves the clause
> where `(BE-G_2)` dies.**

### Step BE216 — (BE-217): the verdict, the board, the bars, the price, the E-rider

> **(BE-217)(i)** *(**the verdict on the dispatch's question**)* **The lift
> does NOT go through.** `(BE-G_2a)` is refuted three independent ways —
> unsatisfiable at `ρ_j ≥ 5` by the ambient ((BE-211)(ii)); false at four
> fully-gated in-regime R-node peels ((BE-214)(ii)); and false *by
> (BE-175)(i) itself* applied to the side the target is about
> ((BE-214)(iii)). **It is not a re-statement plus two hypotheses**: the two
> hypotheses are indexed to side 2 and the target is about the non-firing
> side, so neither reaches it ((BE-214)(iv)).

> **(BE-217)(ii)** *(**the board**)* **1.** §8's rank 2 is **not decomposed
> any more**: the frontier is **EXHAUSTED** ((BE-215)(i)). **2.** (BE-E4′)
> itself is **UNREFUTED and still OPEN** — 0 failures at 90 in-regime rows,
> and it holds at every kill witness ((BE-215)(ii)/(BE-216)(iii)). **3.** The
> one **positive** the direction lands is hypothesis-free: `e_j ≥ ρ_j − 2`,
> hence `(BE-E4′) ⟸ ρ₁ + ρ₂ ≥ 8` and an exact open zone `ρ₁ + ρ₂ ≤ 7`
> ((BE-216)). **4.** `(BE-F_4)` **is** the floor `ρ_i ≥ 4` and `q̂` adds
> nothing to it ((BE-212)(iii)), so BEFOURP's *"`(BE-F_4)` is the route's real
> cost"* survives — but as a **`ρ`-floor**, not as a projection question.
> **5.** BEFOURP's arithmetic frontier is **protected** against the tuple
> space's missing floor ((BE-213)(ii)).

> **(BE-217)(iii)** *(**the successor**, one item, costed)* **(BE-E4′) on the
> `ρ₁ + ρ₂ ≤ 7` firing zone**, which (BE-216) makes the *exact* residue.
> Its cheapest live sub-slice is the shape this direction could **not**
> realize: a firing side at `ρ_i ∈ {4, 5}` (so `e_i ∈ {2, 3}`) against a
> non-firing side at `e_j ≤ 6 − ρ_i`. The sweep's nine cells never pair them
> — `ρ₂ ∈ {0, 3, 6}` is quantized by the profile length — so the sub-slice
> needs a **non-uniform** profile or a side-2 family outside
> `bpeel.subdivided`. **If that shape exists in the regime, (BE-E4′) itself is
> refuted**; if it provably does not, (BE-E4′) is a theorem.

> **(BE-217)(iv)** *(**the bars this direction adds**, three)* *(a)* **No
> further attempt at `(BE-G_2)`, `(BE-G_2a)`, or any `(BE-G_g)` with
> `g ≥ 2`** — refuted at a landed in-regime witness. *(b)* **No further
> attempt at any member of the `f + g ≥ 6` frontier**: all five are dead, and
> re-deriving the grid is (BE-213)(ii)'s already-run check. *(c)* **No reading
> of (BE-206)'s grading as a handle on `(BE-F_4)`** — it is rank-nullity plus
> an empty clause ((BE-212)). BLONGARC's four and BEFOURP's three stand
> unchanged; **no bar is crossed** by this direction and none is lifted.

> **(BE-217)(v)** *(**the price**, itemized)* **(a)** Every geometric row is
> at `k = 2`, side-degree `deg_2(x) = 3`, on the two non-adjacent-hub
> skeletons `K33`/`prism`, over ℚ, one seed per cell. **(b)** The kill is
> **CONSTRUCTED and disclosed as such** — `plant_peel` at a profile length the
> predecessors hardcode — not drawn from a habitat census; it is a
> counterexample, which is the one thing a single construction suffices for.
> **(c)** The five sweep rows where `(BE-G_2)` fails are all the same tuple
> `(2,6,0,0,2,6,1,2)` and the same side-1 piece, so *"one shape, five
> embeddings"* is the honest count, not five independent shapes. **(d)** A
> row with a firing side at `ρ_i ∈ {4,5}` against `e_j ≤ 6 − ρ_i` is **not
> found under** the cap *"90 in-regime R-node rows, 5 hub pairs × 3 uniform
> profile lengths × 6 bucket-A pieces"* — and is **not excluded**; it is
> (BE-217)(iii). **(e)** (BE-216)(i)'s bound is proved; (BE-216)(iii)'s
> *"(BE-E4′) holds"* is **measured**, and nothing here upgrades (BE-E4′) to a
> theorem. **(f)** (BE-213)(i)'s defect is recorded, **not repaired**: no
> tracked driver is edited.

> **(BE-217)(vi)** *(**the E-rider**)* **No E-condition fires.** E1/E2/E3 are
> §(K-grid) objects, untouched — no g-flank, no rank computed, and this
> direction exhibits a refutation plus one elementary positive rather than a
> class-uniform result. **What did NOT move:** `PencilPair K 3 G`,
> `hbareSplit`, `hK`, `hcontract`, (BE-14), **S-mark**, half (β) at and
> outside the window, cross-pair welding, class uniformity, the 12
> unwitnessed-not-excluded blocks ((BE-97)(iv)), item 0(b) **[MARGIN]** (still
> unexhibited), (BE-101)(iii), the flag base, `Γ`-properness, item 0(a)'s
> **48 of 99** generic closure and its **51** open, (BE-206)(i)/(ii),
> (BE-175)(i)/(ii)/(iii) **as theorems about side 2** (untouched — what is
> refuted is a *lift* of them to the non-firing side), (GR-10), (GR-15),
> (OC-8), (K-res), W4. **Side-degree `≥ 3` untouched; the `V^k` graph
> untouched. No `.lean` opened; the 2026-08-05 hold untouched. NOT a PENCIL
> event.**

### Verification (direction BGTWOA)

| claim | evidence |
|---|---|
| (BE-210)(i) `c_j(Π_x) ≤ 2`, hence `e_j ≥ ρ_j − 2`; `(BE-G_2)` free at `ρ_j ≥ 4`, false at `ρ_j ≤ 1` | **PROVED** (`dim Π_x = 2`, asserted by `bimage.pencil_space`) + **exhaustive** over 6 400 tuples; 2 124 / 250 asserted |
| (BE-210)(ii) the repair is an EQUIVALENCE to `(BE-G_2)` | **PROVED by exhaustion**; asserted at all 3 375 firing tuples |
| (BE-210)(iii) BSTEER's `ρ_j = 1` habitat is disjoint from `(BE-G_2)`'s content | **PROVED** from (i)'s two endpoints |
| (BE-211)(i) realizable range `max(0, ρ−4) ≤ c ≤ min(2, ρ)`; `Σ_x` totally singular | **CONSTRUCTED** in exact ℚ, 23 shapes, every rung asserted; Klein form asserted `0` on the basis and every pairwise sum |
| (BE-211)(ii) `(BE-G_2a)` unsatisfiable at `ρ_j ≥ 5`; forced `c = 2` at `ρ_j = 6` | **CONSTRUCTED**; `0` realizations asserted, and 20 of the 245 at `ρ_j ≥ 5` |
| (BE-211)(iii) the kill condition is mis-specified; `e_j ≤ 1` needs `ρ_j ≤ 3` | **PROVED by exhaustion**; asserted no firing tuple with `ρ_j ≥ 4` has `e_j ≤ 1` |
| (BE-212)(i) (BE-206)'s grading is asserted only under `c_i = 2`, where it is a tautology | **VERIFIED AT SOURCE** — `befourp.run_peel`'s control flow and its own `dsig ≥ 2` assert opened, not the prose |
| (BE-212)(ii) the grading is FALSE off that branch | **CONSTRUCTED**; 8 of 23 shapes, every failure asserted to have `c < 2` |
| (BE-212)(iii) `(BE-F_4)` IS `ρ_i ≥ 4`; `q̂` adds no leverage | **PROVED** from (i) + (BE-207)(iii)'s own statement |
| (BE-213)(i) `all_tuples` omits `c_i ≥ ρ_i − 4`; 2 800 unrealizable | **VERIFIED AT SOURCE** (docstring **and** body) + **measured** |
| (BE-213)(ii) the frontier is unmoved; 245 floor-legal; grid identical | **PROVED by exhaustion**; grid asserted equal cell by cell, five minimal members asserted |
| (BE-214)(i) four fully-gated in-regime peels, every habitat gate | **CONSTRUCTED and MEASURED**; (CH-1), `x ≁ y`, hub degrees, `rnode_shaped`, partition, witness, `flag_frame` non-None, `δ_i ≥ 1` all asserted 4/4 |
| (BE-214)(ii) `(BE-G_2)` FALSE at 4/4, `e_j = 1` | **MEASURED**, asserted |
| (BE-214)(iii) the mechanism is (BE-175)(i): `ℓ = p_x ∧ p_c ∈ ρ̄₁ ∩ Π_x` | **MEASURED**, both memberships asserted separately at 4/4, with `deg_1(x) = 1` asserted |
| (BE-214)(iv) the hypotheses are indexed to side 2; `rnode_shaped(side 1)` False | **MEASURED** (asserted False 4/4) + **stated** from (BE-175)(ii)'s own text |
| (BE-215)(i) every surviving member implies `(BE-G_2)`; the frontier is exhausted | **PROVED by exhaustion** for the three `g ≥ 2` members; the other two by (BE-207)(i)/(BE-205)(ii) |
| (BE-215)(ii) this kills the route, not the clause | **stated**, with (BE-E4′) asserted to HOLD at all four witnesses |
| (BE-216)(i) `(BE-E4′) ⟸ ρ₁ + ρ₂ ≥ 8`, hypothesis-free | **PROVED**; `e_i = ρ_i − 2` asserted at every firing tuple, 1 575 asserted |
| (BE-216)(ii) the escapes' `ρ` sum census, maximum 7 | **PROVED by exhaustion**, asserted |
| (BE-216)(iii) 90-row in-regime census; `(BE-G_2)` fails 5, (BE-E4′) fails 0 | **MEASURED**; both counts asserted, the second as a guard |
| (BE-217)(i)–(vi) verdict, board, successor, bars, price, E-rider | **stated**, with every cap named in (v) |

**Reproduce.**

```
python3 notes/scripts/w4/bgtwoa.py arith     # (BE-210)/(BE-213)/(BE-215)/(BE-216), exhaustive
python3 notes/scripts/w4/bgtwoa.py rungs     # (BE-211)/(BE-212), CONSTRUCTED in exact Q
python3 notes/scripts/w4/bgtwoa.py hunt      # (BE-214), the kill + the 90-row census
python3 notes/scripts/w4/bgtwoa.py validate  # all three
```

**WHICH CONJUNCTS ARE TESTED.** `(BE-G_2a)` is *`c_j(Π_x) = 0` at the
non-firing side of a peel that is (a) an internal R-node peel with side 2
`rnode_shaped`, (b) inside the generic flag regime, (c) both-flexible, (d)
firing (`c_i(Π_x) = 2` for some `i`)*. `hunt` reads **all four separately and
never one**: (a) `rnode_shaped` is asserted on side 2 **and reported for side
1**, which is the conjunct the refutation turns on; (b) `flag_frame` is
asserted **non-None** rather than inferred from `e_row` returning a row —
`e_row`'s own gate is the weaker *"a plane at `x` and at `y`"*, and the two
are **not** the same test; (c) `δ₁, δ₂ ≥ 1` is asserted, so no witness is a
(BE-22)(vi) vacuity; (d) the firing set is computed and its **membership**
asserted, and the driver additionally asserts `0 not in fires` — i.e. that
the firing side is side **2** — because a witness with side 1 firing would
exhibit BEFOURP's configuration and not the asymmetry. `(BE-G_2)` and
`(BE-F_f)` are evaluated **per firing side**, so the `c₁ = c₂ = 2` cell (15 of
the 90) is tested on **both** sides.

**THE SAMPLER'S SUPPORT, AND WHICH GENERATOR PARAMETERS MOVED.** `arith` does
not sample: it enumerates `barch.all_tuples()` in full and prints the seed
**unused**. `rungs` does not sample either — it **constructs** every shape
from the named basis `e₁…e₄`, which is the whole point: a random 2-space is
never isotropic, so an assert about `Σ_x`/`Π_x` drawn at random passes
vacuously (`RESEARCH-ARC.md` §4). `hunt` moves **exactly one** generator
parameter against BEFOURP's `peel`: the **skeleton profile length**, 3 → 2/4/5
(`PEELJOBS` and `bline.legal_peel` hardcode 3), and widens the hub pairs to
the five non-adjacent pairs the two skeletons admit and the side-1 piece to
six bucket-A entries. Held fixed, and inherited as caps: the seed formula
(one draw per cell), `k = 2`, the field ℚ, the two skeletons, uniform
profiles, and `deg_2(x) = 3`.

**EVERY CAP, AS "NOT FOUND UNDER CAP C".** *(a)* A firing in-regime R-node row
pairing `ρ_i ∈ {4,5}` on the firing side with `e_j ≤ 6 − ρ_i` on the other —
the one shape that would refute **(BE-E4′) itself** — is **not found under**
the cap *"90 in-regime R-node rows, 5 hub pairs × 3 uniform profile lengths ×
6 bucket-A pieces, one seed each"*, and is **not excluded**; `ρ₂ ∈ {0,3,6}` is
quantized by the uniform profile length, so the search needs a non-uniform
profile or a side-2 family outside `bpeel.subdivided`. *(b)* A **fourth**
`c_j(Π_x) ≥ 1` mechanism beyond the ambient one ((BE-211)) and (BE-175)(i)'s
series end ((BE-214)) is **not found under** the same cap and is **not
excluded** — but it no longer matters for the frontier, which (BE-215)(i)
already retires. *(c)* `(BE-G_2)`'s failure is exhibited at **one tuple in
five embeddings**, not five shapes ((BE-217)(v)(c)). *(d)* (BE-216)(iii)'s
*"(BE-E4′) holds"* is **measured over those 90 rows only** and is **not** a
proof; (BE-216)(i)'s sufficient condition **is** proved.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bimage.pt_in` is **never called**, so its silent `K⁴` truncation is
unreachable rather than merely avoided. **No width-12 object is built**: every
`span`/`dim`/`isect`/`contains` call takes width-6 (`Λ²K⁴`) rows, which is
`bimage.span`'s rank-triggered `d == 6` branch, and the one `K⁴`-side
dimension (`rank([wedge3(v, p_x) …])`, whose rows are width-4) goes through
the width-agnostic `exactcore.rank`, **never** `bimage.span`/`dim`. `bwin` is
**not imported**, so `dehom`'s list-vs-tuple guard defeat is unreachable, and
**every configuration comes from `bproper.plant_peel`** rather than being
written here — except `rungs`, which writes no configuration at all and works
in `Λ²K⁴` from a standard basis.

**THE HARNESS-DEBT ROW THIS LANDING ADDS TO.** `w4/bgtwoa.py` is the next
`w4/` consumer of the standing sibling-import chain (`bgtwoa → bfour → barch →
bdegtwo → bline → bopen → bproper → bsigma → bsatur → … → kbare_common`), a
**second** consumer of `bfour.e_row`, a **fourth** of
`bproper.plant_peel`/`side_named`, a **fifth** of `bsigma.wedge3` (its own
**OVERDUE** item), a **second** of `bline.hcard_ok_piece` outside `bline`, and
a **first** of `bpeel.girth` from `w4/`. **All folded into the standing
sibling-import item, NO MOVE MADE**, by the rule that a dispatch does not move
a landed name. It opens **no new hazard item**, and it does **not** repair
(BE-213)(i)'s `barch.all_tuples` defect — recorded there as a debt item, since
repairing it would edit a tracked driver that ~30 landed figures cite.
