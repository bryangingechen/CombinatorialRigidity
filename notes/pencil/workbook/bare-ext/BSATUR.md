## §(K-bare-ext) — continuation (direction BSATUR): **(PENCIL-SATURATES) IS FALSE, AND THE REPAIR IS FREE** — the clause BDOUBLE's redundancy theorem rests on fails at **exactly `ρ_i = 5`**, at a flag that is legal, inside the **generic flag regime**, at an **internal R-node peel**, through both gates: at a terminal of side-degree `1` the legal planes at `x` form a **pencil** (those through `p_x ∨ p_{c₁}`), a plane is bad exactly when it carries a `t` with `p_x ∧ t ∈ ρ̄_i`, and since (M1) puts `ℓ_e` in `ρ̄_i ∩ Σ_x` always, **a bad plane exists iff `dim(ρ̄_i ∩ Σ_x) ≥ 2`, which is `ρ_i ≥ 5`** — so the witness `K4(5,3,3,3,3,3)` peeled at its 5-branch has `c₁(Π_x) = 2` with `ρ₁ = 5`, `δ = (5,3)`, `a = (0,0)`, and the peel still **ATTAINS**. **Every sampler in the corpus draws that plane at random**, so the 24 × 14 run's `assert not (cuv >= 2 and r1 < 6)` — a genuine assert, read at source — could never fire: **the middle clause over-read a SUFFICIENT condition as a characterization; the third clause over-read a GENERIC statement as a UNIVERSAL one**, the same shape at a different quantifier. **The price is SLACK, not a shortfall** — `margin ≤ 0` and `reach = min(δ₁+δ₂,6)+a₁+a₂` asserted at **260** exhibited bad-flag rows over three skeletons, **0** shortfalls — but at **76** of them `Π_x` is exactly **tight** with `ρ₁ = 5`, so **(BE-101)(i)'s PROOF is gone**: with the clause replaced by its measured floor `c_i(Π) = 2 ⟹ ρ_i ≥ 5`, **24** `Π_x` violations **escape** `U = Λ²K⁴` (controls: **0** under the landed clause, reproducing (BE-101)'s 300/300, and **313** under none, reproducing its negative control). **The repair is (PENCIL-SATURATES-GEN)** — the same clause read **at the generic flag** — and it is **FREE**, because (BE-14) is **EXISTENTIAL** ((BE-16)), the good locus is dense on an irreducible chart ((BE-69)) and `reach` is lower-semicontinuous, so the arc only ever needs a generic flag; under it **(BE-101)(i)/(ii) hold verbatim and the 14 → 12 drop stands**. At a terminal of side-degree `≥ 2` there is **no flag freedom at all** — `Π_x` is the span of two of the side's *own* hinge lines — so the clause needs no repair there. **Job 2's `⟨M⟩` hunt fires EMPTY**: **0** both-sides `c_i(⟨M⟩) = 1` rows and **0** sides exceeding the generic profile at `⟨M⟩` over **72** peel rows, the first measurement of the 12-block residue. The coordinator's reading — (PENCIL-SATURATES) as (BE-33)'s **(P) trap** read as vacuity — is **INAPPLICABLE** (its ambient is a side-1-plus-**EAR** composition and its content is the ear's *loss*, not `ρ̄₁`'s dimension) **and refuted outright by the witness**, which is the (P) trap genuinely realized at a non-vacuous piece

### Standing notation

BUNIF's, unchanged (*Steps BE93–BE97*): `H` an internal R-node piece peeled at
`{x, y}`, sides `H₁, H₂`, `ρ̄_i ⊆ Λ²K⁴`, `ρ_i = dim ρ̄_i`, `δ_i = f_i − g_i`,
`a_i = dim M_i − 6 − f_i`, blocks `Π_x, ⟨M⟩, ⟨L⟩, Π_y`, `c_i(U) = dim(ρ̄_i ∩ U)`.
Two objects are used here that the block frame does not name:

- **`Σ_z := p_z ∧ K⁴`** — the 3-dimensional space of lines through `p_z`
  (already in BUNIF's notation list, unused there); `Π_z = Σ_z ∩ Λ²π_z`.
- **the BAD PLANE at `x`** — prose, not a token: a legal `π_x` with
  `Π_x ⊆ ρ̄_i`.

One name is minted: **(PENCIL-SATURATES-GEN)**, the repaired clause.

### Step BE103 — (BE-104): (PENCIL-SATURATES) is FALSE, and the witness is a real peel

> **(BE-104)(i)** *(**THE REFUTATION**, exhibited at an internal R-node peel)*
> Take the subdivided `K₄` skeleton with branch-length profile
> `(5,3,3,3,3,3)`, peeled at the skeleton edge `{A, B}` carrying the
> **5-branch**. Then `{x, y} = {A, B}` is a 2-cut, the peel is
> **R-node-shaped** (`bpeel.rnode_shaped`, BPEEL's disclosed stand-in), side 1
> **is** that 5-edge branch — so `deg₁(x) = 1`, a **series end** — and side 2 is
> the rest. Draw one legal configuration; then there is a plane `π_x` through
> `p_x` at which **all** of the following are asserted, not reported:
>
> - `π_x` **is** `plane_at`'s closed-star plane of `x` **in the whole graph**,
>   so the pencil condition at `x` holds with **side 2's** neighbours of `x`
>   inside it as well;
> - the configuration passes `assert_generic_star` **and**
>   `kbare_common.verify_pencil_witness` (`bdecor.assemble`'s two gates);
> - the flag pair is in the **generic regime** (`bunif.flag_frame` non-`None`:
>   `π_x ≠ π_y`, `p_x ∉ π_y`, `p_y ∉ π_x`);
> - **`Π_x ⊆ ρ̄₁` as SPACES, with `ρ₁ = 5`.**
>
> Hence `c₁(Π_x) = 2` at `ρ₁ = 5 < 6`: **(PENCIL-SATURATES) is FALSE.**
> Measured at **4 of 6** independent seeds (the other two failed to draw, not to
> refute), each with `δ = (5,3)`, `a = (0,0)`, `c₁(Π_y) = 1`, `c₂(Π_x) = 0`.
> **F13 negative control**: at the *same* side-1 configuration the sampler's own
> random plane at `x` gives `c₁(Π_x) = 1`, asserted — which is the whole
> explanation of the landed measurement.

> **(BE-104)(ii)** *(what is refuted, and what is NOT — said before anything
> else)* **Not** `PencilPair K 3 G`; **not** half (B) — the witness peel
> **attains** ((BE-106)(i)); **not** (BE-101)(i) as a theorem, whose content is
> *"given (PENCIL-SATURATES)"* and which is untouched as an implication; **not
> one landed measurement** — every histogram, every `0 of 4`, every `92/92` in
> *Steps BE93–BE102* stands, because each was taken at a **drawn** flag and the
> refutation lives at a flag no sampler draws. What falls is **the universal
> reading of one prose clause**, and with it (BE-101)(ii)'s corollary as an
> *unconditional* statement at an arbitrary legal flag. It is a
> **candidate-side correction of exactly (BE-45)(iii)'s kind**, one clause
> further along the same sentence.

### Step BE104 — (BE-105): the mechanism, the threshold `ρ = 5`, and the quantifier that was over-read

> **(BE-105)(i)** *(proven; **THE BAD PLANE**, and it is elementary)* Let `x` be
> a terminal with `deg_i(x) = 1` and `e = x c₁` the unique side-`i` edge there.
> The closed star of `x` is `{p_x, p_{c₁}} ∪ (side 2's neighbours of x)`, and by
> (BE-70)(ii) side 2 may be moved at a fixed flag pair, so the **legal planes at
> `x` are exactly the pencil of planes through the line `p_x ∨ p_{c₁}`**. Write
> `q : K⁴ → Σ_x`, `t ↦ p_x ∧ t`, a surjection with kernel `⟨p_x⟩`. For a legal
> `π`,
>
> **`Π_x = p_x ∧ π ⊆ ρ̄_i ⟺ π ⊆ q^{-1}(ρ̄_i ∩ Σ_x)`,**
>
> and `dim q^{-1}(ρ̄_i ∩ Σ_x) = 1 + dim(ρ̄_i ∩ Σ_x)`. By (BE-45)(i) **(M1)**
> `ℓ_e ∈ ρ̄_i`, and `ℓ_e ∈ Σ_x`, so that intersection is never `0`. Therefore:
>
> - `dim(ρ̄_i ∩ Σ_x) = 1` ⟹ `q^{-1}(ρ̄_i ∩ Σ_x) = ⟨p_x, p_{c₁}⟩`, a **line** of
>   `P³`, which no plane is contained in: **no legal plane is bad**;
> - `dim(ρ̄_i ∩ Σ_x) = 2` ⟹ `q^{-1}(ρ̄_i ∩ Σ_x)` is a 3-space containing `p_x`
>   and `p_{c₁}`, i.e. **one** plane of the legal pencil: **exactly one** legal
>   plane is bad;
> - `dim(ρ̄_i ∩ Σ_x) = 3`, i.e. `Σ_x ⊆ ρ̄_i` ⟹ `q^{-1}(ρ̄_i ∩ Σ_x) = K⁴` and
>   **every** legal plane is bad. ∎
>
> No genericity, no draw. The trichotomy is the whole mechanism.

> **(BE-105)(ii)** *(the THRESHOLD: `max(1, ρ_i − 3)`, so the failure sits at
> `ρ_i = 5` and nowhere below)* The modular law gives
> `dim(ρ̄_i ∩ Σ_x) ≥ ρ_i + 3 − 6`, and (M1) gives `≥ 1`; **equality**
>
> **`dim(ρ̄_i ∩ Σ_x) = max(1, ρ_i − 3)`**
>
> is **asserted** at every `deg = 1` terminal of BEARCASE's 24-piece battery —
> `ρ = 3 ↦ 1`, `4 ↦ 1`, `5 ↦ 2`, `6 ↦ 3` — never reported. With (i) this says: a
> bad plane exists **iff `ρ_i ≥ 5`**, and at `ρ_i = 5` it is **unique**. So
> (PENCIL-SATURATES)'s failure locus is exactly `ρ_i = 5`, one value; the clause
> is **true at `ρ_i ≤ 4` for a proved reason** and its measured floor is
>
> **`c_i(Π) = 2 ⟹ ρ_i ≥ 5`,**
>
> which is what (BE-106)(ii) enumerates against.
>
> > **SCOPE CORRECTED and one half UPGRADED, 2026-09-02, direction BSIGMA.**
> > The identity `dim(ρ̄_i ∩ Σ_x) = max(1, ρ_i − 3)` is a statement about
> > **generic configurations of a PATH side** — the battery's five `deg = 1`
> > terminals are exactly its five path pieces, one generic draw each
> > ((BE-111)(i)). On that class the `≤` half is now **PROVED**, not measured
> > ((BE-110)(iii)). Off it the identity is **FALSE**: the tail stratum gives
> > `dim = 3` at `ρ = 5` ((BE-109)). See *Steps BE108–BE112*.

> **(BE-105)(iii)** *(**why the 24 × 14 run could not fire**, and which
> quantifier was over-read)* The assertion behind (BE-38)(iii)'s third clause is
> real and was read **at source**: `bearcase.py`'s `run_betahunt` carries
> `assert not (cuv >= 2 and r1 < 6)` with the message *"Π_u ≤ ρ̄₁ at a
> NON-vacuous piece — this would be the (P) trap, genuinely realized"*, where
> `cuv` is the minimum of `dim(ρ̄₁ ∩ Π_u)` over the draws attaining `r1 = max
> dim ρ̄₁` — i.e. the **generic** value of both. So the driver does assert the
> clause. But **the plane at a degree-1 terminal is drawn at random**:
> `bearcase.sample_piece_config` draws a free normal at `u`, and
> `bdecor.flag_assignment` fills a hub plane with random points whenever no
> length-1 branch constrains it. The bad plane is **one member of a
> 1-parameter family**, so no sampled run can reach it, and the assert could
> never fire. **This is (BE-45)(iii)'s failure shape at a different
> quantifier**: the middle clause over-read a *sufficient* condition as a
> *characterization*; the third clause over-read a *generic* statement as a
> *universal* one. Both are summary sentences outrunning their own table, and
> this is the **third** time in the sub-arc ((BE-36), (BE-45)(iii), here).
>
> **And the expected defect was NOT the one found — worth recording, because the
> two are easy to confuse.** The natural guess (and this direction was dispatched
> with it) is a **converse/contrapositive slip** of the kind (BE-102)(iii) caught
> in (BE-44)(ii): the table shows `2` at the `ρ₁ = 6` rows, which is
> `ρ₁ = 6 ⟹ …`, and the clause asserts the other direction. That is **not** what
> happened. (BE-38)(iii)'s own wording is *"`2` occurring at **exactly** the
> `ρ₁ = 6` rows"*, and *exactly* carries **both** directions over the population
> measured — so on its own table the third clause is a **faithful** readout, and
> the driver's assert makes it a real claim about every draw the run made. The
> defect is one level up: the run varied the **configuration** and never the
> **flag**, and the clause is false only off the flags it drew. A converse slip
> is a reading error inside a table; this is a **quantifier the sampler never
> ranged over** — the same relationship (BE-46)(i)/(ii) formalizes for
> configurations, applied to a variable the arc had not noticed was free.

> **(BE-105)(iv)** *(the `deg_i(x) ≥ 2` regime, where the clause needs no
> repair)* If `deg_i(x) ≥ 2`, two edges `e, e'` of side `i` at `x` give distinct
> hinge lines (`assert_generic_star`), both in `Π_x` ((BE-16)), so
> **`Π_x = ⟨ℓ_e, ℓ_{e'}⟩`** — asserted as an identity of spaces at **19** of the
> 24 battery pieces. The flag therefore carries **no freedom at `x` at all**,
> the bad-plane mechanism cannot run, and `c_i(Π_x) = 2` is a closed condition
> on side `i`'s **own** configuration — generic-or-never by (BE-46)(i)/(ii). On
> that class `c = 2 ⟹ ρ = 6` is **asserted and holds at 19/19**.

### Step BE105 — (BE-106): the price — SLACK, not a shortfall, but (BE-101)(i)'s proof is gone

> **(BE-106)(i)** *(measured; **the refutation is on the SLACK side**, as
> BDOUBLE's was)* Over subdivided `K₄` (every 3rd profile of `{1..4}⁵` with the
> peeled branch at `5`), prism and `K_{3,3}` (16 seeded profiles each), 2 draws
> each: **451** drawn peel rows, **260** of them **bad-flag rows**
> (`c₁(Π_x) = 2` with `ρ₁ = 5`, the plane constructed by (BE-105)(i)). At every
> one, **asserted**: `margin ≤ 0` at `Π_x` **and** at `Π_y`, `⟨M⟩` and `Λ²K⁴`;
> and `reach = min(δ₁+δ₂, 6) + a₁ + a₂`, so **the peel ATTAINS**. Margin
> histogram at `Π_x`: `{−3: 28, −2: 4, −1: 152, 0: 76}`. **0 shortfalls.**
> `(c₁, c₂)` at `Π_x`: `(2,0): 233`, `(2,1): 23`, `(2,2): 4`. So half (B) is
> **not** refuted, and the coordinator's pre-priced reading of a refutation —
> *"it removes the redundancy theorem's hypothesis, not half (B)"* — is
> **confirmed**.

> **(BE-106)(ii)** *(**what it does cost**: (BE-101)(i)'s proof, quantified)*
> At **76** of the 260 rows the `Π_x` inequality is **exactly tight** while
> `ρ₁ = 5`, so (BE-101)(i)'s step *"`c₁(Π_x) = 2`, hence `c₁(Λ²K⁴) = ρ₁ = 6`"*
> is simply unavailable there. Enumerated exhaustively over the **same** tuple
> space (`bdouble.py arith`'s, `c_i ≤ min(2, ρ_i)`, `ρ_i = δ_i + a_i ≤ 6`), with
> the clause replaced by its measured floor `c_i(Π) = 2 ⟹ ρ_i ≥ 5`:
>
> | clause imposed | admissible tuples | `Π_x` violations | **escape `U = Λ²K⁴`** |
> |---|---|---|---|
> | `c_i(Π) = 2 ⟹ ρ_i = 6` (the landed clause) | 3 844 | 300 | **0** |
> | `c_i(Π) = 2 ⟹ ρ_i ≥ 5` (the measured floor) | 4 624 | 648 | **24** |
> | none (F13 negative control) | 6 400 | 1 655 | **313** |
>
> The first and third rows **reproduce (BE-101)(i)'s own `300 / 300, 0 escape`
> and `313` exactly**, which is what makes the middle row comparable. Smallest
> escapee: `δ = (0,0)`, `a = (1,5)`, `c = (1,2)`. **Read this the right way**:
> the 24 are **arithmetic**, i.e. the theorem's *proof* is gone, not that any of
> them is realized — (i) found **none** realized.

> **(BE-106)(iii)** *(the live-block count, stated both ways)* As a **pointwise**
> statement at an arbitrary legal flag, `Π_x` and `Π_y` are **back among the
> live blocks: 12 → 14**, and BUNIF's tight place at `Π_x` is re-opened. As a
> statement at the **generic** flag, they stay out and the count stays **12** —
> that is (BE-107). The honest one-line summary is: **BDOUBLE's reduction
> survives, with its hypothesis's quantifier corrected.**
>
> > **A THIRD READING, 2026-09-02, (BE-112)(ii), direction BSIGMA.** Between
> > the two readings here sits a third: pointwise **in the configuration** at
> > a generic flag, `Π_x`/`Π_y` are **back among the 14**, because the bad
> > configurations are not avoided by choosing a generic flag. Only at a
> > generic point of `Chart(H)` does the count stay **12**.

### Step BE106 — (BE-107): the repair, and it is FREE

> **(BE-107)(i)** *(**(PENCIL-SATURATES-GEN)**, and why the arc may have it for
> nothing)* Name the repaired clause
>
> > **(PENCIL-SATURATES-GEN).** At a **generic** flag of an internal R-node peel
> > in the generic flag regime, `c_i(Π) = 2 ⟹ ρ_i = 6` — at `Π = Π_x` and at
> > `Π = Π_y`.
>
> By (BE-105)(i)/(ii) the bad flags at a `deg_i(x) = 1` terminal are a **single
> member** of a 1-parameter pencil, hence a proper closed subset, exactly when
> `Σ_x ⊄ ρ̄_i` — which the threshold gives at every `ρ_i ≤ 5`; by (BE-105)(iv)
> there is no flag freedom at all at a `deg_i(x) ≥ 2` terminal. So
> (PENCIL-SATURATES-GEN) is (PENCIL-SATURATES) with its **flag quantifier**
> repaired, and **(BE-101)(i) and (ii) hold verbatim under it** — the proof
> quotes the clause once, at the flag the obligation is being evaluated at.
>
> **It costs the arc nothing**, and this is the load-bearing sentence: (BE-14)
> is **EXISTENTIAL, not generic** ((BE-16)), so the arc must exhibit **one**
> attaining configuration; the good locus is Zariski-open on the irreducible
> `Chart(H)` and hence **dense or empty** ((BE-69)); and `dim(ρ̄₁ + ρ̄₂)` is
> lower-semicontinuous, so the **maximum** reach is attained on a dense open
> set — the generic flag is exactly where the arc already computes. A
> codimension-1 family of bad flags is the kind of locus an existential target
> is entitled to avoid.
>
> > **WARRANT CORRECTED 2026-09-02 by (BE-122)/(BE-123), direction BOPEN —
> > the CONCLUSION stands and the residue gets SMALLER.** *"The good locus is
> > Zariski-open … ((BE-69))"* cites (BE-69) for a locus it is not about:
> > (BE-69)(i)'s subject is the **attainment** locus `A₁ ∩ A₂ ∩ GP`, proved
> > open by rank **lower** bounds, and saturation is an **upper** bound on an
> > intersection dimension, so that proof does not transport. It is not
> > needed: the bad locus is **constructible**, and on an **irreducible**
> > chart a constructible set with empty interior is nowhere dense — which is
> > strictly weaker than open and is all *generic* means. The half of the
> > sentence that is load-bearing is *irreducible*, and that is
> > **(CH-1)(a)**, one level down. Nothing in this step's verdict changes.
>
> > **REFUTED AS STATED 2026-09-02 by (BE-109), direction BSIGMA — read this
> > with *Steps BE108–BE112*.** (PENCIL-SATURATES-GEN) quantifies the flag
> > generically but the **configuration** universally, and the configuration
> > quantifier is where it fails: at the tail stratum `Σ_x ⊆ ρ̄_i` at
> > `ρ_i = 5`, so **every** flag is bad. The clause survives as
> > **(PENCIL-SATURATES-CHART)** — the same statement at a generic point of
> > `Chart(H)` — free by the same argument, and now with the bad locus
> > **proved** proper at a path side ((BE-110)(iii)).

> **(BE-107)(ii)** *(what the repair is NOT free for — said plainly)* It is free
> **only** because the target is existential. Any later step that needs the
> block inequalities at **every** legal flag — a *uniform* statement over the
> flag base, a *closure* argument, or anything that quantifies the class
> statement before choosing a configuration — does **not** get the repair, and
> there `Π_x`/`Π_y` are live and (BE-106)(ii)'s 24 escapees are the price.
> Nothing in the arc as it stands does that; this is recorded so a future
> direction does not assume it.
>
> > **SCOPE WIDENED, 2026-09-02, (BE-112)(iv).** Read "at every legal flag"
> > as "at every point of the chart": a *uniform* statement over
> > configurations, a closure argument, **or a degeneration argument that
> > lands on a stratum**, equally forfeits the licence. The last is the new
> > one and the most likely to be reached for.

> **(BE-107)(iii)** *(the residual for the repair, named rather than smoothed)*
> The one configuration that would kill (PENCIL-SATURATES-GEN) as well is
> **`Σ_x ⊆ ρ̄_i` with `ρ_i ≤ 5`** — every legal plane bad, so no genericity
> saves it. (BE-105)(ii)'s threshold **excludes it at every `deg = 1` terminal
> of the 24-piece battery** (`ρ = 5 ↦ 2`, never `3`), and the modular law makes
> it impossible below `ρ_i = 3`. It is **named and measured absent, not
> excluded**: a shape forcing `dim(ρ̄_i ∩ Σ_x) = 3` at `ρ_i = 5` would refute
> the repair too, and that — not the original clause — is the thing to hunt.
>
> > **REALIZED 2026-09-02 by (BE-109), direction BSIGMA — this residual is no
> > longer "measured absent".** The shape exists, at `ρ_i = 5`, on this
> > direction's own witness peel, in the generic flag regime: place the peeled
> > branch with `p_x` and its tail coplanar. And the "impossible below
> > `ρ_i = 3`" bound is improved to **impossible below `ρ_i = 5`** at a path
> > side, by a proof ((BE-110)(ii)).

### Step BE107 — (BE-108): job 2's `⟨M⟩` verdict, job 3's residual, the board, and the reading

> **(BE-108)(i)** *(**job 2**: the `⟨M⟩` hunt, and it fires EMPTY)* (BE-97)(iv)
> names `c_i(⟨M⟩) = 1` on **both** sides — both relative screw spaces containing
> the virtual edge's own line `M = p_x ∨ p_y` — as the one shape that would put
> a second block in play at once. Over **72** peel rows of BUNIF's two
> populations (A with 2 draws, B with 40 tier jobs), with
> `max(0, ρ_i − 5) ≤ c_i(⟨M⟩) ≤ 1` **asserted** at every side:
>
> | statistic | result |
> |---|---|
> | `(c₁(⟨M⟩), c₂(⟨M⟩))` census | `(0,0)`: **70**; `(0,1)`: **2**; `(1,1)`: **0** |
> | both-sides hits | **0** |
> | sides **exceeding** the generic profile at `⟨M⟩` (i.e. `c_i = 1` with `ρ_i ≤ 5`) | **0** |
>
> **Verdict (F11): none found under this cap** — *"no both-sides `⟨M⟩` row in
> these 72"*, never *"does not exist"*. It is the **first** measurement of the
> 12-block residue (BE-103)(i) item 2 left *unwitnessed rather than excluded*,
> and the residue is now *measured-empty-at-72* rather than unmeasured.
> **Structural note, offered as a reason the shape is hard and not as a proof**:
> `M ∈ ρ̄_i ⊆ ⟨P⟩` for **every** `x–y` path `P` of side `i`, and the two cheap
> constructions that force `M` into a side — putting a neighbour of `x`, or of
> `y`, on the line `M`, which makes `M` a hinge line outright — each put
> `p_y ∈ π_x` (resp. `p_x ∈ π_y`) and so **leave the generic flag regime**,
> where the whole block law lives ((BE-98)).

> **(BE-108)(ii)** *(**job 3**: the residual, in (BE-97)(iv)'s terms and not one
> word stronger)* **Half (B) is NOT discharged.** Against (BE-103)(i)'s four
> items:
>
> 1. **(PENCIL-SATURATES) is settled — negatively.** Item 1 is closed as posed
>    and **replaced** by (PENCIL-SATURATES-GEN), which is *still a measurement*
>    (the threshold at 24 pieces, the deg-`≥2` class at 19) with its own named
>    residual ((BE-107)(iii)) — **which (BE-109) then REALIZED, replacing the
>    clause again by (PENCIL-SATURATES-CHART)**. The denominator is no longer *"4 sides at
>    `c_i(Π) = 2`"*: it is **260 exhibited bad-flag rows** plus the threshold
>    identity, which is a different and better kind of evidence.
> 2. **The other 12 live blocks**: `⟨M⟩` is now **measured empty at 72 rows**;
>    the remaining 11 are still *unwitnessed rather than excluded*.
> 3. **The non-attaining case** — unchanged; (BE-101)(ii) is an `a₁ = a₂ = 0`
>    statement and off it `U = Λ²K⁴` is live ((BE-101)(iii)).
> 4. **The ear case's (β) side at the window**, modulo §(K-bare-ext)'s own two
>    window conditions, and **cross-pair welding** ((BE-28)(i)) — unchanged.
>
> **The board. What moved.** A landed clause is refuted and its repair is
> exhibited and priced; the failure locus is pinned to one value of `ρ_i` by a
> proved trichotomy; `⟨M⟩` is measured for the first time. **What did not
> move.** No class statement is proved; **no shortfall is exhibited** —
> 260 bad-flag rows all attain; `hbareSplit`, `hK`, (GR-15) and class
> uniformity of the escape are untouched; the coincident regime ((BE-98)(i))
> still keeps only the cap.

> **(BE-108)(iii)** *(**the coordinator's reading**, classified — and it is the
> second **INAPPLICABLE**)* The reading was: *(PENCIL-SATURATES) may be
> (BE-33)'s **(P) trap** read as a vacuity statement, with (BE-34) already
> saying every trap is a configuration artifact.* It is **INAPPLICABLE, on the
> ambient the prep itself named as the risk**, and the ambient is only the first
> of two misses:
>
> - **Ambient.** (BE-33)/(BE-34) are stated for the composition *(side 1) ∪
>   **ear**(m)*, and (P) is a lower bound on the **ear's** loss
>   `dim(A ∩ ρ̄₂)` when `A ⊇ Π_u`. The general-piece side of a peel is not an
>   ear, and (BE-34)(iii)'s escalation rebuilds trapped rows as
>   `G' = (side 1) ∪ ear(m)`. **Check the ambient before the statement** —
>   `RESEARCH-ARC.md` §7's seventh kind, minted by BBASE.
> - **Content.** Even inside that ambient the reading misreads what is proved:
>   (BE-34)(iii) says every trapped row **reaches the criterion once side 1 is
>   allowed to move**, a statement about the *composition's attainment*, never
>   that `Π_u ⊆ ρ̄₁` forces `ρ̄₁ = Λ²K⁴`. There is no vacuity statement to
>   inherit.
> - **And it is refuted outright by the witness.** (BE-104)(i) exhibits
>   `Π_x ⊆ ρ̄₁` at `ρ₁ = 5` — a **non-vacuous** piece — which is *precisely* the
>   configuration `bearcase.py`'s assert calls *"the (P) trap, genuinely
>   realized"*. So the (P) trap is realizable where it is **not** vacuous, and
>   the reading is false in the direction it was offered.
>
> **Tally**: ten instances, **seven kinds**; INAPPLICABLE now has **two**.

> **(BE-108)(iv)** *(classification, mandatory and explicit)* **What is
> refuted**: one prose clause, **(BE-38)(iii)'s third**, as a universal
> statement — and with it (BE-101)(ii) read at an arbitrary legal flag; plus the
> coordinator's reading. **What is NOT refuted**: `PencilPair K 3 G`;
> `hbareSplit`; (BE-14)-for-all-`G`; the 2-cut step; half (B); (BE-101)(i) as an
> implication; **any** landed measurement. **No route is closed. One route is
> narrowed** — the clause the redundancy theorem rests on is now a *generic-flag*
> statement with a named residual. **Not a PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 2 — REFUTED**, with a witness at an internal R-node peel in the
  generic flag regime, through both gates ((BE-104)). And **priced exactly as
  the prep asked**: it removes the redundancy theorem's hypothesis, **not** half
  (B) — the witness peel attains ((BE-106)(i)).
- **HIT shape 3 — REDUCED**, twice over: the failure locus is **exactly
  `ρ_i = 5`** by a proved trichotomy ((BE-105)(i)/(ii)), and the clause survives
  verbatim on the `deg_i(x) ≥ 2` class with **no flag hypothesis at all**
  ((BE-105)(iv)).
- **HIT shape 4 — job 2's `⟨M⟩` verdict**, empty at 72 rows with the cap and
  denominator named ((BE-108)(i)).
- **HIT shape 5 — the residual and the E-rider** ((BE-108)(ii), *TERMINATION
  riders*).
- **The coordinator's reading: INAPPLICABLE and refuted** ((BE-108)(iii)) — the
  second instance of the kind, and its ambient risk was the one the prep named.
- **NOT HIT shape 1** — (PENCIL-SATURATES) is **not** proved; it is **false**.
  What is delivered instead is the repair, and the repair is **free only because
  the target is existential** ((BE-107)(ii)).
- **The price, stated as a price.** (a) (PENCIL-SATURATES-GEN) is **still a
  measurement**, on a 24-piece battery and a 260-row scan; the threshold
  identity `dim(ρ̄_i ∩ Σ_x) = max(1, ρ_i − 3)` is asserted, not proved (only its
  `≥` half is). (b) (BE-107)(iii)'s `Σ_x ⊆ ρ̄_i` shape is **named, not
  excluded**. (c) The scan's populations are **constructed** subdivided
  skeletons, not a census. (d) The bad plane is exhibited at `deg_i(x) = 1`
  terminals only; whether a `deg ≥ 2` shape can force `c = 2` below `ρ = 6` is
  measured-no at 19 pieces and **not** argued.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py witness   #   1.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py mech      #  77.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py arith     #   0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py mhunt     #  26.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py scan      # 131.7 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsatur.py validate  # 137 s (reduced scan, all five)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single seed is
`20260902`, printed by every mode. Every headline is an `assert`, not a report:
the witness's seven identities at every seed (including the F13 negative
control), the threshold `max(1, ρ_i − 3)` at every degree-1 terminal,
`Π_u = ⟨ℓ_e, ℓ_{e'}⟩` as spaces at every degree-`≥2` terminal, `margin ≤ 0` at
four blocks and `reach = min(δ₁+δ₂,6)+a₁+a₂` at every one of the 260 bad-flag
rows, `0 ≤ c_i(⟨M⟩) ≤ 1` with the modular lower bound at every side of the 72,
and the two enumeration controls that reproduce (BE-101)(i)'s own figures.

### Caps, disclosed rather than smoothed — with the denominator named

1. **The refutation needs no cap.** (BE-105)(i) is a trichotomy with no
   genericity in it; the witness supplies only the **realizability** of a peel
   meeting its hypotheses, and that is asserted at 4 independent seeds.
2. **The threshold is a 24-piece measurement.** `max(1, ρ_i − 3)` is asserted at
   the **5** degree-1 terminals and the `deg ≥ 2` clause at the **19** others of
   BEARCASE's battery, one guarded draw each at the measured max `ρ` over 6
   seeds. Its `≥` half is the modular law plus (M1) and is **proved**; the `≤`
   half is **measured**. BEARCASE's own shape guard (branch vertices an
   independent set; subdivisions with each base edge split at least three ways)
   is inherited verbatim.
3. **The scan is a constructed population.** 374 skeleton profiles — subdivided
   `K₄` at every 3rd profile of `{1..4}⁵` with the peeled branch at `5`, plus 16
   seeded profiles each of the prism and `K_{3,3}` — 2 draws each, **451** drawn
   rows and **260** bad-flag rows. *"0 shortfalls"* is a statement about those
   260. It is a **new** population (BUNIF's two are not used here), which is why
   it is not evidence about BUNIF's 92.
4. **The `⟨M⟩` hunt rides BUNIF's populations unchanged** — A = BDECOR's 7
   R-node pieces + BPEEL's nested one; B = `bpeel.constructed_tier(maxlen=3,
   nsamp=60)` behind `rnode_shaped` — **72** rows. It adds no population, so its
   *"none found"* inherits (BE-98)'s caps verbatim.
5. **`rnode_shaped` is BPEEL's disclosed stand-in** for *"a virtual edge of a
   simple 3-connected SPQR skeleton"*, not an SPQR implementation. Every peel
   here is R-node-shaped **in that sense**.
6. **The bad plane is constructed at `deg_i(x) = 1` only.** Nothing here says a
   `deg ≥ 2` shape cannot fail the clause; (BE-105)(iv) measures it does not, at
   19 pieces.

### Harness note — the `kbare/` sibling-import set gains its TWENTY-SECOND consumer

`w4/bsatur.py` imports `bunif`, `bdecor`, `bpeel`, `bearcase`, `bimage`,
`binduc` and `exactcore` read-only and reimplements none of them: no deficiency
oracle, no `ρ̄`, no peel scan, no sampler, no R-node stand-in and no block
decomposition is rewritten. It is the **twenty-second** `kbare/` consumer and
takes the chain **twenty** deep (`… → bunif → bdouble → bsatur`). The recorded
**unpaid** sibling-import debt (`notes/scripts/README.md` *Harness debt*) is
unchanged; **no move made**. BDOUBLE's set-diff probe was not retained, and this
landing ships its own (`notes/scripts/gapdiff.py`) for the F21 label check.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-104)(i) (PENCIL-SATURATES) is FALSE | **REFUTED BY WITNESS** — 4 seeds, both gates, generic regime, R-node-shaped, `Π_x ⊆ ρ̄₁` asserted as spaces |
| (BE-104)(ii) nothing landed is refuted with it | **ARGUED**, and the F13 control is the evidence |
| (BE-105)(i) the bad-plane trichotomy | **PROVED** — one surjection and a dimension count |
| (BE-105)(ii) `dim(ρ̄ ∩ Σ_x) = max(1, ρ − 3)` | `≥` **PROVED** (modular law + (M1)); `=` **MEASURED**, asserted at 5 terminals |
| (BE-105)(iii) the run could not fire | **VERIFIED AT SOURCE** — the assert and both samplers read, not inferred |
| (BE-105)(iv) no flag freedom at `deg ≥ 2` | **PROVED** (two distinct hinge lines span a 2-space); the `c = 2 ⟹ ρ = 6` clause there **MEASURED** at 19 |
| (BE-106)(i) slack, not a shortfall | **MEASURED**, 260 rows, `margin ≤ 0` and attainment asserted |
| (BE-106)(ii) 24 escapees | **PROVED** (exhaustive enumeration), with both controls reproducing (BE-101)'s figures |
| (BE-107)(i) the repair is free | **ARGUED** from (BE-16) + (BE-69) + semicontinuity; **not** a new theorem |
| (BE-107)(iii) `Σ_x ⊆ ρ̄_i` absent | **MEASURED**, 5 terminals — the thinnest number here |
| (BE-108)(i) the `⟨M⟩` hunt | **MEASURED EMPTY**, 72 rows |
| (BE-108)(iii) the reading | **INAPPLICABLE** (ambient) **and REFUTED** (by the witness) |

### What would change this

- **A `deg_i(x) ≥ 2` shape with `c_i(Π_x) = 2` and `ρ_i < 6`** would show the
  refutation is not confined to series ends and would kill the repair's second
  half.
- **A shape forcing `dim(ρ̄_i ∩ Σ_x) = 3` at `ρ_i = 5`** would make **every**
  legal plane bad and refute (PENCIL-SATURATES-GEN) as well ((BE-107)(iii)).
- **A bad-flag row with `margin > 0`** — `δ₂ ≤ 2` and `c₂(Π_x) ≥ slack + 1` is
  the arithmetic shape — would be the arc's **first exhibited shortfall** and
  would matter far more than this landing does.
- **A both-sides `c_i(⟨M⟩) = 1` row in the generic flag regime** would re-open
  the block (BE-97)(iv) named.
- **A step that needs the block inequalities at every flag** would remove
  (BE-107)(i)'s licence and put `Π_x`/`Π_y` back among the fourteen for good.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/pencil/fanout-archive.md`, with the
2026-09-02 correction (`61e046a6`) in force: **"the target" in E1–E3 is the
ARC's target, `PencilPair K 3 G`**, never a direction's local obligation. The
corpus carries **two** E3 texts; **this reading is `:1700`'s two-conjunct
form**, with `:2098`'s one-conjunct deviation noted and **not** used — as BBASE,
BUNIF and BDOUBLE all read it.

- **E1** — a g-flank, a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: no colourings, no `D`, no g-flank here.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on either
  conjunct**, and the distinction BDOUBLE made sharp is exactly the one this
  landing needs: what is refuted is **(PENCIL-SATURATES)**, a clause a landed
  theorem is conditional on — a direction's local obligation — **not**
  `PencilPair K 3 G`. And this landing names dispatchable attacks
  ((BE-107)(iii)'s `Σ_x` shape; (BE-108)(ii) items 2–4).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct.** Under `:2098`'s
  one-conjunct text it still does not fire, the first conjunct being the one
  that fails.

**F11 — the central rider, and the target was again a universal claim.** *"For a
side of an internal R-node peel, `dim(ρ̄_i ∩ Π) = 2 ⟹ ρ_i = 6`"* is a `∀` that
no sweep exhausts — and this direction did not need to exhaust it, because the
answer is **negative** and a `∀` falls to one witness. The figures that *are*
sweeps are disclosed with their denominators in *Caps*: **24** pieces (5 + 19)
for the threshold and the `deg ≥ 2` clause; **451** drawn rows / **260**
bad-flag rows on a **new** constructed population for the scan; **72** rows on
BUNIF's two for the `⟨M⟩` hunt. Every *"none found"* — the scan's `0`
shortfalls, the hunt's `0` both-sides rows, (BE-107)(iii)'s absent `Σ_x` shape —
reads **none found under those caps**, never *"does not exist"*. The claims that
are **not** sweeps are (BE-105)(i) (a trichotomy), (BE-105)(ii)'s `≥` half,
(BE-105)(iv)'s span identity, and (BE-106)(ii) (an exhaustive enumeration with
two controls). And the **asserted-in-driver / proved** distinction the prep
asked for is now paid in the other direction too: (BE-38)(iii)'s clause **was**
asserted in its driver — verified at source — and that was still not enough,
because the assert ran only on flags the sampler drew.

**F12 paid at source.** Five hunks, at the statements rather than only here:
**(BE-38)(iii)** (its third clause annotated FALSE beside its already-corrected
middle clause — and its *"the first and third clauses stand"* sentence, which
(BE-45)(iii) also carries, corrected with it), **(BE-97)(i)** (the clause it
calls *"(BE-38)(iii)'s measured third clause"*), **(BE-101)(i)** and
**(BE-101)(ii)** (the redundancy theorem and its corollary, both repointed to
(PENCIL-SATURATES-GEN) with the pointwise reading priced), and **(BE-103)(i)
item 1** (the residual that named the clause as the arc's next attack).

**F21**: the `(K-bare)` gap-map row is **recomputed to a target with real
headroom** — 1 546 → **1 466** words against the generic cap of **1 600**, i.e.
**134 spare** where BDOUBLE's recompute left 54 — while **absorbing a full
direction and five labels and still coming out shorter than it went in**
(−80 words net, so roughly 225 words of pre-existing prose compressed away
against the ~145 added). No `SPECIAL_CAPS` entry is added and none is needed:
the gate's docstring rule is **no overflow, no bump**, and the row does not
overflow. Label preservation verified by a **scripted set-diff**
(`notes/scripts/gapdiff.py`, shipped with this landing because BDOUBLE's probe
was not retained, with its label regex stated in its own docstring so the count
is reproducible): **130 codes in, 137 out, ZERO dropped** — the seven added are
(BE-104)–(BE-108), (BE-107)(iii) and (PENCIL-SATURATES-GEN).

**Reservation, and what is returned.** Labels **(BE-104)–(BE-108)** and ***Steps
BE103–BE107*** were reserved and are **consumed in full**; nothing is returned.
The driver `w4/bsatur.py` landed at the reserved path. **One** new
configuration-level name is minted, and it is a *condition*, not an object:
**(PENCIL-SATURATES-GEN)**. Nothing is minted for `Π_x`, `c_i(U)`, `ρ_i`, the
(P)/(Z)/(R) traps or the double pencil, per the reservation's constraint;
`Σ_x` and *"the bad plane"* are BUNIF's existing symbol and plain prose
respectively. The section has now gone **six** directions without minting a
configuration-level token.
