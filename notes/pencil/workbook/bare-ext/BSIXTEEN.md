## §(K-bare-ext) — continuation (direction BSIXTEEN, ordinal 111, 2026-09-12): **THE ELEVEN ARE NOT ELEVEN PROBLEMS — but not for the reason a block-sum inheritance lemma would give, and that lemma is FALSE in the dangerous direction.** `c_i` is **superadditive** over block sums (`c_i(A ⊕ B) ≥ c_i(A) + c_i(B)`, strict at 7 120 of 10 000 sampled splittings, with an exhibited exact-ℚ witness at `dim 1`), so a sum can bind where **both** summands are closed; *"close the summands and the sums follow"* is refuted before it is used. What does collapse the eleven is **ONE INSTRUMENT APPLIED SIXTEEN TIMES**: (BE-30)(iv)'s confinement `ρ̄_i ⊆ ⟨P⟩` is **block-agnostic**, so `c_i(U) ≤ dim(⟨P₀⟩ ∩ U)` at **every** configuration for **every** `U`, and the right-hand side is a **closed-form table** `B(m, U) = max(|U ∩ {Π_x, Π_y}|, m + dim U − 6)` in `m = dim ⟨P₀⟩` — a **forced floor** (`ℓ₁ ∈ Π_x`, `ℓ_m ∈ Π_y`, (BE-30)(ii)) or a general-position count, **never anything between**, asserted at 4 480 pointwise cells, 4 200 Klein-pairing cells and 4 256 equality cells on free legal chains and at **13 664 cells on `Chart(H)`** with 0 failures anywhere, and it **reproduces two landed measurements it was not fitted to** ((BE-258)(iii)'s `α_x` histogram and (BE-272)(ii)'s `⟨M⟩` column). **THE VERDICT: two of the eleven — `⟨L⟩` and `⟨M⟩⊕⟨L⟩` — close CAP-FREE by exactly (BE-274)(i)'s two-step, and the other NINE reduce to ONE named candidate law** `(BLOCK-GP)`, under which **all 16 blocks close and `Good ≠ ∅` at rung 3 follows**. `(BLOCK-GP)` is **not** (BE-277)(iii)'s residue: every surviving shape has `dim ⟨P₀⟩ ≤ 5` on **both** sides, i.e. the confinement is **proper** on both, where (BE-277)(iii)/(BE-259)(ii) live at `dim ⟨P₀⟩ = 6`, where it is **vacuous**. **The spec's mechanism is CONFIRMED with its stated reason REFUTED**, and the spec's *"where I expect to be wrong"* sentence is itself **refuted**. **One landed threshold is upgraded**: `Π_x` closes at `dist_i ≤ 5` on both sides, not `dist_i ≤ 4`, by a **direct** argument that does not go through `α_x` — which is what (BE-258)(iii)'s own `0 of 27` rows at `dist = 5` were already reporting. **A scope limit is named that the headline claim needs and the corpus has not stated in one place** (*Steps BE277–BE284*)

### Standing notation (on top of *Steps BE148–BE276*)

BMBLOCK's notation block, **verbatim and including its correction** — `bunif.SUBS`
is every subset of `bunif.BLK`, so the 16 stable `U` **are** the block sums and the
four blocks are their atoms. Read at source (`bunif.BLK` line 131, `bunif.CAP` 132,
`bunif.SUBS` 133–134, `bunif.blocks_of` 196–202, `bunif.profile` 217–226,
`bunif.generic_c` 283–285, `bunif.flag_frame` 183–195):

> **The four blocks, from `bunif.blocks_of`'s body, not from its comment.**
> `'Pix': pencil_space(px, Bx)`, `'Piy': pencil_space(py, By)`,
> `'M': [wedge2(px, py)]`, `'L': [wedge2(e1, e2)]` with `⟨e1, e2⟩ = π_x ∩ π_y`
> (`bunif.flag_frame` via `bimage.plane_meet`). The function **asserts**
> `dim(Pix + Piy + M + L) == 6` — *"the four blocks do not sum DIRECTLY to the
> screw space"* — and **that assert is the fact that makes the 16 subsets the 16
> stable `U`**, so every statement below about `U_S := ⊕_{b ∈ S} B_b` is a
> statement about a **direct** sum.
>
> **`f(S) := |S ∩ {Π_x, Π_y}|`**, the **forced floor**. **`d_S := dim U_S =
> Σ_{b∈S} CAP[b]`**. **`m_i := dim ⟨P₀⟩`** for a shortest x–y path `P₀` of side
> `i` — *the dimension, not the edge count*; `m_i ≤ min(dist_i, 6)` always, and
> every bound below is stated in `m_i` and then **weakened** to
> `min(dist_i, 6)` when the arithmetic needs a combinatorial input. That
> direction is the safe one: `B` is monotone increasing in `m`, so
> `B(m_i, S) ≤ B(min(dist_i, 6), S)`, and **no hypothesis is dropped by the
> substitution**. (This is the one place a `dim ⟨P₀⟩ < dist_i` degeneration
> could have bitten, and it does not.)
>
> **`B(m, S) := max(f(S), m + d_S − 6)`** — THE TABLE. **`(NO-END-ON-L)`**: the
> interior path vertices adjacent to a terminal are not on `L = π_x ∩ π_y`.
>
> **THE KLEIN PAIRING PAIRS THE BLOCKS OFF, and this is used below.** In the
> frame `(p_x, e₁, e₂, p_y)` the pairing `⟨ω, η⟩ = ω ∧ η` sends `Π_x ↔ Π_y` and
> `⟨M⟩ ↔ ⟨L⟩`; each block is totally singular. Hence
> **`U_S^⊥ = U_{(τS)^c}`** with `τ` the involution swapping `Π_x ↔ Π_y`,
> `⟨M⟩ ↔ ⟨L⟩`. Two identifications fall out and both are used: **`α_x = Π_x ⊕
> ⟨M⟩`** (the (BE-258) operator's kernel **is** a block sum of this family, at
> `d = 3`) and **`Λ²π_x = Π_x ⊕ ⟨L⟩`** (a maximal totally singular 3-space, so
> Klein-self-perp).

---

### *Step BE277* — **(BE-278): the two block-sum lemmas, both directions — and the one the spec hoped for is the FALSE one**

**(BE-278)(i)** `[PROVED]` — **THE TRACE LEMMA.** *For sub-sums `U_{S'} ⊆ U_S`,*
> `c_i(U_S) ≤ c_i(U_{S'}) + (d_S − d_{S'})`,
*equivalently: the deficiency `e_i(S) := d_S − c_i(U_S)` is **monotone increasing**
in `S`.* **Proof.** Projection of `ρ̄_i ∩ U_S` along `U_{S'}` onto
`U_S / U_{S'} ≅ U_{S∖S'}` has kernel exactly `ρ̄_i ∩ U_{S'}`, so
`c_i(U_S) − c_i(U_{S'}) ≤ dim U_{S∖S'} = d_S − d_{S'}`. ∎ Asserted at **16 200**
`(subspace, U' ⊆ U)` pairs — random `W ⊆ Λ²K⁴` of every dimension `1…5` against a
freshly drawn generic-regime flag — **0 failures** (`bsixteen.py trace`, seed
`20260912`, exact ℚ).

**(BE-278)(ii)** `[REFUTED]` — **THE INHERITANCE LEMMA THE SPEC HOPED FOR IS FALSE,
and false in the direction that matters.** *`c_i` is **superadditive**:
`c_i(A ⊕ B) ≥ c_i(A) + c_i(B)`, and the inequality is strict on a nonempty open.*
Asserted at **10 000** splittings with **0** failures and **strict at 7 120** of
them. **THE WITNESS, exact over ℚ, in the standard frame
`(p_x, e₁, e₂, p_y) = (e₀, e₁, e₂, e₃)`:** `W = ⟨(p_x ∧ p_y) + (e₁ ∧ e₂)⟩`, of
dimension `1`, has `c(⟨M⟩) = 0`, `c(⟨L⟩) = 0` and **`c(⟨M⟩ ⊕ ⟨L⟩) = 1`**. So both
summands are closed at `W` and the sum is not. **Consequence, stated before
anything is built:** *"(BE-97)(iii) reports the margin reaching `0` only at four
blocks, so the sums may inherit their closures from the summands"* — the spec's
own **highest-yield** sentence — is **refuted as a route**. A closure of `Π_x` and
of `⟨M⟩` says **nothing** about `Π_x ⊕ ⟨M⟩`; the trace lemma (i) runs the other
way and gives only `margin(U_S) ≤ margin(U_{S'}) + (d_S − d_{S'})`, which is never
a closure.

**(BE-278)(iii)** `[PROVED]` — **THE BLOCK PATH BOUND — the instrument that
replaces it, and it costs nothing new.** *For every stable `U`, every x–y path `P`
of side `i`, and **at every configuration**,*
> `c_i(U) = dim(ρ̄_i ∩ U) ≤ dim(⟨P⟩ ∩ U)`.
**Proof.** (BE-30)(iv) gives `ρ̄_i ⊆ ⟨P⟩` **pointwise**; intersect with `U`. ∎
**This is (BE-272)(i) with `⟨M⟩` deleted from the statement.** BMBLOCK read
(BE-30)(iv) at `⟨M⟩` and noted that *"`⟨M⟩` is a single line and the bound is
already the whole statement"*; what is being recorded here is that **the
confinement never mentioned `⟨M⟩` at all** — it is a statement about `ρ̄_i`, so it
bounds `c_i(U)` at **all sixteen** `U` with no new input. **The dispatch spec's
caution is therefore itself imprecise and the correction is load-bearing:** the
spec wrote that *"(BE-30)(iv) confines `ρ̄_i` to `⟨P⟩` **because of that
identification**"* of `⟨M⟩` with the virtual edge's hinge line, and warned that
*"`⟨L⟩` has no such identification, so the confinement that did all the work may
simply not apply."* (BE-30)(iv) is *"for **every** `u–v` path `P` of a piece `H`,
`ρ̄_{uv}(H) ⊆ ⟨ℓ_e : e ∈ P⟩`"*, quoted with its hypotheses — **no block appears
in it**. Had this direction inherited the spec's reading it would have looked for
a second instrument at `⟨L⟩` and found none.

---

### *Step BE278* — **(BE-279): THE TABLE — sixteen columns of one confinement, and it reproduces two landed histograms it was not fitted to**

**(BE-279)(i)** `[PROVED]` — **the pointwise floor.** *At every legal
configuration, `dim(⟨P⟩ ∩ U_S) ≥ B(dim ⟨P⟩, S)`.* **Proof.** Two lower bounds,
and the max of two lower bounds is one. **(a)** `dim(A ∩ B) ≥ dim A + dim B − 6`
gives `≥ m + d_S − 6`. **(b)** By (BE-30)(ii) the pencil condition at `x` puts
`closedNbhd(x) ⊆ π_x`, so `p_1 ∈ π_x` and `ℓ₁ = p_x ∧ p_1 ∈ Π_x`; likewise
`ℓ_m ∈ Π_y`; and `ℓ₁ ≠ ℓ_m` for `m ≥ 2` (at `m = 2` because `p_x, p_1, p_y` are
not collinear — the carrier's own hinge-coincidence gate). So `⟨P⟩ ∩ U_S` contains
`f(S)` independent lines. ∎ Asserted at **4 480** `(draw, U)` cells, **0
failures** (`bsixteen.py table`, seed `20260912`, exact ℚ, 40 legal chains per
`m = 2…8`, `dim ⟨P⟩ = min(m, 6)` at 280 of 280).

**(BE-279)(ii)** `[PROVED]` / `[MEASURED]` — **the equality, and it is ONE
determinantal condition, not a list of special cases.** Since
`⟨P⟩ = (⟨P⟩^⊥)^⊥` under the Klein pairing,
> `dim(⟨P⟩ ∩ U_S) = d_S − rank K(⟨P⟩^⊥, U_S)`,
**asserted at all 4 200 cells with nonzero `U`, 0 failures.** And
`rank K(⟨P⟩^⊥, U_S) ≤ min(6 − m, d_S − f(S))` **always** — `⟨P⟩^⊥` annihilates
the `f(S)` forced end lines and has only `6 − m` dimensions to spend — with
equality **iff** `dim(⟨P⟩ ∩ U_S) = B(m, S)`. **So the table is exactly the
statement that one Klein pairing has maximal rank**, an open condition per
`(m, U)`. Asserted at **4 256 of 4 256** cells off the named loci, **0
failures**, over 280 draws of which **14** sit on a named locus. The certificates, per
`m`, via the identity `dim(⟨P⟩ ∩ U) = dim U − rank K(⟨P⟩^⊥, U)` (`K` the Klein
pairing) — so **one decomposable `η`, a line meeting every path edge, kills one
unit at every block it does not annihilate**, and for a decomposable `η` the
pattern is read off the geometry (`⟨η, Π_x⟩ = 0` iff `η ∋ p_x` or `η ⊆ π_x`;
`⟨η, ⟨M⟩⟩ = 0` iff `η` meets `M`; `⟨η, ⟨L⟩⟩ = 0` iff `η` meets `L`):

| `m` | certificate | status |
|---|---|---|
| `2` | `⟨P⟩ ⊆ Π_x ⊕ Π_y` **identically** (both hinge lines are end lines), so the whole column is `f(S)`. The transversal `η = p_0 ∧ p_2 = M` separates `⟨L⟩` alone, **30/30**, and is skew to `L` by the **generic flag regime itself** (`rank[p_x, e₁, e₂, p_y] = 4`) | **POINTWISE**, no extra hypothesis |
| `3` | `η = p_1 ∧ p_2`, decomposable **30/30**, annihilates every hinge line **30/30**, separates all four blocks at **28/30** | **POINTWISE** under a named spanning condition |
| `4` | `η = p_1 ∧ p_3`, decomposable **30/30**, annihilates every hinge line **30/30**, separates all four blocks at **28/30** | **POINTWISE** under a named spanning condition |
| `5` | the Klein annihilator of `⟨P⟩` is **1-dimensional** and **decomposable at 0 of 30** — so the functional is genuinely **not** a transversal line, exactly as at `⟨M⟩` ((BE-272)(ii)) — and separates all four blocks at **30/30** | **GENERIC**, open condition, exact-ℚ witness |
| `≥ 6` | `⟨P⟩ = Λ²K⁴`; the confinement is **vacuous** and `B = d_S` | identity |

**(BE-279)(iii)** `[MEASURED]` — **the two jump loci, BOTH found by the driver's
own assert and neither assumed — and the second one is (BE-272)(ii)'s own
condition, reproduced from the other side.** The equality claim was written
first and **crashed twice**.

* **`endL` = (NO-END-ON-L).** First crash: `dim(⟨P⟩ ∩ Λ²π_x) = 2` against a
  predicted `1` at `m = 3`. The cause is exact: `p_1 ∈ L` means `p_1 ∈ π_y`, so
  `ℓ₂ = p_1 ∧ p_2` with `p_2 ∈ π_y` lies in `Λ²π_y = Π_y ⊕ ⟨L⟩`. At the committed cap this moves **15 cells** across the locus draws, and
  **only five distinct cells**, all containing `⟨L⟩` **and** an end block:
  `L+Pix` (×3), `L+M+Pix` (×3), `L+Piy` (×2), `L+M+Piy` (×2) at `1 → 2` and
  `L+Pix+Piy` (×5) at `2 → 3`. **Forced only at `m = 2`**,
  where `p_1` is adjacent to both terminals — and the `m = 2` column is
  **unaffected**, for the reason in the table above.
* **`span`.** Second crash, on the **reduced** `validate` cap, which the full
  run had not reached: `dim(⟨P⟩ ∩ ⟨M⟩) = 1` against `0` at `m = 3`. This is
  **(BE-272)(ii)'s own hypothesis** — that clause's `m = 3` row is *"`0`
  whenever `p_0, p_3, p_1, p_2` **span** `K⁴`"* — arrived at here from the
  opposite direction, by a failure rather than by a proof. The cells it moves
  are exactly those containing `⟨M⟩`: `M`, `M+Pix`, `M+Piy`, `L+M`, `L+M+Pix`,
  `L+M+Piy`, `M+Pix+Piy`.

**The two loci are disjoint in effect** — `endL` moves the `⟨L⟩`-plus-end cells,
`span` moves the `⟨M⟩` cells — and each is a **proper closed condition**. **This
is the F31/F32 direction, checked rather than quoted:**
`dim(⟨P⟩ ∩ U)` is **upper** semicontinuous, so the generic value is the
**minimum** and a special point can only make it **larger**; the criterion
(BE-96)(iv) is stated at the **generic** `c_i(U)`, so the jump does not host a
violation — it weakens a bound.

**(BE-279)(iv)** `[MEASURED]` — **the table, and two landed histograms it
reproduces without having been fitted to either.**

| `U` | `d` | `f` | `m=2` | `3` | `4` | `5` | `6` | `7` | `8` |
|---|---|---|---|---|---|---|---|---|---|
| `0` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `Π_x` | 2 | 1 | 1 | 1 | 1 | 1 | 2 | 2 | 2 |
| `⟨M⟩` | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 1 |
| `⟨L⟩` | 1 | 0 | 0 | 0 | 0 | 0 | 1 | 1 | 1 |
| `Π_y` | 2 | 1 | 1 | 1 | 1 | 1 | 2 | 2 | 2 |
| `Π_x⊕⟨M⟩ = α_x` | 3 | 1 | 1 | 1 | 1 | 2 | 3 | 3 | 3 |
| `Π_x⊕⟨L⟩ = Λ²π_x` | 3 | 1 | 1 | 1 | 1 | 2 | 3 | 3 | 3 |
| `Π_x⊕Π_y` | 4 | 2 | 2 | 2 | 2 | 3 | 4 | 4 | 4 |
| `⟨M⟩⊕⟨L⟩` | 2 | 0 | 0 | 0 | 0 | 1 | 2 | 2 | 2 |
| `⟨M⟩⊕Π_y = α_y` | 3 | 1 | 1 | 1 | 1 | 2 | 3 | 3 | 3 |
| `⟨L⟩⊕Π_y = Λ²π_y` | 3 | 1 | 1 | 1 | 1 | 2 | 3 | 3 | 3 |
| `Π_x⊕⟨M⟩⊕⟨L⟩` | 4 | 1 | 1 | 1 | 2 | 3 | 4 | 4 | 4 |
| `Π_x⊕⟨M⟩⊕Π_y = ⟨L⟩^⊥` | 5 | 2 | 2 | 2 | 3 | 4 | 5 | 5 | 5 |
| `Π_x⊕⟨L⟩⊕Π_y = ⟨M⟩^⊥` | 5 | 2 | 2 | 2 | 3 | 4 | 5 | 5 | 5 |
| `⟨M⟩⊕⟨L⟩⊕Π_y` | 4 | 1 | 1 | 1 | 2 | 3 | 4 | 4 | 4 |
| `Λ²K⁴` | 6 | 2 | 2 | 3 | 4 | 5 | 6 | 6 | 6 |

**CROSS-CHECK 1, and it is a genuine one — a different population, a different
driver, a different direction.** The `α_x` row reads `(m, B) = (2,1), (3,1),
(4,1), (5,2), (6,3), (7,3)`. (BE-258)(iii)'s **427-row** `Chart(H)` census of
`dim(⟨P₀⟩ ∩ α_x)` reads `{(2,1): 203, (3,1): 103, (4,1): 58, (5,2): 22, (6,3):
23, (7,3): 18}` — **the same six cells**, including the `dist = 7 → 3`
saturation that clause records as a correction to its own display formula. Here
that saturation is not a special case but the `min(m, 6)` inside `B`.
**CROSS-CHECK 2.** The `⟨M⟩` row is `0` for `2 ≤ m ≤ 5` and `1` for `m ≥ 6` —
(BE-272)(ii)'s path lemma verbatim, now as the `d = 1, f = 0` row of a table.

**(BE-279)(v)** `[PROVED]` — **`Π_x` CLOSES AT `dist_i ≤ 5`, NOT `dist_i ≤ 4` — a
landed threshold upgraded, by deleting a detour rather than adding an argument.**
(BE-258)(i) bounds `c_i(Π_x)` through `Π_x ⊆ α_x` and gets
`max(1, dim ⟨P₀⟩ − 3)`, hence `≤ 1` only at `dist_i ≤ 4`. But **`Π_x` itself is
a block of this family**, and its row is `1` for every `m ≤ 5`: the `α_x` detour
costs exactly the one unit `(BE-258)(iii)` had to recover by measurement, since
`dim(⟨P₀⟩ ∩ Π_x) = 2` needs `Π_x ⊆ ⟨P₀⟩`, which at `m = 5` is the annihilator of
`⟨P₀⟩` lying in `Π_x^⊥ = Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩` — a proper closed condition with an
exhibited witness. **Therefore: if BOTH sides have `dist_i ≤ 5` then generic
`c₁(Π_x) + c₂(Π_x) ≤ 2 = dim Π_x` and `Π_x` cannot bind**, which is
(BE-259)(i)'s statement with `4` replaced by `5`. (BE-258)(iii) already
**reported** this — *"`c_i(Π_x) = 2` occurs at 0 rows with `dist_i ≤ 5`, the 27
rows at `dist_i = 5` included, where the α-bound would allow `2`"* — and
attributed it to *"the second kernel vector must additionally lie in `Λ²π_x`, one
further condition"*. That is the same fact; what is added here is that it is the
**generic** value of a table cell with a certificate, not a residual observation.
The same at `Π_y`. **Status honesty:** at `m ≤ 4` this is pointwise under the
named spanning conditions; at `m = 5` it is generic with a witness — one notch
weaker than (BE-259)(i)'s `dist_i ≤ 4` half, which uses no draw at all. **It does
not supersede (BE-259)(i); it extends it by one, at one notch lower status.**

---

### *Step BE279* — **(BE-280): the rung-3 arithmetic at all sixteen blocks, cap-free — and the answer is 2 + 9**

**(BE-280)(i)** `[PROVED]` (exhaustion) — **the enumeration.** `bsixteen.py
arith`, **seedless, no sampling, 0.1 s**. Enumerate every
`(δ₁, δ₂, dist₁, dist₂, ρ₁, ρ₂)` the landed constraints allow — **5 392** tuples
— and every `(c₁, c₂)` on top, under

| law | statement | status |
|---|---|---|
| L0 | `δ₁ + δ₂ ≤ 6` | **rung 3**, (BE-225)(iii) |
| L1 | `ρ_i ≤ δ_i` | (BE-22)(ii) at `a_i = 0` |
| L2 | `ρ_i ≤ dist_i` | (BE-256)(ii), **pointwise** |
| L2b | `δ_i ≤ dist_i` | (BE-256)(i), **combinatorial** |
| L3 | `c_i(U) ≤ min(ρ_i, d_S)` | trivial |
| L4 | `dist_i ≥ 2` | the region, `x ≁ y`, (BE-272)(iii) |
| LP | `c_i(U) ≤ B(min(dist_i, 6), S)` | **THE TABLE**, (BE-279) |
| L6 | `dist_i ≥ 6 ⟹ c_i(U) = max(0, ρ_i + d_S − 6)` | general position once the confinement is **vacuous** — the (BE-277)(iii) / (BE-259)(ii) residue; **MEASURED** at `⟨M⟩` ((BE-273)(ii)) and at `Π_x` ((BE-258)(iv)), **unmeasured at the other 14** |
| LG | `c_i(U) ≤ max(f(S), ρ_i + B(min(dist_i,6), S) − min(dist_i,6))` | **(BLOCK-GP)** — the forced floor **or** the general-position count inside `⟨P₀⟩`, never anything between. A **NAMED CANDIDATE** |

A violation at `U` is `c₁(U) + c₂(U) ≥ d_S + 1`, `slack = 0` being rung 3.
Survivor counts, block by block:

| `U` | `d` | L0–L4 | +LP | +L6 | +LG |
|---|---|---|---|---|---|
| `Π_x` | 2 | 2 224 | 832 | **0** | 0 |
| `⟨M⟩` | 1 | 1 845 | 280 | **0** | 0 |
| **`⟨L⟩`** | 1 | 1 845 | 280 | **0** | 0 |
| `Π_y` | 2 | 2 224 | 832 | **0** | 0 |
| `α_x` | 3 | 1 407 | 547 | 15 | **0** |
| `Λ²π_x` | 3 | 1 407 | 547 | 15 | **0** |
| `Π_x⊕Π_y` | 4 | 545 | 321 | 37 | **0** |
| **`⟨M⟩⊕⟨L⟩`** | 2 | 2 224 | 480 | **0** | 0 |
| `α_y` | 3 | 1 407 | 547 | 15 | **0** |
| `Λ²π_y` | 3 | 1 407 | 547 | 15 | **0** |
| `Π_x⊕⟨M⟩⊕⟨L⟩` | 4 | 545 | 265 | 21 | **0** |
| `⟨L⟩^⊥` | 5 | 109 | 76 | 12 | **0** |
| `⟨M⟩^⊥` | 5 | 109 | 76 | 12 | **0** |
| `⟨M⟩⊕⟨L⟩⊕Π_y` | 4 | 545 | 265 | 21 | **0** |

**(BE-280)(ii)** `[PROVED]` — **TWO OF THE ELEVEN CLOSE BY EXACTLY (BE-274)(i)'s
TWO-STEP, cap-free.**

* **`⟨L⟩`.** Every `+LP` survivor has `min(m₁, m₂) = 6`, i.e. `dist_i ≥ 6` on
  **both** sides — so the table alone closes `⟨L⟩` whenever **either** side has
  `2 ≤ dist_i ≤ 5`, the same one-sided shape (BE-272)(iii) has at `⟨M⟩` and
  strictly stronger than (BE-259)(i)'s two-sided one. In the corner, **the
  derivation, since a kill naming a number carries it**: `c_i(⟨L⟩) = 1` at
  `dist_i ≥ 6` forces `ρ_i = 6` (L6); with L1 and `δ_i ≤ 6` ((BE-21)(ii)) that
  forces `δ_i = 6`; on **both** sides `Σδ = 12 > 6`, contradicting L0. **So at
  rung 3 the `⟨L⟩` block cannot bind** — and the `⟨M⟩`/`⟨L⟩` columns of the
  table are **identical**, which is the whole of why the transport works.
* **`⟨M⟩ ⊕ ⟨L⟩`.** `+LP` survivors have `min(m₁, m₂) ≥ 5`, so the table alone
  closes it whenever **either** side has `dist_i ≤ 4`; and at `(5,5)` the table
  gives `c_i ≤ 1` each, sum `≤ 2 = d`, so that corner is closed too. The
  survivors are `(5,6), (6,5), (6,6)`, where `(c₁,c₂) = (1,2)` (or its mirror)
  needs `ρ₂ = 6` by L6, hence `δ₂ = 6`, hence `δ₁ = 0`, hence `ρ₁ = 0` and
  `c₁ = 0` — the collapse (BE-22)(vi) names. **Cap-free, 0 survivors.**

**These two closures are CONDITIONAL on L6**, which is (BE-277)(iii)'s residue and
belongs to direction BPROPCL. **This direction does not attempt it.** Their
**unconditional** content is the proved half: `⟨L⟩` closed whenever either side
has `dist_i ≤ 5`, `⟨M⟩⊕⟨L⟩` whenever either side has `dist_i ≤ 4` or both have
`dist_i ≤ 5`.

**(BE-280)(iii)** `[UNTAGGED]` — **THE NINE, and why the table cannot finish
them.** Every remaining open block **contains `Π_x` or `Π_y`**, hence has
`f(S) ≥ 1`, hence its table row never drops below `1` at any `m`. That is not an
accident of the count: `ℓ₁ ∈ Π_x` **pointwise**, so the path instrument can never
exclude an end block, and `B(m, S) ≥ 1` caps nothing once `d_S ≥ 2`. **The three
blocks the table closes outright are exactly the three with `f(S) = 0`** —
`⟨M⟩`, `⟨L⟩`, `⟨M⟩⊕⟨L⟩`, the sums of the two 1-dimensional *interior* blocks. **A
sharp statement of the instrument's reach, not a lament:** the path confinement
sees the flag only through its two end pencils, and those are precisely where it
is blind.

**(BE-280)(iv)** `[PROVED]` (exhaustion) — **THE RESIDUE IS NOT (BE-277)(iii)'s,
and the derivation is printed rather than summarized.** The `+L6` survivors reduce
to **40 distinct shapes** `((m₁,m₂), (c₁,c₂), (ρ₁,ρ₂))`. **Every one has
`m_i ≤ 5` on BOTH sides** — `39` of the `40` have a side at `m_i = 5` and the
remaining one is `(m₁,m₂) = (4,4)`, `(c₁,c₂) = (3,3)`, `(ρ₁,ρ₂) = (3,3)` at
`⟨L⟩^⊥` and `⟨M⟩^⊥`. So the whole residue sits where the path confinement is
**proper on both sides**, whereas (BE-277)(iii) and (BE-259)(ii) are the corner
where it is **vacuous** (`dim ⟨P₀⟩ = 6`). **The two residues are disjoint**, and
a proof of BPROPCL's would leave this one standing — which is the useful thing
to know before the next round is scoped.

---

### *Step BE280* — **(BE-281): (BLOCK-GP), the one law the nine reduce to — stated so it can be attacked, and with its OWN refutation already inside it**

**(BE-281)(i)** `[UNTAGGED]` — **the statement.** *At an internal R-node peel at
rung 3 in the generic flag regime, for every stable `U` and each side `i`,*
> **(BLOCK-GP)**  `generic c_i(U) ≤ max( f(U), ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩ )`.
*i.e. `ρ̄_i` meets `U` either in the lines the flag forces, or in general position
**inside** `⟨P₀⟩` — never in more.* Under it **all sixteen blocks close at rung
3** and therefore, by (BE-96)(iv), **`Good ≠ ∅` at every such peel**.

**(BE-281)(ii)** `[UNTAGGED]` — **why the forced floor is in the statement, and
the stronger version WITHOUT it is REFUTED by a landed lemma.** The natural first
guess is the equality `c_i(U) = max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)` — pure
general position inside `⟨P₀⟩`, with no floor. **It is false, and (BE-45)(i)
refutes it with no measurement:** at a **series end** at `x` (every x–y path of
side `i` leaves `x` by the same edge `e`, so `e` is a bridge) that clause gives
`⟨ℓ_e⟩ ⊆ ρ̄_i ∩ Π_x` **at every configuration**, so `c_i(Π_x) ≥ 1` with no
general-position content whatsoever; the equality predicts `0` whenever
`ρ_i < dim ⟨P₀⟩ − dim(⟨P₀⟩ ∩ Π_x)`. **A series end is compatible with the
region**: `x ≁ y` and side-degree `≥ 2` do not forbid `x` from having its other
side-`i` neighbours inside the bridge's near component. **(BE-45)(ii)'s second
mechanism is, by contrast, CONSISTENT with the law**: path saturation
`δ_i = d_min` gives `ρ̄_i = ⟨P₀⟩` **as spaces**, hence `ρ_i = dim ⟨P₀⟩` and
`c_i(U) = dim(⟨P₀⟩ ∩ U)`, which is exactly what the general-position term returns
there. **So (BE-45)'s dichotomy does not attack (BLOCK-GP); it explains its two
terms** — (M1) is the floor, (M2) is the saturated end of the count. The
arithmetic above is run at the floored form **and closes all sixteen**, so nothing
below rests on the refuted version. *This is the clause this direction is least
sure of, and it is stated in the weakest form that still closes the arithmetic,
deliberately.*

**(BE-281)(iii)** `[UNTAGGED]` — **what (BLOCK-GP) is NOT, and who owns what.** It
is **not** BPROPCL's lemma: (BE-277)(iii) / (BE-259)(ii) ask for
`U ⊆ ρ̄_i` to be a **proper closed condition at `ρ_i ≤ 5` once `dim ⟨P₀⟩ = 6`*,
and every shape (BLOCK-GP) has to kill has `dim ⟨P₀⟩ ≤ 5` on both sides
((BE-280)(iv)). The two are **the same shape one regime apart**, and the
honest way to put it is: BPROPCL's lemma is the `dim ⟨P₀⟩ = 6` instance of
(BLOCK-GP), and this direction's nine blocks need the `dim ⟨P₀⟩ ∈ {4, 5}`
instances. **A single lemma stated relative to `⟨P₀⟩` rather than to `Λ²K⁴` would
discharge both**, and that — not two lemmas — is what this direction hands
forward. *Stated as a direction's question; the two dispatches are complementary
and not duplicative, exactly as the spec's division intends.*

> **— TESTED 2026-09-12 by (BE-295) (direction BPROPCL), and it is the round's
> cross-return item.** That direction's headline through six steps was *"the two
> residues are NOT one question"*. This clause landed **mid-run**, proposing the
> repair — state the lemma **relative to `⟨P₀⟩`** — and BPROPCL **tested it rather
> than argued against it**: `c_i(U) = max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)`,
> asserted at **1 281/1 281** draws, both blocks, 0 exceptions. **So
> (BE-277)(iii)'s *"a single lemma would discharge both"* is REFUTED in its own
> frame and CONFIRMED in this one**, and two directions each told not to attempt
> the other's lemma converged on one from opposite ends of the `dim ⟨P₀⟩` axis.
> BPROPCL reached it by **diffing against `HEAD` rather than against its dispatch
> baseline**, which is the concurrency discipline working as intended.

---

### *Step BE281* — **(BE-282): THE CARRIER READING — the table holds on `Chart(H)` at 13 664 cells, and the law's 100 % is a CAP, not a confirmation**

**(BE-282)(i)** `[MEASURED]` — `bsixteen.py side`, **368.7 s**, seed
`20260912`, exact ℚ, **427 side rows**, **854 generic-regime draws**, **13 664
`(draw, U)` cells**. *(**Denominator disclosure, added 2026-09-12 by (BE-293)
(direction BPROPCL): the 427 rows are **400 DISTINCT sides** — `side_library`
and `side1_library` share **27** shapes, 26 of them at `dist ≤ 5` and exactly
1 at `dist ≥ 6`. So "427 side rows" over-reads distinct shapes by 27; no cell
count or verdict here moves, because every assertion is per row.)* Asserted at every cell, **0 failures**:

* **the block path bound** `c_i(U) ≤ dim(⟨P₀⟩ ∩ U)` ((BE-278)(iii)) — the
  pointwise instrument, now on the carrier rather than on free legal chains;
* **the table floor** `dim(⟨P₀⟩ ∩ U) ≥ B(dim ⟨P₀⟩, U)` ((BE-279)(i));
* **(BE-30)(iv) itself** at the shortest path (`dim(ρ̄_i ∩ ⟨P₀⟩) = ρ_i`).

And the **equality** `dim(⟨P₀⟩ ∩ U) = B(dim ⟨P₀⟩, U)` holds at **13 664 of
13 664** — i.e. **(NO-END-ON-L) is not violated at a single drawn configuration
of this population**, so the jump locus (BE-279)(iii) found on free chains is
not realized by any side the library builds.

**CAPS, and they travel with every figure above:** `ndraw = 2` per side — the
landed `bgoodempty.run_pix` value is **3**, and this is **fenced to 2** and named
here rather than in a footnote; `maxarc = 8`, `maxtheta = 7`,
`xy_paths(cap = 400, maxlen = 9)` are `run_pix`'s **committed** values, restored
and stated; **one** shortest path per side, not all of them (sound — `ρ̄_i` is
confined by **every** x–y path, so using one is an upper bound and not sharp).

**THE 427 IS A SAME-INPUT REPRODUCTION, not a cross-check.** It is
(BE-258)(iii)'s own denominator, and for the reason (BE-277)(vi) item 6 gives:
`bsixteen.SEED`, `bmblock.SEED` and `bgoodempty.SEED` are the **same integer** and
`side_library` is seeded, so this mode reads the **identical** library. It buys
**comparability of the columns** — the `α_x` column here agrees with
(BE-258)(iii)'s `c(Π_x)` cell-for-cell at `dist ∈ {2,3,4}` (`190/13`, `91/12`,
`49/9`), where the table makes the two coincide, and diverges at `dist = 5`
exactly where the table says `α_x` allows `2` and `Π_x` does not. It buys
**nothing about independence**.

**(BE-282)(ii)** `[MEASURED]` — **`⟨L⟩` on the carrier, and L6 at all sixteen
blocks for the first time.** Generic `c_i(⟨L⟩)` by `dist_i`:
`{(2,0): 203, (3,0): 103, (4,0): 58, (5,0): 22, (6,0): 16, (6,1): 7, (7,1): 18}`.
So **`c_i(⟨L⟩) = 0` at all 386 rows with `dist_i ≤ 5`** and `= 1` at **25 of the
41** rows with `dist_i ≥ 6` — the `⟨M⟩` shape of (BE-273), one letter changed,
and the measured confirmation of (BE-280)(ii)'s proved half. The unfloored law
L7 `c_i(U) = max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)` holds at **13 664 of
13 664** cells; **at `dim ⟨P₀⟩ = 6` that reads `c_i(U) = max(0, ρ_i + d_U − 6)`,
which IS L6** — so **L6 is now measured at all sixteen blocks on this
population**, where it was measured only at `⟨M⟩` ((BE-273)(ii)) and at `Π_x`
((BE-258)(iv)). *It is still a measurement, and the residue it names is still
BPROPCL's.*

**(BE-282)(iii)** `[MEASURED]` — **THE 100 % IS A CAP, AND THE DRIVER PROVES IT
IS.** A law holding at 13 664 of 13 664 cells is exactly the shape that invites a
false confirmation, so the question *can this population refute it?* was asked
with its own mode. `bsixteen.py mech`, **draw-free, 0.0 s**: over the **428**
sides of the library, the number of **distinct first edges** of the x–y paths at
each terminal is `(#at x, #at y) ∈ {(2,2): 94, (3,3): 96, (4,4): 112, (5,5): 126}`
— **never `1`, at either terminal, at any side**. So **(BE-45)(i)'s series end
(M1) fires at ZERO sides of this library**, and (M1) is the one landed mechanism
that refutes the unfloored law ((BE-281)(ii)). **Therefore the 100 % is evidence
about the library's shape — cycles, generalized thetas and ladders, all with two
path-disjoint first edges at each terminal — and not evidence that the unfloored
law holds.** The closure is run at the **floored** form (BLOCK-GP), which
survives a series end, and both forms close all sixteen blocks
((BE-280)(i)), so nothing depends on the distinction. **NOT FOUND UNDER CAP C.**

**(BE-282)(iv)** `[UNTAGGED]` — **the `0` off-regime rejections are not evidence
either.** `bunif.flag_frame` rejected **0 of 854** draws. That is **not** a
finding that the generic flag regime always holds: these are **one-sided library
rows**, where `π_x` and `π_y` are drawn independently by
`bdecor.sample_by_branches` and nothing can force them equal. The forced
coincidence (BE-81) exhibits is a property of the **composite** two-sided peel,
which this mode does not build. **This is (BE-284)(ii)'s scope limit showing up as
a sampling fact**, and it is recorded here so the `0` is not later read as
covering it.

---

### *Step BE282* — **(BE-283): the residue's population, priced WITHOUT A SINGLE DRAW**

**(BE-283)(i)** `[MEASURED]` — `bsixteen.py pop`, **~6 s, no configuration
drawn**. `(dist_i, δ_i)` at an internal R-node peel is **combinatorial**, so which
blocks' corners are reachable in-region is graph theory. Replays
`bgoodempty.run_block`'s job list at its **committed** defaults through the same
region gates as `bmblock.run_reach`: **2 946** in-region peels of **4 752** jobs
offered, with `δ_i ≤ dist_i` ((BE-256)(ii)) re-verified at all of them.

| `U` | `d` | +LP | +L6 | +LG |
|---|---|---|---|---|
| `Π_x` / `Π_y` | 2 | 834 | **0** | 0 |
| `⟨M⟩` / `⟨L⟩` | 1 | 248 | **0** | 0 |
| `α_x` / `Λ²π_x` / `α_y` / `Λ²π_y` | 3 | 743 | 17 | **0** |
| `Π_x⊕Π_y` | 4 | 727 | 79 | **0** |
| `⟨M⟩⊕⟨L⟩` | 2 | 433 | **0** | 0 |
| `Π_x⊕⟨M⟩⊕⟨L⟩` / `⟨M⟩⊕⟨L⟩⊕Π_y` | 4 | 599 | 42 | **0** |
| `⟨L⟩^⊥` / `⟨M⟩^⊥` | 5 | 348 | 47 | **0** |

**CAP, and it travels:** that job list — two skeletons, branch lengths `≤ 5`, the
non-adjacent hub pairs, a 66-shape side-1 library, no `njob` truncation, no
`quick`. **NOT FOUND UNDER CAP C, never "does not exist".**

**(BE-283)(ii)** `[UNTAGGED]` — **the cross-check, and its honest standing.**
`⟨M⟩`'s `+LP` figure is **248 of 2 946**, which is (BE-276)(i)'s own number,
reached here by a **different route** (the table's `min(m_i) = 6` corner rather
than a `dist ≤ 5` threshold) but from the **same job list**. **That is a
same-input reproduction**: it buys comparability of the columns and confirms the
table reproduces BMBLOCK's threshold, and it buys **nothing about independence**.
The arc's own 2026-09-12 cross-return finding is what makes saying so
mandatory.

**(BE-283)(iii)** `[UNTAGGED]` — **the population figures are per-block corners,
not per-block failures.** A `+LP` entry of `743` does **not** say `743` peels
have a violation; it says the table alone does not exclude one there. Every one
of them is excluded by `+LG`, and `17` of them are still alive after `+L6`. The
`+L6` column is the honest size of what (BLOCK-GP) has to do **beyond** what
BPROPCL's lemma would do: **17 to 79 peels per block, of 2 946**.

---

### *Step BE283* — **(BE-284): the F26 consumer check — the POSITIVE arm, and it HAS a consumer, with one scope limit the corpus has not stated in one place**

**(BE-284)(i)** `[UNTAGGED]` — **the positive arm is consumed, and it is the
arc's actual target rather than an elimination.** The chain, read at the owning
sections rather than off a summary: `Good(H; x,y) ≠ ∅` **is** (BE-67)(iii) at that
peel ((BE-69)(ii), *"(BE-67)(iii) at `H` is exactly `Good ≠ ∅`"*); (BE-67)(iii) is
the class form of the **general-position half** of (BE-22)(iii)(b); (BE-22)(iii)
is the 2-cut composition criterion the **S-mark** induction of (BE-25)(ii) runs at
every node of the rooted 3-block tree; and (BE-25)(ii)'s check **(a)** is *"implies
(BE-14) at the top — **yes**, at the root `H = G` and there is no marked pair"*.
So a **proof** of the inequalities at rung 3 discharges the rung-3 instances of
the universal the induction consumes. **The negative arm is not the only one with
a consumer** — by (BE-69)(ii) a shortfall holds identically on `Chart(H)` and
reaches (BE-14) the other way, and **both arms land somewhere**. This is the
question the spec asked to be checked before the round was spent, and the answer
is the favourable one.

**(BE-284)(ii)** `[UNTAGGED]` — **THE SCOPE LIMIT, and it is the most important
caveat this direction can deliver.** *"`Good ≠ ∅` at rung 3 is PROVED"* would need
**two** things, and the block family only reaches one of them. (BE-96)(iv) holds
*"at a **generic-regime** flag pair"*, and `bunif.flag_frame` returns `None` off
that regime — `π_x = π_y`, `p_x ∈ π_y`, `p_y ∈ π_x` are all rejected by its
`rank[p_x, e₁, e₂, p_y] = 4` test. **But `π_u = π_v` IS FORCED at an internal
R-node peel with both sides flexible, at 392 of 928** ((BE-81), direction
BONEONE; (BE-67)(iii) carries this as its own 2026-09-02 correction). At those
peels the four blocks **do not decompose the screw space at all** — there is no
`L = π_x ∩ π_y` of dimension 1 — so the 16-block criterion is not merely
unproved there, it is **not the right object**. Those peels are settled
**per-piece**, by (BE-86)(ii)'s 392 exact-ℚ certificates with shortfall `0` at
392/392 — which by (BE-69)(ii)'s consequence 1 is a **theorem per piece**, not a
measurement — but **not as a class**. And they are **rung-3 peels**:
(BE-86)(ii) reads `min(δ₁+δ₂, 6) = 2`, so `Σδ = 2 ≤ 6`. **Therefore: closing all
sixteen blocks proves `Good ≠ ∅` at rung 3 in the generic flag regime, and the
coincident-flag arm of rung 3 remains a per-piece theorem and a class-level
open question.** No single surface in the corpus states this, and the dispatch's
own framing (*"close them all → `Good ≠ ∅` at rung 3 is PROVED"*) does not carry
it.

**(BE-284)(iii)** `[PROVED]` — **which rungs each block can live at, since the
question will be asked next.** `c_i(U) ≤ min(ρ_i, d_S)` and `ρ₁ + ρ₂ ≤ Σδ` give
`c₁ + c₂ ≤ min(2 d_S, Σδ)`, while a violation needs
`c₁ + c₂ ≥ d_S + max(0, Σδ − 6) + 1`. Both together force **`Σδ ≤ d_S + 5`**.
So `⟨M⟩` and `⟨L⟩` can bind **only at rung 3**; the 2-dimensional blocks only at
`Σδ ≤ 7`; and the 5-dimensional ones survive to `Σδ ≤ 10`. ∎ **This is
(BE-225)(i)'s `Π_x` statement generalized** — that clause gets `Σδ ≥ 8` free at
`Π_x` from `c₁ + c₂ ≤ 4`, which is the `d_S = 2` case. **Consequence for the
arc:** rung 3 is where the *small* blocks live and the higher rungs keep the
*big* ones alive, so *"the higher rungs are free"* is true at `Π_x` and **false
in general**. Out of scope here; named so it is not assumed.

---

### *Step BE284* — **(BE-285): the verdict, the board, the prediction scored, and what this direction self-caught**

**(BE-285)(i)** `[UNTAGGED]` — **THE VERDICT, with the quantifier it carries.**
**The eleven remaining stable blocks can be closed at rung 3 in the generic flag
regime, and no violation is exhibited or located.** Precisely: **two** of them
(`⟨L⟩`, `⟨M⟩⊕⟨L⟩`) close by (BE-274)(i)'s two-step, cap-free, with the same L6
dependency `⟨M⟩` has; the other **nine** close under one named candidate,
**(BLOCK-GP)**, whose surviving shapes are disjoint from BPROPCL's residue. **No
block hosts a violation under any law this direction could test**, and the
arithmetic that would allow one is closed at every block by (BLOCK-GP). **What is
NOT claimed:** (BLOCK-GP) is not proved; `Good ≠ ∅` at rung 3 is therefore not
proved; and the coincident-flag arm of rung 3 is outside the family entirely
((BE-284)(ii)).

**(BE-285)(ii)** `[UNTAGGED]` — **the dispatch's prediction, scored; verdict,
mechanism and tell SEPARATELY**, per `RESEARCH-ARC.md` §7.

* **VERDICT: CONFIRMED, and the reasoning offered for it is REFUTED.** The spec
  predicted *"most of the eleven close, and the arithmetic triages them before any
  geometry"*. **Close: confirmed** (all of them, under one law). ***The
  arithmetic triages them before any geometry*: REFUTED.** Under L0–L4 alone,
  every one of the 14 live blocks keeps hundreds to thousands of violating tuples
  ((BE-280)(i), the `L0–L4` column) — which is (BE-97)(i) read at all sixteen
  blocks, and the spec's own briefing quoted (BE-97)(i) saying exactly that. The
  triage is **entirely** geometric: it is the table, and without it the
  arithmetic closes **nothing**.
* **THE SPEC'S *"WHERE I EXPECT TO BE WRONG"* SENTENCE: REFUTED, and refuting it
  cheaply is what produced the result.** It predicted the real content would be
  *"two or three singletons plus one structural argument"* about **block sums**,
  inheriting sums' closures from summands. `c_i` is **superadditive**
  ((BE-278)(ii)), so no such lemma exists — a sum binds where both summands are
  closed, with a `dim 1` witness. The one true block-sum lemma, the **trace**
  lemma (BE-278)(i), runs the other way and closes nothing. The structural
  argument that does exist is not about sums at all: it is **one confinement read
  at sixteen subspaces**.
* **MECHANISM: CONFIRMED IN ITS CONCLUSION, REFUTED IN ITS REASON** — the
  board's `0 of 9` becomes a split, not a clean tenth. The spec's mechanism was
  *"`⟨L⟩` is the exact structural analogue of `⟨M⟩` — the Plücker point of
  `π_x ∩ π_y`, `dim 1`, `cap 1` — so BMBLOCK's transversal transports to it"*, and
  it instructed that this be refuted first because *"(BE-30)(iv) confines `ρ̄_i`
  to `⟨P⟩` **because of that identification**"* of `⟨M⟩` with the virtual edge's
  own hinge line. **The transport does happen** — `⟨L⟩`'s column is identical to
  `⟨M⟩`'s and closes by the same derivation. **The stated reason is wrong in both
  halves**: (BE-30)(iv) mentions no block at all, so nothing was riding on the
  identification ((BE-278)(iii)); and the transversal is **not** BMBLOCK's — at
  `m = 2` the separating line for `⟨L⟩` is `M` **itself**, skew to `L` by the
  generic flag regime alone, which is a *cheaper* certificate than the
  non-collinearity `⟨M⟩` needs. **Nothing in the first slice rested on it**: the
  first slice was (BE-278)(ii)'s refutation, which is independent of `⟨L⟩`.
* **TELL: DID NOT FIRE, and it COULD have in the region it samples.** The tell was
  *"a row where `margin > 0` at any `U` other than the three closed ones"*. Over
  the `side` census's `(draw, U)` cells and the `pop` population, **no violation
  was found**, and no shape the arithmetic leaves alive was realized. **The region
  it samples is real**: rung-3 internal R-node peels, `a = (0,0)`, side-degree
  `≥ 2`, generic flag regime — `pop`'s 2 946 in-region peels, `side`'s library
  rows. **But the tell is structurally one-sided**, and this is its honest limit:
  a `margin > 0` needs **both** sides at once, and the two-sided census is the
  ~4-hour `block` run BMBLOCK fenced ((BE-277)(vi) item 7). What was run is the
  **per-side** column, where a violation shows as a side realizing
  `c_i(U) = B(m_i, U)` at small `ρ_i` — the necessary half. **So the tell fired in
  its one-sided form and the two-sided form was not run**, and that is disclosed
  rather than averaged in. **Semicontinuity, checked not quoted:** `c_i(U)` is
  **upper** semicontinuous ((BE-255)(i) row 4), so a draw is an **upper** bound
  and the tell runs the right way for **closing** and the wrong way for
  **witnessing** — exactly as at `⟨M⟩`. **F32, and the spec asked for it
  specifically:** `margin` is a **difference** `c₁ + c₂ − dim U − slack` of
  semicontinuous quantities, so it inherits **neither** cap direction; every
  figure above is therefore quoted at the level of `c_i(U)` and
  `dim(⟨P₀⟩ ∩ U)` — each individually upper semicontinuous — and **never as a
  cap on `margin` itself**.

**(BE-285)(iii)** `[UNTAGGED]` — **the board. What moved.** The block-sum
inheritance route refuted with an exact-ℚ witness before it was used
((BE-278)(ii)); the trace lemma proved and the deficiency's monotonicity recorded
((BE-278)(i)); the path confinement read as **block-agnostic**, correcting the
spec's reading of (BE-30)(iv) ((BE-278)(iii)); the **16-column table** proved,
certificated and measured, reproducing (BE-258)(iii)'s `α_x` histogram and
(BE-272)(ii)'s `⟨M⟩` column ((BE-279)); **(NO-END-ON-L)** found by the driver's
own assert, with the five cells it moves named ((BE-279)(iii)); `Π_x`'s threshold
upgraded from `dist_i ≤ 4` to `dist_i ≤ 5` by deleting the `α_x` detour
((BE-279)(v)); the rung-3 arithmetic taken at **all sixteen** blocks for the first
time, cap-free ((BE-280)); `⟨L⟩` and `⟨M⟩⊕⟨L⟩` closed by (BE-274)(i)'s two-step
((BE-280)(ii)); the residue named as **(BLOCK-GP)** and shown **disjoint** from
BPROPCL's ((BE-280)(iv), (BE-281)(iii)); the residue's population priced draw-free
over 2 946 in-region peels ((BE-283)); the whole table carried to `Chart(H)` at
13 664 asserted cells and **L6 measured at all sixteen blocks for the first time**
((BE-282)(i)/(ii)); **the census's own 100 % shown to be a CAP** by a draw-free
count of the mechanism that would refute it ((BE-282)(iii)); the **F26 consumer
check** answered for the **positive** arm ((BE-284)(i)); the **rung ceiling `Σδ ≤ dim U + 5`** proved,
generalizing (BE-225)(i) ((BE-284)(iii)); and the **generic-flag-regime scope
limit** stated in one place for the first time ((BE-284)(ii)).

**What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`,
(GR-15), **(BE-14)**, the S-mark, half (B), half (β), the 2-cut step, class
uniformity, cross-pair welding, `(BE-E4′)`, the flag base, `(BE-OBL7)`,
`(BE-OBLK)`, (BE-253)'s verdict and certificate, **(BE-259)(ii)'s and
(BE-277)(iii)'s residue** (untouched, and deliberately — BPROPCL owns it),
(BE-262)'s verdict, and **every landed measurement**. (BE-274)'s and (BE-272)'s
verdicts are **confirmed and extended**, never contradicted: `⟨M⟩`'s column here
is (BE-272)(ii)'s, and `⟨L⟩`'s closure is (BE-274)(i)'s derivation with one letter
changed. **The E-rider:** no termination-ledger entry fires; E1/E2/E3 are
§(K-grid) objects and the sibling GODDRUNG (112) is on that lane.

**(BE-285)(iv)** `[UNTAGGED]` — **what this direction self-caught.**

1. **The table was WRONG on first statement and the driver's assert caught it —
   TWICE, and the second time only at the REDUCED `validate` cap.** First at
   `dim(⟨P⟩ ∩ Λ²π_x) = 2` against a predicted `1` (`endL`), then — after the
   full-cap run was green at 4 480 cells — at `dim(⟨P⟩ ∩ ⟨M⟩) = 1` against `0`
   (`span`). **The second is the more instructive**: a *smaller* run found what a
   *larger* one missed, because the loci are proper closed conditions and a
   different rng stream hits different ones. The fix is not a patched constant but
   **a split of the claim into a pointwise floor and an equality stated as one
   Klein-pairing rank condition** ((BE-279)(ii)), which is the honest shape anyway
   since `dim(⟨P⟩ ∩ U)` is upper semicontinuous. **The `span` locus turns out to
   be (BE-272)(ii)'s own hypothesis**, so the driver rediscovered a landed
   proviso by failing on it — which is the check that the table and the path
   lemma are the same object.
2. **The candidate law was stated in a form (BE-45)(i) REFUTES, and this direction
   refuted it against the corpus rather than waiting for a measurement.** The
   equality `c_i(U) = max(0, ρ_i + B − m)` is false at a **series end**, where
   (BE-45)(i) forces `c_i(Π_x) ≥ 1` at every configuration with no genericity. The
   floored form (BLOCK-GP) is what the arithmetic is run at, and it closes all
   sixteen. **The stronger form's column is kept in the driver** so a reader can
   see exactly how much of the closure needs the floor — the answer is: nothing,
   both columns are `0`.
3. **The first background run of the census wrote ZERO bytes** — launched with
   `nohup … &`, which dies with its shell. This is the **same** failure
   (BE-276)(iii) disposed of one landing earlier, re-encountered rather than
   inherited. Re-launched in the harness's own background mode. No figure was
   taken from the dead run.
4. **The reservation's declaration hits are a DIFFERENT set at this baseline than
   the spec verified.** The spec verified at `69712c87` and reported *"`BE277`/
   `BE279` hit only previous reservations' bookkeeping"*. Re-verified at this
   direction's own baseline `16881765`: the colliding tokens are **(BE-278)**
   (6 hits), **(BE-280)** (4), **(BE-281)** (1) and **(BE-290)** (2), and every
   one is bookkeeping — BMBLOCK's return note at `labels.md:5620–5639`, this
   direction's own reservation row at `5653`, the tail note at `5671`, and the
   `notes/Phase39.md` status sentence at line 245. **No claim is minted at any of
   them.** Recorded because *"clean except the declaration"* was true and its
   **list** was not, and a successor re-verifying at a later `HEAD` will get a
   third list.
5. **`pop`'s per-block figures were nearly reported as failure counts.** A `+LP`
   entry of `743` is the number of peels at which the **table alone** does not
   exclude a violation, not the number that has one. Stated explicitly at
   (BE-283)(iii) rather than left for a reader to misread, because the `+L6`
   column (`17`–`79`) is the figure that actually measures the residue.
6. **The `⟨M⟩` cross-check at `248 of 2 946` is a SAME-INPUT reproduction**, not
   an independent confirmation: it replays `bmblock._jobs` at the same seed and
   the same committed defaults. It confirms the table reproduces BMBLOCK's
   `dist ≤ 5` threshold and buys comparability of the columns — nothing more. This
   is (BE-277)(vi) item 6's lesson, applied to this direction's own figure.
7. **A 100 % agreement was nearly reported as a confirmation, and the driver was
   made to price its own population instead.** `side`'s L7 column reads **13 664
   of 13 664**. The first draft of (BE-282)(ii) called that *"the law measured at
   every cell"*. It is not: (BE-45)(i)'s series end is the one landed mechanism
   that refutes L7, and `mech` shows it fires at **0 of 428** sides of the
   library — every terminal has between `2` and `5` distinct first edges. **A
   population that cannot host the counterexample cannot confirm the law**, and a
   dead confirmation looks identical to a live one. The mode was written **because
   the number was suspiciously clean**, not because a gate asked for it.
8. **`dim ⟨P₀⟩` and `dist_i` are kept apart throughout.** The table is stated in
   `dim ⟨P₀⟩`; the arithmetic needs a combinatorial input and substitutes
   `min(dist_i, 6)`, which is the **weaker** bound because `B` is monotone in `m`.
   The first draft of the arithmetic mode used the two interchangeably; they
   differ exactly at a degenerate configuration, and the substitution direction
   was checked rather than assumed.

---

### Confidence, and what would change this

**CONFIDENCE, clause by clause.**

* **HIGH** — (BE-278)(i)/(ii)/(iii), (BE-279)(i)/(ii)/(iv), (BE-280)(i)/(ii)/(iii)/(iv),
  (BE-282)(i)/(iii)/(iv), (BE-283), (BE-284)(iii). These are proofs, exhaustions,
  or asserts at named caps, and each has a driver testing that exact sentence.
* **HIGH, with a status notch** — (BE-279)(v), the `Π_x` threshold upgrade: the
  statement is solid, but at `m = 5` it is **generic with a witness**, one notch
  below (BE-259)(i)'s draw-free half. It **extends**, it does not supersede.
* **MEDIUM** — (BE-281), **(BLOCK-GP)**. It is a *named candidate*, chosen as the
  weakest form that still closes all sixteen blocks and the weakest form that
  survives (BE-45)(i). Its 100 % agreement on `Chart(H)` is **capped by
  (BE-282)(iii)**: the population cannot host the mechanism that would refute
  the unfloored version, and no population in the harness currently can.
* **MEDIUM-HIGH** — (BE-284)(i), the consumer check: the chain is read at owning
  sections, but the S-mark induction's coverage of **non-R-node** peels is
  assumed from (BE-22)(vi) and (BE-20) rather than re-verified here.
* **This direction's own least-sure clause is (BE-281)(ii)**, and it says so
  inside itself.

**WHAT WOULD CHANGE THIS.**

1. **A side with a series end, measured.** `mech` reports **0 of 428**; a side
   library extended with a **lollipop** (a pendant path from `x` into a θ, the
   shape (BE-45)(i) names) would let the `side` census test (BLOCK-GP)'s floor
   against the mechanism that motivates it. **That is the single highest-value
   next measurement on this lane**, it is cheap, and it is draw-light.
2. **The two-sided census.** Every figure here is **per-side**. A violation needs
   both sides at once, and `bgoodempty.run_block` at committed defaults is the
   ~4-hour run (BE-277)(vi) item 7 fenced. Until it runs, *"no violation found"*
   means *"no side realizes the necessary half"*, which is weaker.
3. **BPROPCL's lemma landing.** It discharges L6 and makes `⟨L⟩` and `⟨M⟩⊕⟨L⟩`
   unconditional; it leaves the nine untouched, because their surviving shapes
   have `dim ⟨P₀⟩ ≤ 5` on both sides ((BE-280)(iv)).
4. **A proof of (BLOCK-GP) at `dim ⟨P₀⟩ ∈ {4,5}`** closes the nine and, with
   item 3, proves `Good ≠ ∅` at rung 3 **in the generic flag regime**.
5. **The coincident-flag arm** ((BE-284)(ii)) would still be open as a class
   statement after all of that. Nothing here touches it, and nothing in the
   corpus states in one place that it is outside the 16-block family.
