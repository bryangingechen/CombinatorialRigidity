## §(K-bare-ext) — continuation (direction BDOUBLE): **(NO-DOUBLE-PENCIL) IS REFUTED, AND THE TIGHT BLOCK IS REDUNDANT** — BUNIF's named residue forbade a configuration that is generic, harmless and produced by **one landed lemma read at both ends**: (BE-45)(ii)'s own explicitly-flagged **vacuous corner** `d_min = 6` gives `ρ̄_i = ⟨P⟩ = Λ²K⁴`, hence `c_i(U) = dim U` at **every** stable `U` and in particular `c_i(Π_x) = c_i(Π_y) = 2`, while (BE-45)(i)/(ii) at the other side gives `c_j(Π_x) ≥ 1` — exactly the `(2, ≥ 1)` pair (NO-DOUBLE-PENCIL) forbids. It is realized **inside BUNIF's own 92-row population**, at `K4 + th(6,6,6)/ab + ear4/ua`, peel `(a,b)`: side 2 the `θ(6,6,6)` at `δ₂ = ρ₂ = 6`, side 1 the two-path side at `δ₁ = ρ₁ = d_min = 2`, `c = (1,2)` at **both** 2-blocks. **BUNIF's *"the two clauses have never been sought jointly"* is answered: they are not merely compatible, one lemma produces both.** And the double pencil is **SLACK, NOT A SHORTFALL** — `δ₁+δ₂ = 8`, so the block inequality's slack is `2` and the margin is `−1`, with the peel attaining at `dim(ρ̄₁+ρ̄₂) = 6`. The coordinator's **reading (1) is CONFIRMED**: (NO-DOUBLE-PENCIL) ⟺ `c₁+c₂ ≤ 2`, which is the obligation only at `δ₁+δ₂ ≤ 6` (28 of 49 `(δ₁,δ₂)` pairs), so the condition was **strictly stronger** than half (B) needs, and 320 of 1 975 conceivable double pencils are not violations at all. What replaces it is smaller and **per-side**: under **(PENCIL-SATURATES)** — *`c_i(Π) = 2` forces `ρ_i = 6`*, which is **(BE-38)(iii)'s third clause** read contrapositively — **every `Π_x` violation is a `U = Λ²K⁴` violation**, so `Π_x` and `Π_y` are **implied by the all-of-it inequality**, drop out of the fourteen, and are **FREE in the attaining case**. Reading (2)'s named weak link `dist_i ≥ 6 ⟹ δ_i = 6` is **REFUTED** — (BE-30) bounds `ρ` by `dist` from **above**, so a large `dist` removes a constraint rather than supplying one, and two measured sides sit at `dist = 6`, `δ = 1` — but its **conclusion** is recovered by a shorter route that never mentions `dist`. Job 2 **fires on both of the target's citations**

**Direction BDOUBLE** (ordinal 64, `notes/Pencil-fanout.md` §"BDOUBLE"), 2026-09-02.
Driver `notes/scripts/w4/bdouble.py`; labels **(BE-99)–(BE-103)**, *Steps
BE98–BE102*. Read against *Steps BE93–BE97* (BUNIF), whose (BE-97)(iii) is the
target, and *Steps BE43–BE45* ((BE-44)/(BE-45)/(BE-46)), which price it.

### Standing notation

Inherited verbatim from *Steps BE93–BE97*: `H` an internal R-node piece peeled
at `{x, y}` (`xy ∉ E(H)`), sides `H₁, H₂`; `ρ̄_i ⊆ Λ²K⁴` the side's relative
screw space, `ρ_i = dim ρ̄_i`, `δ_i = f_i − g_i`, `a_i = dim M_i − 6 − f_i`, so
`ρ_i = δ_i + a_i` ((BE-86)(i)); the **generic flag regime** `π_x ≠ π_y`,
`p_x ∉ π_y`, `p_y ∉ π_x`, in which `Λ²K⁴ = Π_x ⊕ ⟨M⟩ ⊕ ⟨L⟩ ⊕ Π_y` of dims
`(2,1,1,2)` with the **16** sums exactly the `S(ϕ)`-stable subspaces
((BE-94)(iii)); `c_i(U) := dim(ρ̄_i ∩ U)`, taken at its **generic** (= minimal)
value over side `i`'s own family ((BE-96)(iv)); `d_min` the length of a
shortest `x–y` path of the side, `⟨P⟩` the span of a path's hinge lines. Write

**`slack := max(0, δ₁ + δ₂ − 6)`**, so the block obligation at `U` is
**`c₁(U) + c₂(U) ≤ dim U + slack`** ((BE-96)(iv)), and a violation of it **is**
a shortfall by the modular law ((BE-95)(i)).

### Step BE98 — (BE-99): (NO-DOUBLE-PENCIL) is FALSE, and one landed lemma refutes it

> **(BE-99)(i)** *(proven; **the vacuous corner saturates every block**)*
> Suppose side `i` is **path-saturated** in (BE-45)(ii)'s sense with
> `δ_i = d_min = 6`. Then (BE-45)(ii) gives `ρ̄_i = ⟨P⟩` **as spaces** for a
> shortest path `P`, and `dim⟨P⟩ = ρ_i = 6 = dim Λ²K⁴`, so
>
> **`ρ̄_i = Λ²K⁴`, hence `c_i(U) = dim U` at EVERY subspace `U`** — in
> particular `c_i(Π_x) = c_i(Π_y) = 2`, the block cap. ∎
>
> This is not a new observation: **(BE-45)(ii) names this corner itself**
> (*"Note `δ₁ = 6` is the sub-case `d_min = 6`: (M2) subsumes the vacuous
> corner, where the intersection is all of `Π_u`"*). What is new is reading it
> **at a peel**, against (BE-97)(iii)'s condition.

> **(BE-99)(ii)** *(proven; **the partner clause is the same lemma**)* By
> (BE-45)(i) a **series end** at `x` on side `j` gives `c_j(Π_x) ≥ 1` at every
> configuration, and by (BE-45)(ii) so does **path saturation** `δ_j = d_min`
> at any `d_min`. Both are unconditional identities — no genericity, no draw.
> Hence at any peel with side `i` at the vacuous corner and side `j` in either
> mechanism,
>
> **`c_i(Π_x) = 2` and `c_j(Π_x) ≥ 1`: (NO-DOUBLE-PENCIL) FAILS**, and equally
> at `Π_y`. ∎

> **(BE-99)(iii)** *(**the witness**, and it was already inside BUNIF's own
> population)* The two hypotheses are simultaneously realizable. At
> `K4 + th(6,6,6)/ab + ear4/ua`, peel `(a,b)` — **population A**, one of the
> 92 rows (BE-97)(ii) measured — the combinatorics are configuration-free:
> **side 2 is the `θ(6,6,6)`**, three internally-disjoint `a–b` paths of length
> 6, so `d_min = 6`; **side 1 is `{a–v–b, a–e1₄–e1₃–e1₂–e1₁–u–b}`**, so
> `d_min = 2`. Measured (`bdouble.py witness`, 6 of 6 independent seeds drawing
> a generic-regime configuration, **every line an assert**):
>
> | quantity | value |
> |---|---|
> | `d_min` (side 1, side 2), from `bimage.dist_in` | **2, 6** |
> | `(ρ₁, δ₁, a₁)`, `(ρ₂, δ₂, a₂)` | **(2,2,0)**, **(6,6,0)** |
> | `ρ̄₂ = Λ²K⁴` **as a space**; `Π_x, Π_y ⊆ ρ̄₂` | **yes**, asserted as containments |
> | `c₁(Π_x), c₂(Π_x)` and `c₁(Π_y), c₂(Π_y)` | **1, 2** and **1, 2** |
> | `dim(ρ̄₁ ∩ ρ̄₂)` | **2** — the two sides meet **in all of `Π_x`** |
> | `dim(ρ̄₁ + ρ̄₂)` vs `min(δ₁+δ₂,6) + a₁ + a₂` | **6 = 6** — the peel **ATTAINS** |
>
> So the forbidden `(2, ≥1)` pair occurs, at **both** 2-blocks, at **2** of the
> 92 rows (`bdouble.py hunt`: 4 `(row, block)` hits, `2` at `Π_x` and `2` at
> `Π_y`). **(NO-DOUBLE-PENCIL) is REFUTED.** ∎

> **(BE-99)(iv)** *(why BUNIF's census did not see it)* (BE-97)(iii)'s table
> counts the `U` at which **both sides exceed the generic profile**
> `max(0, ρ_i + dim U − 6)`. A side at `ρ_i = 6` has `c_i(Π_x) = 2` **as its
> generic value**, so it never registers as exceeding, and the pair `(1,2)`
> is invisible to that statistic — which is why the census reported
> *"`Π_x` … where they sit at `c₁ = c₂ = 1`"*. The census is **correct as
> written**; what it measures is *non-genericity*, and a double pencil does not
> need non-genericity on both sides. **This is a candidate-side reading
> correction, not a correction of any landed measurement** — the same shape as
> (BE-45)(iii) and (BE-36).

### Step BE99 — (BE-100): it is SLACK, not a shortfall — reading (1), confirmed and used

> **(BE-100)(i)** *(proven; **reading (1)'s equivalence**)* Since
> `c_i(Π_x) ≤ dim Π_x = 2`, the pair `(c₁, c₂)` has one entry `= 2` and the
> other `≥ 1` **iff** `c₁ + c₂ ≥ 3`. Hence
>
> **(NO-DOUBLE-PENCIL) at `Π_x` ⟺ `c₁(Π_x) + c₂(Π_x) ≤ 2`,**
>
> whereas the obligation is `c₁ + c₂ ≤ 2 + slack`. The two coincide **exactly
> when `slack = 0`, i.e. `δ₁ + δ₂ ≤ 6`** — asserted over all 9 profile pairs
> and all 49 `(δ₁,δ₂)` pairs (`bdouble.py arith`; **28 of 49** agree, **21**
> do not). The coordinator's **reading (1) is CONFIRMED as arithmetic**: above
> the threshold the inequality has slack the condition never uses. ∎

> **(BE-100)(ii)** *(proven; **the exhibited double pencil is on the slack
> side**, and so is every one the corner produces)* At a vacuous-corner peel
> `δ_i = 6`, so `slack = max(0, δ_j) = δ_j`, and
>
> `c_i(Π_x) + c_j(Π_x) = 2 + c_j(Π_x) ≤ 2 + ρ_j = 2 + δ_j + a_j`,
>
> which is `≤ 2 + slack` **whenever side `j` attains** (`a_j = 0`). So the
> whole family of double pencils manufactured by (BE-99) is **harmless**: the
> obligation holds, with equality only at `c_j = δ_j`. At the witness
> `δ_j = 2`, `c_j = 1`, and the margin is **exactly `−1`** at both 2-blocks,
> asserted at every seed. **Half (B) is untouched by the refutation.** ∎

> **(BE-100)(iii)** *(the size of the gap, exhaustively)* Over the **6 400**
> tuples `(δ₁,δ₂,a₁,a₂,c₁,c₂)` the caps `ρ_i = δ_i + a_i ≤ 6` and
> `c_i ≤ min(2, ρ_i)` allow, **1 975** are double pencils and **1 655** are
> `Π_x` violations, and **every violation is a double pencil** (asserted). So
> the condition forbids **320** tuples the class statement permits — it is
> **strictly stronger**, and (BE-99) lands inside exactly that gap.

### Step BE100 — (BE-101): the REDUNDANCY THEOREM — `Π_x` and `Π_y` drop out of the fourteen

> **(BE-101)(i)** *(proven, given (PENCIL-SATURATES); **the tight block is
> implied by the trivial one**)* Name the per-side clause
>
> > **(PENCIL-SATURATES).** At an internal R-node peel in the generic flag
> > regime, `c_i(Π_x) = 2 ⟹ ρ_i = 6` — equivalently, if a side's generic
> > relative screw space contains the whole pencil at a terminal, it is the
> > whole screw space. Same at `Π_y`. *(This is exactly **(BE-38)(iii)'s third
> > clause**, "never `2` below `ρ₁ = 6`", read contrapositively.)*
>
> > **REFUTED AS STATED 2026-09-02 by (BE-104), direction BSATUR — read this
> > step with (PENCIL-SATURATES-GEN) in its place.** The clause fails at
> > **exactly `ρ_i = 5`**, at one plane of the legal pencil at a
> > side-degree-`1` terminal, in the generic flag regime and through both
> > gates. The **theorem below is unaffected as an implication**; what changes
> > is its hypothesis, which must be read **at a generic flag**
> > ((BE-107)(i)) — free, because (BE-14) is EXISTENTIAL ((BE-16)) and the good
> > locus is dense ((BE-69)). At an arbitrary legal flag the theorem's proof is
> > gone and **24** `Π_x` violations escape `U = Λ²K⁴` ((BE-106)(ii)).
>
> **Theorem.** Assume (PENCIL-SATURATES). If the obligation fails at
> `U = Π_x`, it fails at `U = Λ²K⁴`.
>
> *Proof.* A failure at `Π_x` is `c₁(Π_x) + c₂(Π_x) > 2 + slack` with both
> entries `≤ 2`, so some side — say 1 — has `c₁(Π_x) = 2`, and then
> `c₂(Π_x) > slack`. By (PENCIL-SATURATES) `ρ₁ = 6`, so
> `c₁(Λ²K⁴) = ρ₁ = 6`; and `c₂(Λ²K⁴) = ρ₂ ≥ c₂(Π_x) > slack`. Hence
> `c₁(Λ²K⁴) + c₂(Λ²K⁴) > 6 + slack = dim Λ²K⁴ + slack`. ∎
>
> Verified exhaustively (`bdouble.py arith`): over the same 6 400 tuples with
> the clause imposed, **300 of 300** `Π_x` violations are also `Λ²K⁴`
> violations, **0 escape**. **Negative control (F13):** drop the clause and the
> theorem fails — **313** `Π_x` violations escape, **30** of them in the
> attaining case, the smallest at `δ = (0,0)`, `a = (1,2)`, `c = (1,2)`. So the
> theorem genuinely rests on the clause, and the clause is the whole residual.

> **(BE-101)(ii)** *(corollary; **in the attaining case the two 2-blocks are
> FREE**)* The `U = Λ²K⁴` inequality reads `ρ₁ + ρ₂ ≤ 6 + slack`, i.e.
>
> **`a₁ + a₂ ≤ max(0, 6 − δ₁ − δ₂)`,**
>
> which is **automatic at `a₁ = a₂ = 0`**. So under (PENCIL-SATURATES) and
> (BE-22)(iii)'s `a = 0` case — the proviso the arc carries as **S-mark's pin**
> — there are **no `Π_x` violations at all** (asserted: 0 over the enumeration).
> **The measured tight place of (BE-97)(iii) is therefore closed**, and the
> live block list drops from **14 to 12**: neither `Π_x` nor `Π_y` can be the
> binding `U`. This is the direction's result, and it is a **reduction**
> (HIT shape 3), not a proof of half (B) — see (BE-103)(i) for the scope.
>
> > **Scope corrected 2026-09-02 by (BE-106)(iii).** Read at a **generic flag**
> > this stands verbatim under (PENCIL-SATURATES-GEN) and the count stays
> > **12**. Read **pointwise at an arbitrary legal flag** it does not: `Π_x`
> > and `Π_y` are back among the **14**, and 76 of 260 exhibited bad-flag rows
> > have `Π_x` exactly **tight** with `ρ₁ = 5`. No shortfall is exhibited at
> > any of them ((BE-106)(i)).

> **(BE-101)(iii)** *(the scope correction (BE-97)(i)'s own enumeration needs)*
> `bunif.never_bites` bounds `c_i ≤ min(dim U, δ_i)`. The true cap is
> `c_i ≤ min(dim U, ρ_i) = min(dim U, δ_i + a_i)`, so **the landed
> "14 of 16 blocks live" is an `a₁ = a₂ = 0` statement**. Re-run with the
> `ρ`-cap, **15 of 16** are live: only `U = ∅` still dies, and `U = Λ²K⁴`
> **joins** the list — which is precisely the block (BE-101)(i) routes a `Π_x`
> failure into. (BE-97)(i)'s conclusion — *the arithmetic does not triage the
> list* — is **unchanged and strengthened**; its **denominator** is corrected.
> Asserted both ways in `bdouble.py arith`.

### Step BE101 — (BE-102): reading (2) refuted at its named step, and job 2's verdict

> **(BE-102)(i)** *(**reading (2)'s weak link is REFUTED**, and the inequality
> points the wrong way)* Reading (2) needs `dist_i(x,y) ≥ 6 ⟹ δ_i = 6`. But
> (BE-30) gives `ρ ≤ dist` — and `ρ_i ≤ 6` always — so
>
> **`ρ_i ≤ min(dist_i, 6)`: `dist` bounds `ρ` from ABOVE.**
>
> A large `dist` therefore **removes** a constraint; it never supplies a lower
> bound, and `δ_i ≤ ρ_i` inherits nothing. Asserted at **184/184** sides of the
> two populations, and **refuted by measurement** at **2** of them —
> `K4(1,3,3,3,3,2)` and `K4(1,3,3,3,3,3)` at peel `(C,D)`, side 1, with
> `dist = 6` and `ρ = δ = 1` (`bdouble.py price`). The landed corpus already
> carried the same shape: (BE-44)(iii)'s loose rows have `δ₁ ∈ {0,3}` against
> `d_min ∈ {3,6}`. **Reading (2) fails at the step the coordinator named**, and
> the `δ = min(L,6)` identity of (BE-79)/(BE-80) does **not** survive off a
> path side.

> **(BE-102)(ii)** *(**its conclusion is recovered by a different route**)*
> What reading (2) wanted was `δ_i = 6` from `c_i(Π_x) = 2`. (PENCIL-SATURATES)
> supplies `ρ_i = 6` **directly**, without `dist`; in the attaining case
> `δ_i = ρ_i = 6`, whence `slack = δ_j` and a violation needs `c_j > δ_j`,
> i.e. `a_j ≥ 1` — **side `j` NON-ATTAINING**, exactly the conclusion reading
> (2) predicted. So the reading is **CORRECTED IN ITS ROUTE and CONFIRMED IN
> ITS CONCLUSION**; and (BE-101)(i) then supersedes it, since the same
> hypothesis kills the block outright rather than merely constraining it.

> **(BE-102)(iii)** *(**job 2** — the standing inventory verdict, run on this
> direction's own two load-bearing citations, and it FIRES on both)* The target
> (BE-97)(iii) states its two clauses as *"already priced by (BE-44)(ii) and
> (BE-45)"*. Read at the statements rather than the summaries:
>
> - **(BE-44)(ii)** is **PROVED in the `dim⟨P⟩ = 6` direction only** — *"`Π_u`
>   has dimension 2 in dimension 6, so `dim⟨P⟩ = 6` gives `⟨P⟩ = Λ²K⁴`"*, at
>   every configuration. The **converse** — `dim⟨P⟩ ≤ 5 ⟹ ⟨P⟩ ∩ Π_u` is
>   exactly the first line — is the **open condition (BE-46) discharges**,
>   **per shape, from one witness**, and (BE-46)(iv) says plainly that *"the
>   class-level statement over all pieces"* is **not** discharged. The price
>   (BE-97)(i) quotes — *`c_i(Π_x) = 2` forces every `x–y` path to span 6* — is
>   the **contrapositive of that converse**, so the target's first clause rests
>   on the **generic, per-shape** half, not the proved one. *(The remaining
>   step, `dim⟨P⟩ = 6 ⟹ |P| ≥ 6`, is free: `⟨P⟩` is spanned by the path's
>   `|P|` hinge lines, so `dim⟨P⟩ ≤ |P|`. The measured identity
>   `dim⟨P⟩ = min(|P|,6)` is not needed for it.)*
> - **(BE-45)** has its **forward** direction proved — (i) series end and (ii)
>   path saturation each force `c ≥ 1` unconditionally — while the **converse**
>   (BE-45)(iv), *"where neither mechanism fires the sharpening holds"*, is
>   **PROVED at 8 of 11 pieces and MEASURED at 3**. The target's second clause
>   reads (BE-45) as **characterizing** `c_j(Π_x) ≥ 1`, which is the converse:
>   **not a theorem**.
>
> **Both citations are used in their non-theorem direction** — the same shape
> BUNIF found one direction earlier at (BE-38)(iii)'s third clause
> ((BE-98)(ii)), and the second consecutive time a *"priced by"* phrase has
> outrun its own statement. **The refutation (BE-99) is unaffected**: it uses
> only (BE-45)(i)/(ii) **forward** and (BE-44)(ii)'s **proved** `= 6` half.
> **What this does change** is the standing of the residual: (PENCIL-SATURATES)
> is *not* implied by (BE-44)(ii) — that lemma yields `dist_i ≥ 6`, and
> (BE-102)(i) shows `dist_i ≥ 6` gives no lower bound on `ρ_i` — so the clause
> stands on (BE-38)(iii)'s measurement alone.

### Step BE102 — (BE-103): job 3 — the honest residual, the board, and the E-rider

> **(BE-103)(i)** *(**job 3**, stated in (BE-97)(iv)'s terms and not one word
> stronger)* **Half (B) is NOT discharged.** What this direction closes is the
> **measured tight place**: under (PENCIL-SATURATES) and `a₁ = a₂ = 0` the
> `Π_x`/`Π_y` blocks are free ((BE-101)(ii)), and those are the only blocks any
> measurement has ever seen bite on both sides (12/92). What remains:
>
> 1. **(PENCIL-SATURATES) itself** — *`c_i(Π) = 2 ⟹ ρ_i = 6`* — a **per-side**
>    implication, one quantifier, no pairing. Evidence: (BE-38)(iii)'s
>    measurement over **37** pieces, plus BUNIF's stress test (**4** sides at
>    `c_i(Π) = 2`, **0** with `ρ_i < 6`, over 112 rows) and this direction's
>    (**4** sides, **0**, over 92 rows). **Still a measurement, with a small
>    denominator**, and by (BE-102)(iii) **not** implied by (BE-44)(ii).
>    *(**SETTLED — negatively — 2026-09-02 by (BE-104)**: the clause is FALSE,
>    failing at exactly `ρ_i = 5`; item 1 is closed as posed and replaced by
>    **(PENCIL-SATURATES-GEN)**, with its own residual at (BE-107)(iii).)*
> 2. **The other 12 live blocks**, which (BE-97)(iv) records as
>    **unwitnessed rather than excluded** — 92 rows of two constructed
>    populations exhaust nothing. The shape (BE-97)(iv) names as the one that
>    would put a second block in play at once is still the right one to hunt:
>    **`c_i(⟨M⟩) = 1` on BOTH sides**, i.e. both relative screw spaces
>    containing the virtual edge's own line `p_x ∨ p_y`.
> 3. **The non-attaining case.** (BE-101)(ii) is stated at `a₁ = a₂ = 0`; off
>    it the `U = Λ²K⁴` inequality is the real constraint
>    `a₁ + a₂ ≤ max(0, 6 − δ₁ − δ₂)`, and by (BE-101)(iii) it is a **live**
>    block rather than a dead one.
> 4. Unchanged from (BE-98)(iii): **the ear case's (β) side at the window**,
>    modulo *Step BE56* / (BE-57)(iv)'s **(S1)**/**(S2)** — vacuous at every
>    drawn piece, neither a theorem, with a per-shape residue outside the
>    window — and **cross-pair welding** ((BE-28)(i)). *(The (S1)/(S2) clause
>    of this item is SUPERSEDED 2026-09-03: both are decided, *Steps
>    BE141–BE147*. The per-shape residue outside the window and cross-pair
>    welding stand.)*

> **(BE-103)(ii)** *(the board)* **What moved.** (BE-97)(iii)'s named successor
> condition is **false**, so the arc is not looking for a proof of it; the tight
> block is **redundant** given a clause the arc already carries; the
> triage denominator of (BE-97)(i) is corrected to an `a = 0` statement; and
> reading (2)'s `dist ⟹ δ` step is refuted, which also annotates the
> `δ = min(L,6)` identity as **path-side-only** wherever it is quoted.
> **What did not move.** No class statement is proved; **no shortfall is
> exhibited** — the exhibited double pencil is on the slack side, and by
> (BE-101)(i) a genuine one would show up at `U = Λ²K⁴` first; `hbareSplit`,
> `hK`, (GR-15) and class uniformity of the escape are all untouched; the
> coincident regime ((BE-98)(i)) still keeps only the cap.

### Verdict, classification, and the price

- **HIT shape 2** — *a double pencil exhibited*, and **classified**: it is a
  **slack** configuration at `δ₁+δ₂ = 8`, **not** a violation of the
  inequality, so it is **not** the third mechanism (BE-71) leaves open
  ((BE-99), (BE-100)(ii)).
- **HIT shape 3** — *reduced to a named condition strictly smaller than
  (NO-DOUBLE-PENCIL)*: **(PENCIL-SATURATES)**, a per-side implication with no
  pairing, under which `Π_x`/`Π_y` drop out of the fourteen entirely
  ((BE-101)).
- **NOT HIT shape 1** — (NO-DOUBLE-PENCIL) is **not** proved; it is **false**.
  The weaker `Π_x` inequality is proved **only modulo (PENCIL-SATURATES)** (and
  `a = 0`), which is why the verdict is a reduction and not a proof.
- **HIT shape 4** — job 2's verdict fires on **both** load-bearing citations
  ((BE-102)(iii)).
- **HIT shape 5** — job 3 answered in (BE-97)(iv)'s terms, with half (B)
  explicitly **not** reported as discharged ((BE-103)(i)).
- **Reading (1) CONFIRMED** ((BE-100)(i)) and immediately load-bearing: it is
  what makes the exhibited double pencil a non-event.
- **Reading (2) REFUTED at its named weak link, its conclusion RECOVERED**
  ((BE-102)(i)/(ii)).
- **The price, stated as a price.** (a) (BE-101) is **conditional** — its whole
  content is *"given (PENCIL-SATURATES)"*, and that clause is a measurement.
  (b) (BE-101)(ii) additionally assumes `a₁ = a₂ = 0`; the non-attaining case
  is left live, not closed. (c) (BE-99)(iii)'s witness is **one** piece at one
  peel; what makes it more than a lucky draw is that (BE-99)(i)/(ii) are
  identities, so the draw only certifies **realizability**. (d) Everything
  measured here rides on BUNIF's two **constructed** populations and adds no
  new one.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdouble.py arith     #  0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdouble.py witness   #  3.9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdouble.py hunt      # 28.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdouble.py price     # 26.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bdouble.py validate  # 33 s (reduced tiers, all four)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single seed
is `20260902`, printed by every mode. Every headline is an `assert`, not a
report: reading (1)'s equivalence and its threshold, the redundancy theorem and
its negative control, `margin ≤ 0` at every row, `slack` at every exhibited
double pencil, (PENCIL-SATURATES) at every side reaching `c_i(Π) = 2`,
(BE-30)'s `ρ_i ≤ min(dist_i, 6)` at every side, and the witness's ten identities
at every seed.

### Caps, disclosed rather than smoothed — with the denominator named

1. **The populations are BUNIF's, unchanged** — population **A** = BDECOR's 7
   R-node pieces + BPEEL's nested one; population **B** =
   `bpeel.constructed_tier(maxlen=3, nsamp=60)` filtered by BPEEL's disclosed
   **stand-in** `rnode_shaped`. **92** rows for `hunt`, **184** sides for
   `price`. This direction adds **no new population**, so its *"none found"*
   figures inherit (BE-98)'s caps verbatim and are **not independent evidence**
   of anything BUNIF already measured on them.
2. **The refutation needs no cap at all.** (BE-99)(i)/(ii) are identities off
   (BE-45); the population supplies only the **existence** of a peel meeting
   both hypotheses, and one witness suffices for an existence claim.
3. **`arith` is exhaustive**, not sampled: 9 profile pairs, 49 `(δ₁,δ₂)` pairs,
   6 400 `(δ,a,c)` tuples, 16 stable `U`. Its figures are enumerations, and the
   only modelling assumption is the cap `ρ_i ≤ 6`.
4. **`price`'s refutation is `2` sides of 184** — a **none-found-elsewhere**
   at that scale, not a claim that the failure is rare in the class.
5. **(PENCIL-SATURATES)'s stress test has a denominator of 4.** Four sides in
   92 rows reach `c_i(Π) = 2`; **0** have `ρ_i < 6`. That is the same small
   denominator (BE-98)(ii) disclosed, on an overlapping population — it is
   *not* a second independent confirmation.
6. **`witness` is 6 seeds on ONE piece and ONE peel.** The assertions are
   pointwise identities at those 6 configurations; the *generic* value of
   `c_i(U)` is inferred by (BE-69)(i)'s semicontinuity exactly as BUNIF infers
   it, and no more.

### Harness note — the `kbare/` sibling-import set gains its TWENTY-FIRST consumer

`bdouble.py` imports `bunif` (`battery_peels` / `battery_rows` / `tier_rows` /
`measure_row` / `SUBS` / `CAP` / `SEED`), `bimage` (`dist_in` / `contains` /
`dim` / `same_space`), `bdecor` (`sample_by_branches`) and `bpeel`
(`peel_sides`) **read-only** and reimplements nothing: the block frame, the
profile `c_i(U)`, the deficiency oracle, `ρ̄`, the peel split, the samplers and
the two bounds are all BUNIF's or its dependencies'. It is the **first**
external consumer of any `bunif` device. The chain is **nineteen** deep
(`… → bgenuine → bbase → bunif → bdouble`). **No move made**, per the standing
rule; the *interface decision* recorded at (BE-83)(iii) remains a
coordinator/user call.

### Confidence verdicts, per claim

| claim | verdict |
|---|---|
| (BE-99)(i) the vacuous corner gives `ρ̄_i = Λ²K⁴`, so `c_i(U) = dim U` | **proven** from (BE-45)(ii); asserted as a space equality at 6/6 seeds |
| (BE-99)(ii) the partner clause `c_j(Π_x) ≥ 1` | **proven** from (BE-45)(i)/(ii), both forward directions |
| (BE-99)(iii) the two hypotheses are simultaneously realizable | **measured** — 1 piece, 1 peel, 6 seeds; 2 of BUNIF's 92 rows |
| (BE-99)(iv) why BUNIF's census did not see it | **verdict** (a reading correction; no landed measurement changes) |
| (BE-100)(i) (NO-DOUBLE-PENCIL) ⟺ `c₁+c₂ ≤ 2`; threshold `δ₁+δ₂ ≤ 6` | **proven** (exhaustive, 9 + 49 cases asserted) |
| (BE-100)(ii) every vacuous-corner double pencil is slack, given `a_j = 0` | **proven** (one line from `c_j ≤ ρ_j`) |
| (BE-100)(iii) the 320-tuple gap | **proven** (exhaustive enumeration) |
| (BE-101)(i) the REDUNDANCY THEOREM, given (PENCIL-SATURATES) | **proven**; 300/300 caught, 0 escaping, with a negative control at 313 |
| (BE-101)(ii) `Π_x`, `Π_y` FREE at `a₁ = a₂ = 0` | **proven**, given (PENCIL-SATURATES) |
| (BE-101)(iii) "14 of 16 live" is an `a = 0` denominator; 15 of 16 off it | **proven** (exhaustive, both caps asserted) |
| (BE-102)(i) `dist ≥ 6 ⟹ δ = 6` is FALSE | **refuted** — `ρ ≤ min(dist,6)` proved from (BE-30), asserted 184/184; 2 explicit counterexample sides |
| (BE-102)(ii) the conclusion recovered through `ρ` | **proven**, given (PENCIL-SATURATES) |
| (BE-102)(iii) job 2 fires on (BE-44)(ii) and (BE-45) | **verdict**, read at the statements |
| (BE-103) the residual and the board | **verdict**, in (BE-97)(iv)'s terms |
| **(PENCIL-SATURATES)** itself | **MEASURED, not proven** — 37 pieces ((BE-38)(iii)) + 4 sides of 92 here; **this is the residual** |

### What would change this

- **A side with `c_i(Π) = 2` and `ρ_i < 6`.** That refutes (PENCIL-SATURATES),
  and with it (BE-101) entirely — the `Π_x` block returns to the residue and
  the enumeration's 313 escaping violations become live shapes. This is the
  single cheapest falsification of this direction, and the first place to look
  is a side whose every `x–y` path spans `≤ 5` yet whose `ρ̄_i` still contains
  `Π_x` — i.e. exactly where (BE-44)(ii)'s **per-shape** half is doing the work
  ((BE-102)(iii)).
- **A peel with `c_i(⟨M⟩) = 1` on both sides** and `δ₁+δ₂ ≤ 6`. That is a
  violation at `U = ⟨M⟩`, hence a genuine shortfall, and it is the shape
  (BE-97)(iv) names. Unwitnessed; `xy ∉ E(H)` removes the obvious source.
- **A peel with `a₁ + a₂ > max(0, 6 − δ₁ − δ₂)`.** That breaks `U = Λ²K⁴`
  directly, which (BE-101)(iii) shows is a **live** block off the attaining
  case — and by (BE-101)(i) it is where a `Π_x` failure would surface anyway.
- **A vacuous-corner peel whose OTHER side does not attain.** (BE-100)(ii)'s
  slack argument needs `a_j = 0`; at `a_j ≥ 1` the exhibited family stops being
  automatically harmless, and the classification would have to be redone
  row by row.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/Pencil-fanout-archive.md`, with the
2026-09-02 correction (`61e046a6`) in force: **"the target" in E1–E3 is the
ARC's target, `PencilPair K 3 G`**, never a direction's local obligation. The
corpus carries **two** E3 texts; **this reading is `:1700`'s two-conjunct
form**, with `:2098`'s one-conjunct deviation noted and **not** used — as
BBASE and BUNIF both read it.

- **E1** — a g-flank, a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: no colourings, no `D`, no g-flank here.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on either
  conjunct.** *Note the distinction this landing makes sharp*: what is refuted
  is **(NO-DOUBLE-PENCIL)**, a direction's local obligation, **not**
  `PencilPair K 3 G` — E2 is about the ARC's target, and refuting a candidate
  successor condition is ordinary progress. And this landing names a
  dispatchable attack ((PENCIL-SATURATES), (BE-103)(i) item 1).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct**: the target is not
  proven, and (PENCIL-SATURATES) is dispatchable rather than gated. Under
  `:2098`'s one-conjunct text it still does not fire, the first conjunct being
  the one that fails.

**F11 — the central rider, and the target was again a universal claim.**
*"At no internal R-node peel"* is a `∀` that no sweep exhausts — but this
direction did not need to exhaust it, because the answer is **negative** and a
`∀` is refuted by one witness. The figures that *are* sweeps are disclosed with
their denominators in *Caps*: **92** rows and **184** sides on BUNIF's two
**constructed** populations (A = the R-battery + the nested piece; B =
`constructed_tier(maxlen=3, nsamp=60)` behind `rnode_shaped`), with **no new
population added**. Every *"none found"* here — including (PENCIL-SATURATES)'s
`0 of 4` — reads **none found under those caps**, never *"does not exist"*, and
the `4` is the same small denominator (BE-98)(ii) disclosed. The claims that
are **not** sweeps are (BE-99)(i)/(ii) ((BE-45)'s identities), (BE-100)(i)–(iii)
and (BE-101) (exhaustive enumerations plus one proof), and (BE-102)(i)'s
`ρ ≤ min(dist,6)` (from (BE-30)).

**F12 paid at source.** Four hunks, at the statements rather than only here:
(BE-97)(iii) (the condition is refuted), (BE-97)(i) (its enumeration's `a = 0`
denominator), (BE-45)(ii) (its vacuous corner is what refutes (BE-97)(iii)),
and (BE-79)/(BE-80) (the `δ = min(L,6)` identity annotated **path-side-only**,
per the prep's explicit instruction).

**F21**: the `(K-bare)` gap-map row is **recomputed to a target** — 1 472 →
1 546 words while absorbing a full direction and five labels, i.e. ~110 words
of pre-existing prose compressed away against ~186 added — with label
preservation verified by a **scripted set-diff**: **129 codes in, 144 out, ZERO
dropped**. The direction then added a `SPECIAL_CAPS` entry (1 630 / 150); the
**coordinator WITHDREW it** the same day — the row is **compliant at 1 546 under
the generic 1 600**, and every other `SPECIAL_CAPS` entry was added for a row that
had *exceeded* its cap, with a density argument. The recompute stands; the ceiling
does not move (`check-gapmap-cells.py`'s docstring carries the full reason).

**Reservation, and what is returned.** Labels **(BE-99)–(BE-103)** and
***Steps BE98–BE102*** were reserved and are **consumed in full**; nothing is
returned. The driver `w4/bdouble.py` landed at the reserved path. One new
configuration-level object is named, per the reservation's own constraint (no
label for `Π_x`, `c_i(U)`, `margin`, `blockcap`/`blockdeg` or the double pencil
itself, all of which are BUNIF's existing prose names): the condition
**(PENCIL-SATURATES)**.
