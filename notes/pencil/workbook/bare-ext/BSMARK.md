## §(K-bare-ext) — continuation (direction BSMARK, ordinal 117, 2026-09-13)

**Question.** Can the S-mark 2-cut step be restated to close at a FORCED
coincident-flag peel — and what does that restatement cost the claims that
consume (BE-22)(iii)?

**Baseline.** `HEAD` = `5a67660b` at dispatch and at draft time; re-checked
against `HEAD`, never the working tree (two siblings in flight). Driver:
`notes/scripts/w4/bsmark.py` (new, untracked at draft time), seed `20260913`,
exact ℚ. No `.lean` opened (the standing 2026-08-05 Lean hold).

---

### The verdict in one paragraph

**The restatement closes, and it is CHEAPER than the repair (BE-313)(i) names
— because it is not an addition of an `a`-term at all, it is a DELETION.**
S-mark's clause is a conjunction: *"`H_B` attains **and** `H_B/uv` attains"*.
Read at (BE-22)(ii)'s owning section, the **second** conjunct is already
unconditional in `a`: *"`ρ_i ≤ dim M_i − 6 − g_i`, **with equality iff the
WELDED framework attains**"*, and `dim M_i − 6 − g_i = δ_i + a_i`. So
*"`H_B/uv` attains"* **is** `ρ = δ + a`, with no `a = 0` anywhere. Only the
**first** conjunct fails at a forced prescription ((BE-312)(ii), `a_i = 1` at
1 200/1 200). Delete it. What remains — call it **S-mark′** — composes by
(BE-86)(i), and the algebra is an identity: with `ρ_i = δ_i + a_i` on both
sides, *"`dim(ρ̄₁+ρ̄₂) = min(Σδ,6) + a₁ + a₂`"* is **equivalent to**
*"`dim(ρ̄₁ ∩ ρ̄₂) = max(0, Σδ − 6)`"*, **in which no `a`-term appears.**
The `a`-terms cancel between (BE-22)(ii)'s cap and (BE-86)(i)'s target, so
**the general-position obligation the induction carries is BYTE-FOR-BYTE the
one it carried before** — (BE-95)(i)/(BE-96)(iv)/(BE-97)'s
`c₁(U)+c₂(U) ≤ dim U + max(0, Σδ−6)` is untouched.

**The cost is not paid in general position. It is paid at the `a = 0` pin, and
two landed `[PROVED]` clauses go with it.** (BE-101)(ii) and (BE-219)(ii) name
`a₁ = a₂ = 0` in their own words as *"the proviso the arc carries as **S-mark's
pin**"*; S-mark′ does not supply it, so (BE-101)(ii)'s reduction of the live
block list from **14 to 12** lapses and (BE-101)(iii)'s already-landed
`ρ`-capped recount — **15 of 16** — is the correct denominator. And reading
(BE-22) at its owning section rather than off (BE-313)'s quotation turns up the
defect bar *(q)* was written for: **(BE-22)(iv) and (BE-22)(vi) carry the SAME
dropped hypothesis that BGENUINE corrected at (BE-22)(iii) on 2026-09-01, and
neither was corrected with it.** (vi) is cited by name by **16** claims,
including the one-sided discharge (BE-73)(ii)(b) that (BE-81)(iii) leaves
standing as all that survives of (BE-66)(iv). **And (vi) is not merely
imprecise — its conclusion is REFUTED at 44 exhibited configurations**
((BE-315)(ii)): over **984 forced one-sided peels** built by moving one
constant of BONEONE's generator (side 2 at `δ = 0` instead of `1`), 44 of the
972 that drew have **`ρ₂ ≥ 1` on the RIGID side**, which by the lower
semicontinuity of `ρ` is a **theorem** at the component of the draw. At those
44 the general-position half did not disappear — **it held, and it was the
attainment condition**, `dim(ρ̄₁ ∩ ρ̄₂) = 0` with a 2-dimensional `ρ̄₂` on a
rigid side at 24 of them. Forcing is also **more** common with a rigid side
(984 / 1 064) than at BONEONE's `(1,1)` (392 / 928), so this is not a corner.

**And the restatement converts (BE-312)(i)'s `292, not 392` from a hole into a
statement about the wrong object.** Under S-mark′ what each of BONEONE's 392
forced witnesses must exhibit is *welded attainment on both sides* and
*`ρ̄₁ ∩ ρ̄₂ = 0`* — and (BE-86)(ii) asserts **both, at 392 / 392**, together
with `H` attains at 392 / 392. Each is a **theorem at the component of the
exhibited point**, by semicontinuity alone and with **no irreducibility**, so
(BE-85)(iii)'s removal of the dense-or-empty dichotomy does not touch it.
`Good ≠ ∅` is 292 / 392; the consumer's own object is **392 / 392**.

**And the frame gets CHEAPER, not dearer, once it is stated rooting-free.**
Trying to refute the closure check turned up a second gap that S-mark already
has: under a fixed rooting the frame covers only the **child** side of each
tree edge, while the 2-cut step needs welded attainment on **both**. Stating
the clause over **tree edges** rather than **rooted nodes** — which
(BE-271)(ii) licenses, since *"the set of splits the induction must compose
across is the tree's **edge set**, independent of the rooting"* — closes it,
and it **removes (BE-25)(v)'s priced motive cost**: the rooting was only ever
there to name which side is the child.

**What the restatement does NOT do is make the coincident-flag arm safe.** It
moves the whole obstruction onto (BE-310)(ii)'s one inequality: the budget
line is `a₁ + a₂ ≤ 6 − min(Σδ,6)` in the screw space and
`a₁ + a₂ ≤ 3 − min(Σδ,6)` under (BE-310)(i)'s confinement, which is negative at
`Σδ ≥ 4` — BSIGFOUR's question, not answered here.

---

### *Step BE313* — **(BE-314): what the restatement actually is, and the identity it turns on**

> **(BE-314)(i)** `[PROVED]` *(the restatement is a DELETION, not an addition;
> read at (BE-22)(ii)'s owning section, BINDUC *Step BE21*)* S-mark's clause at
> a node `B` with parent pair `{u,v}` is, verbatim ((BE-25)(ii), owning section
> BTWOCUT *Step BE24*): *"the union `H_B` of `B`'s subtree (virtual edges
> deleted) has an irreducible component of `Y°(H_B)`, with the flags at `u,v`
> prescribed, at whose generic point **`H_B` attains and `H_B/uv` attains**"*.
> Write `f = def₃(H_B)`, `g = def₃(H_B/uv)`, `δ = f − g`, and at a
> configuration `q` write `a(q) = dim M(H_B,q) − 6 − f ≥ 0`,
> `ρ(q) = dim ρ̄_{uv}(H_B, q)`.
>
> **Note that (BE-22)(ii) is already unconditional in `a`.** Its statement is
> *"`ρ_i ≤ dim M_i − 6 − g_i`, **with equality iff the WELDED framework
> attains**"*, and its proof invokes only the partition cap at the contracted
> multigraph; the `a = 0` reading (*"when the piece attains this reads
> `ρ_i ≤ δ_i`"*) is a **corollary appended to it**, not its content.
> Substituting `dim M_i = 6 + f_i + a_i` gives `dim M_i − 6 − g_i = δ_i + a_i`,
> so
>
> **`ρ = δ + a` ⟺ `H_B/uv` attains — at every configuration, with no
> hypothesis whatsoever.**
>
> Hence S-mark's **second** conjunct is already in the form (BE-313)(i) asks
> for. Only the **first** conjunct — `a = 0` — is the one that fails at a
> forced prescription. **The restatement is therefore the deletion of the first
> conjunct**, and the resulting frame is
>
> **S-mark′** (the deletion, stated as S-mark is; superseded within this
> section by the rooting-free **S-mark″** of (BE-314)(iii))**.** *Relative to a
> rooted 3-block tree of `G`: for each non-root
> node `B` with parent separation pair `{u,v}` and each legal prescription `ϕ`
> of the flags at `u,v`, the union `H_B` of `B`'s subtree has an irreducible
> component of `Y°(H_B; ϕ)` at whose generic point **`H_B/uv` attains** —
> equivalently `ρ = δ + a`. At the root, `G` attains.*
>
> **The spec's candidate mechanism, refuted before anything was built.** The
> dispatch offered *"the `a`-term version closes because `a_i ≥ 1` on exactly
> the side whose flag is forced, making the composite deficiency bookkeeping
> additive again"*, and named BCOFLAG's `(a₁,a₂)` split as the first test. The
> split **refutes it in one read**: (BE-86)(ii)'s census is `(0,1)` at **60**
> and `(1,0)` at **40**, so the loss falls on **either** side, and there is no
> *"the side whose flag is forced"* — `π_u = π_v` is **one** coincidence and
> forces **both** flags. The bookkeeping is not made additive by `a`; it is
> additive already, and the `a`-terms **cancel** ((BE-314)(ii)) rather than
> accumulate. **Nothing in this section rests on that mechanism.**
>
> **This matters because (BE-313)(i)'s phrasing suggests an addition.** It
> names the repair as *"`a_{H_B} = 0` **or** the composite's
> `min(Σδ,6) + a₁ + a₂` identity is met"* — a disjunction whose second disjunct
> mentions `ρ̄₁, ρ̄₂` of **both** sides, i.e. an object one level **above** the
> node the clause is stated at. An inductive clause at `B` that quantifies over
> the parent's other side is not an induction over the tree; S-mark′ is a
> statement about `H_B` alone and has no such defect. **The mathematics
> BCOFLAG points at is right; the shape it proposes is not the one that
> works.**

> **(BE-314)(ii)** `[PROVED]` *(the identity the whole verdict rests on — the
> `a`-terms CANCEL, so the restatement costs nothing in general position;
> driver `bsmark.py cancel`, draw-free, seedless, 0.0 s)* Suppose S-mark′ holds
> on both sides of a 2-cut `{u,v}` of `H`, i.e. `ρ_i = δ_i + a_i` for `i = 1,2`
> at the chosen configuration. Write `s = dim(ρ̄₁ ∩ ρ̄₂)`. Then
>
> **`H` attains ⟺ `s = max(0, Σδ − 6)`.**
>
> *Proof.* `dim(ρ̄₁+ρ̄₂) = ρ₁ + ρ₂ − s = Σδ + a₁ + a₂ − s`. (BE-86)(i)
> (owning section BGENUINE *Step BE85*) is `H` attains ⟺
> `dim(ρ̄₁+ρ̄₂) = min(Σδ,6) + a₁ + a₂`. Substituting and cancelling `a₁ + a₂`
> from both sides leaves `Σδ − s = min(Σδ,6)`, i.e.
> `s = Σδ − min(Σδ,6) = max(0, Σδ − 6)`. ∎
>
> **No `a`-term survives on the right.** At `a₁ = a₂ = 0` this is exactly what
> (BE-22)(iii)(b) asks for, so **the general-position half the induction
> carries is unchanged by the restatement** — and in particular the obligation
> family `c₁(U) + c₂(U) ≤ dim U + max(0, Σδ − 6)` of (BE-95)(i)/(BE-96)(iv),
> the whole generic-flag apparatus, is **not touched**. That is the precise
> sense in which the restatement is cheap, and it is the sentence a successor
> should quote rather than *"(BE-86)(i) has the `a`-term in it"*.
>
> **The envelope this puts on `a` is NOT new and is not claimed as new (F34).**
> `dim(ρ̄₁+ρ̄₂) ≤ 6` turns the criterion into `min(Σδ,6) + a₁ + a₂ ≤ 6`, i.e.
> **`a₁ + a₂ ≤ max(0, 6 − δ₁ − δ₂)`** — which is (BE-101)(ii)'s own displayed
> line (*"The `U = Λ²K⁴` inequality reads `ρ₁ + ρ₂ ≤ 6 + slack`, i.e. …"*,
> owning section BDOUBLE *Step BE100*), and (BE-220)(ii) already ran it over
> 1 270 relaxation tuples. The driver re-derives it only so the budget table
> sits beside the identity; the figure is theirs.
>
> Asserted tuple by tuple over `δ_i ∈ 0…6` (the (BE-21)(ii) bound), `a_i ∈ 0…6`
> and every legal `s`, at **1 344 / 1 344**. **CAP, disclosed:** `a_i ∈ 0…6` is
> a **range choice** — nothing in the corpus bounds `a_i` — so the assertion is
> exhaustive over that box and says nothing outside it. The proof above is
> box-free; the driver is its control.

> **(BE-314)(iii)** `[PROVED]` *(S-mark′ against (BE-25)(ii)'s own three
> checks, re-run rather than assumed)* **(a) implies (BE-14) at the top —
> `yes`, but by one extra line, where S-mark got it for free.** S-mark's check
> (a) reads *"**yes** — at the root, `H = G` and there is no marked pair"*:
> the root instance of S-mark **is** (BE-14). S-mark′ has deleted exactly that
> conjunct, so at the root it says **nothing**, and the root clause *"`G`
> attains"* has to be obtained from the **top tree edge's 2-cut step** by
> (BE-314)(ii). That is a real if small structural change and it is named, not
> smuggled: S-mark′ is *"welded attainment everywhere below, attainment at the
> root"*, an induction whose hypothesis is **weaker than its conclusion** —
> which is forced, because the conclusion `a = 0` is **false** at a forced
> prescription ((BE-312)(ii)) and an induction cannot carry a false clause.
>
> **Check (b), closed under 1-cut and 2-cut — `yes`, and the deleted conjunct
> played no part in the closure argument; but (b) has a SECOND gap, which
> S-mark shares and which S-mark′ can fix for free.** S-mark's (b) reads *"each
> subtree attaches at **exactly one** separation pair, and contracting the
> marked pair leaves every child attachment pair a 2-cut, so the recursion for
> the welding clause parallels the recursion for attainment"*. S-mark′ keeps
> the welding clause and drops the attainment clause, so it keeps the half of
> (b) that was argued and drops the half that was free.
>
> **The second gap, found by trying to refute this clause rather than to
> confirm it.** Build `H_B` from `B`'s skeleton `B°` by gluing the children in
> some order. At the `j`-th gluing, side 2 is `B`'s skeleton with the parent
> virtual edge deleted, the first `j−1` child virtual edges replaced by their
> subtrees, and the `j`-th deleted. **Two things go wrong, and the first is
> earlier than one expects.** *(1)* Even at `j = 1`, if `B` has `≥ 2` children
> then side 2 is the 3-connected skeleton minus **two** edges, and
> (BE-25)(iii) covers **one**: its bound is `d_H(P) ≥ ⌈3q/2⌉ − 1`, and the
> clause itself records that bound as **tight** (*"the worst `q ≥ 2` partition
> value is exactly `−1` … so the bound is tight"*), so it does not survive a
> second deletion. *(2)* At `j ≥ 2` side 2 is `B° ∪ H_{C₁} ∪ …`, which is
> **not any node's subtree union** under the chosen rooting, so **no S-mark
> clause supplies its welded attainment at `{x_j, y_j}`.** Under a fixed
> rooting the frame covers exactly one side of each tree edge — the **child**
> side — while (BE-22)(iii)(a) needs `ρ_i = δ_i` on **both**.
>
> **This is not an objection to the restatement; it is an argument for stating
> S-mark′ WITHOUT a rooting, and (BE-271)(ii) licenses exactly that.** Its
> words: *"A 2-separation of `G` is a **tree edge** … re-rooting flips which
> endpoint is called parent but does not delete the edge, and (BE-22)(iii)'s
> criterion is **symmetric in the two sides** … So the set of splits the
> induction must compose across is the tree's **edge set**, independent of the
> rooting."* So state it edge-wise:
>
> **S-mark″ (the rooting-free form, and the one to carry).** *For every tree
> edge `{u,v}` of the 3-block tree of `G`, **each of its two sides** `H`, and
> each legal prescription `ϕ` of the flags at `{u,v}`: some irreducible
> component of `Y°(H; ϕ)` has `ρ_{uv}(H) = δ_{uv}(H) + a(H)` at its generic
> point — equivalently `H/uv` attains. And `G` attains.*
>
> **Two things this buys, and they are the direction's bonus.** It closes the
> gap above, because both sides of every gluing are now covered. And it
> **removes (BE-25)(v)'s priced motive cost**: that clause says *"S-mark
> carries a rooted tree and a marked pair, so it is a **motive-level
> change**"*, and the rooting was only ever there to name which side is the
> child. S-mark″ carries an **unrooted tree and a marked edge**. **NOT
> CLAIMED AS FREE:** whether the corpus's carrier can state a clause indexed by
> an unrooted tree edge is a question for whoever writes the motive, not one
> this direction can settle from the workbook.
>
> **Check (c), holds at the base classes — `yes`, and *a fortiori*.** S-mark′'s clause
> at a node is **implied by** S-mark's (`a = 0` and `ρ = δ` give `ρ = δ + a`),
> so any base discharge of S-mark discharges S-mark′. (BE-25)(iii)/(iv) are
> therefore inherited **unchanged**, and (BE-25)(v)'s *"the strengthening costs
> nothing at the base"* survives verbatim. **SELF-CAUGHT:** this direction
> first wrote the opposite — that `δ = 0` with `a > 0` makes `ρ = a` a new base
> obligation, and that the base would have to be re-discharged at the flat via
> (BE-20)(ii) `[INFORMAL]`. That is wrong by one line of monotonicity: the new
> clause is *weaker*, so it cannot cost more. The wrong version would have
> moved the base's support from two `[PROVED]` clauses onto an `[INFORMAL]`
> one, which is exactly the kind of sentence that propagates.

---

### *Step BE314* — **(BE-315): (BE-22)(iv) and (BE-22)(vi) carry the SAME dropped hypothesis, and nobody corrected them with (iii)**

> **(BE-315)(i)** `[PROVED]` *(a defect in two landed `[PROVED]` clauses, found
> by reading (BE-22) at its owning section — bar (q)'s case; arithmetic witness
> `bsmark.py cancel`)* On 2026-09-01 BGENUINE attached a **FORWARD POINTER** to
> (BE-22)(iii) recording that *"if both pieces attain" is not decoration*. That
> correction was made at (iii) **and nowhere else in the step**. Its two
> siblings use the same step and drop the same hypothesis in their **headline
> sentences**.
>
> Here is **(BE-22)(iv)**, verbatim: *"**`δ₁ = δ₂ = 0` makes the composition
> automatic:** then `ρ_i ≤ δ_i = 0`, so `dim(ρ̄₁+ρ̄₂) = 0 = min(0,6)` and (iii)
> fires with no general-position content. In particular **two rigid pieces
> always compose over a 2-cut** … **This is why the *base* of the induction
> never meets the hard case.**"* The step `ρ_i ≤ δ_i` is (BE-22)(ii)'s
> **corollary at `a_i = 0`**; in general `ρ_i ≤ δ_i + a_i = a_i`.
>
> And here is **(BE-22)(vi)**, verbatim: *"**If one side is rigid the general-position half
> disappears.** When `δ₂ = 0`, (ii) gives `ρ₂ = 0`, so
> `dim(ρ̄₁ + ρ̄₂) = ρ₁` …"*. Same step: (ii) gives `ρ₂ ≤ δ₂ + a₂ = a₂`, and
> `ρ₂ = 0` needs `a₂ = 0`.
>
> **What is and is not wrong.** Both clauses say *"and (iii) fires"* / cite
> (iii), and (iii) carries the hypothesis, so **neither is unsound as a
> derivation from (iii)**. What is wrong is that **both headline sentences are
> quoted without it**, and both are quoted that way by their consumers — which
> is precisely the failure mode BGENUINE's F12 rider documents at (iii)'s own
> gap-map row. Corrected statements:
>
> Corrected, **(BE-22)(iv′)**: `δ₁ = δ₂ = 0` **and both pieces attain** make the
> composition automatic. Without the second hypothesis, `ρ_i ≤ a_i`, the
> attainment target is `a₁ + a₂`, and by (BE-314)(ii) `H` attains iff
> `ρ̄₁ ∩ ρ̄₂ = 0` — **a genuine general-position condition between two rigid
> pieces.**
>
> Corrected, **(BE-22)(vi′)**: if one side is rigid **and attains**, the general-position
> half disappears. With `δ₂ = 0` and `a₂ ≥ 1`, `ρ̄₂` may be up to `a₂`-
> dimensional and attainment requires `ρ̄₁ ∩ ρ̄₂ = max(0, Σδ−6)`.
>
> Enumerated (`bsmark.py cancel`, draw-free, over `δ_i ∈ 0…6`, `a_i ∈ 0…6`):
> at `δ₂ = 0`, the tuples split **49** with `a₂ = 0` — where `ρ₂ = 0` is
> **forced** and (vi) holds — against **50** with `a₂ ≥ 1`, both `ρ_i ≥ 1` and
> the target still reachable, where it does not. At `δ₁ = δ₂ = 0` the
> corresponding count is **15**, the smallest being
> `(a₁, a₂, ρ₁, ρ₂) = (1, 1, 1, 1)`: **two rigid pieces, each losing one
> dimension of attainment, composing iff two lines in the screw space are
> distinct.** **CAP:** `a_i ∈ 0…6` is a range choice, as in (BE-314)(ii).

> **(BE-315)(ii)** `[REFUTED]` *(witness: 44 exhibited configurations,
> `bsmark.py rigid`, 844.0 s, seed `20260913`, exact ℚ — **(BE-22)(vi)'s
> conclusion `ρ₂ = 0` is FALSE at a forced one-sided peel**)* (i) says two
> derivations are invalid without a hypothesis. This mode asks whether the
> case is **inhabited**, and it is.
>
> **The population.** BONEONE's factorized generator with **one constant
> moved**: side 1 is every K₄-skeleton R-node side at `δ = 1` (`n₁ ∈ {9,10}`,
> as BONEONE), side 2 every unrestricted side at **`δ = 0`** instead of `δ = 1`
> (`n₂ ∈ {4,5}`). Every member is therefore exactly (BE-22)(vi)'s hypothesis —
> one rigid side at a 2-cut — and the forcing test (`bgenuine.forced_seed`,
> which is `bpeel.pair_forced`'s growth rule with the derivation recorded) is
> unchanged. **Control, asserted:** the parameterized enumerator reproduces
> `boneone.free_sides(n)` exactly at `want = 1`, `n = 4, 5`.
>
> **The census.** **1 064** family members, **984 FORCED** — against BONEONE's
> **392 of 928** at `(1,1)`. *Forcing is MORE common with a rigid side, not
> less*, which is what makes the one-sided discharge load-bearing rather than
> a corner. Geometry at stride 1, i.e. **every forced member**; `3` guarded
> flat-`A` draws each; **12** rows gave no guarded draw in 3 tries and are
> excluded, leaving **972**:
>
> | `(a₁, a₂, ρ₁, ρ₂, dim(ρ̄₁+ρ̄₂), attains, dim(ρ̄₁ ∩ ρ̄₂))` | count |
> |---|---|
> | `(0, 0, 1, 0, 1, 1, 0)` | **604** |
> | `(1, 0, 2, 0, 2, 1, 0)` | **324** |
> | `(0, 1, 1, 1, 2, 1, 0)` | **12** |
> | `(0, 2, 1, 2, 3, 1, 0)` | **24** |
> | `(1, 1, 2, 1, 3, 1, 0)` | **8** |
>
> **`ρ₂ ≥ 1` on a `δ₂ = 0` side at 44 of 972.** `ρ_i` is **lower**
> semicontinuous ((BE-255)(i) row 2), so a draw is a **lower** bound and
> `ρ₂ = 1` or `2` at a draw is a **THEOREM** at the irreducible component
> containing it — **no cap, no irreducibility of `Chart(H)` needed.** So at
> those 44, (BE-22)(vi)'s *"when `δ₂ = 0`, (ii) gives `ρ₂ = 0`"* is **false at
> the generic point of an exhibited component**, and with it the headline
> *"the general-position half disappears"*. The count is **conservative**: the
> row reported per witness is the draw minimising `a₁ + a₂`, and `ρ₂ ≤ a₂`, so
> minimising `a₂` minimises `ρ₂`'s ceiling.
>
> **The general-position half did not disappear — it HELD, and it was doing the
> work.** At all 44, `dim(ρ̄₁ ∩ ρ̄₂) = 0` and `H` attains; by (BE-314)(ii) with
> `Σδ = 1` that intersection being `0` is **exactly** the attainment condition.
> At `(0,2,1,2,3,1,0)` a **2-dimensional `ρ̄₂` on a RIGID side** has to miss a
> line. Every row also satisfies `ρ_i = δ_i + a_i` on both sides and the
> (BE-86)(i) criterion, asserted at every draw.
>
> **What this does and does not refute.** The one-sided discharge
> ((BE-73)(ii)(b), BPEEL's (BE-22)(vi) row: *"wherever the located enemy is
> forced one-sidedly, the general-position half it would attack has already
> disappeared — a **stronger** discharge … covers **every** forcing mechanism,
> landed or not"*) runs *one-sided certificate ⇒ `δ_i = 0` ⇒ (BE-22)(vi) ⇒ no
> general-position content*. **The second arrow is refuted** — `δ₂ = 0` does
> **not** imply the collapse — and that is a general implication, so the
> refutation does not depend on which certificates the 44 rows carry.
> **NOT CHECKED HERE, and named so a successor does not assume it:** whether
> the 44 rows' own forcing derivations are **one-sided** in (BE-77)(i)(b)'s
> sense. `bgenuine.forced_seed` returns the trace and `boneone`'s
> side-membership test is one line, so that is a cheap follow-up. (BE-81)(iii)
> leaves *"precisely the one-sided half, which is a theorem ((BE-73)(ii)(b))
> and is untouched"* as **all** that survives of (BE-66)(iv); this direction
> does not claim that half is gone, only that **its stated mechanism is not
> available as a general implication.**
>
> **CAPS.** Generator: K₄ skeleton on side 1, `n₁ ∈ {9,10}`, `n₂ ∈ {4,5}`,
> `δ = (1,0)` — BPEEL's wider **3 497** forced R-node peels with
> `min(δ₁,δ₂) = 0` are **not** swept. Draws: `3` per row, `|coord| ≤ 20`
> (`draw_flat`'s default), **not** re-run at a second box. `a₂ ≥ 1 at all 3
> draws` is **NOT FOUND UNDER CAP 3 draws** and is not claimed as a theorem —
> the theorem is the `ρ₂ ≥ 1` half, which needs only the exhibited draw.
> The driver's own banner phrases stride `1` as *"every 1th … 984 of 984"*;
> read it as **exhaustive over this generator's forced members**.

---

### *Step BE315* — **(BE-316): the blast radius, enumerated**

> **(BE-316)(i)** `[PROVED]` *(the enumeration the spec asked to be priced
> before any restatement is proposed; `ledger.py --cited-by`, `HEAD`
> `5a67660b`)* `--cited-by '(BE-22)'` returns **64** claims; six clauses are
> cited by name. The per-clause split is **(i)** 9, **(ii)** 17, **(iii)**
> **28**, **(iv)** 1, **(v)** 3, **(vi)** **16** — these are ledger **rows**,
> so a label-clause that appears in two files contributes two (e.g.
> (BE-67)(iii), which has a BDECOR row and a BPEEL row). Sorted by what
> S-mark′ does to them:
>
> **A — untouched, because they already read the `a`-corrected criterion.**
> (BE-86)(i)/(ii); (BE-220)(ii) (*"(BE-22)(iii) as corrected by (BE-86)(i)"*);
> (BE-310)(ii) and (BE-311)(i) (built on (BE-86)(i)); (BE-271)(i) (quotes the
> criterion **with** the `+ a₁ + a₂`) and (BE-271)(ii) (whose re-rooting
> argument turns on the criterion being **symmetric** in `a₁+a₂`, which
> survives); (BE-67)(ii) (per-row biconditional at an exhibited configuration);
> (BE-66)(ii) (generic-flag chain-span law); (BE-23)(a)/(e) (S-mark′'s clause
> is weaker, so a case that satisfied S-mark satisfies it).
>
> **B — lose their hypothesis; conclusions RESTRICTED, not refuted.** These are
> the clauses that state `a₁ = a₂ = 0` **in their own text** and attribute it
> to S-mark:
> - at **(BE-101)(ii)** — *"under (PENCIL-SATURATES) and (BE-22)(iii)'s `a = 0`
>   case — **the proviso the arc carries as S-mark's pin** — there are no `Π_x`
>   violations at all … the live block list drops from **14 to 12**"*. Under
>   S-mark′ the pin is gone and **the 14 → 12 reduction lapses.**
> - at **(BE-101)(iii)** — already landed, and it is the **price tag**:
>   *"`bunif.never_bites` bounds `c_i ≤ min(dim U, δ_i)`. The true cap is
>   `c_i ≤ min(dim U, ρ_i) = min(dim U, δ_i + a_i)`, so the landed '14 of 16
>   blocks live' is an `a₁ = a₂ = 0` statement. Re-run with the `ρ`-cap,
>   **15 of 16** are live"*. **So the restatement's price on the generic-flag
>   arm is 12 → 15 live blocks**, and the corpus computed it before this
>   direction was dispatched (F34).
> - at **(BE-219)(ii)/(iii)/(iv)** — all three are stated *"at `a = 0`"*; their
>   exhaustions are over the `a = 0` slice of the tuple space and are correct
>   there. Under S-mark′ they are **conditional results**, not standing ones.
> - at **(BE-227)(ii)** — *"Of the **324 `a = 0` tuples**, 30 violate the
>   obligation"*: the denominator is the `a = 0` slice.
> - at **(BE-293)(i)/(iii)/(iv)** — clause (a) of the properness certificate is
>   `a_i(q) = 0`. This is **supplied by measurement, not by S-mark**
>   ((BE-293)(iv): `a_i = 0` at 1 281/1 281 draws), so BPROPCL is unaffected in
>   substance. What changes is (BE-293)(iii)'s sentence *"That is precisely
>   (BE-22)(iii)(a), the 2-cut composition's own first requirement"* — under
>   S-mark′ it is **no longer the composition's requirement**, so the
>   certificate's clause (a) becomes a **private hypothesis of BPROPCL with no
>   inductive backing**. That **strengthens** (BE-293)(iii)'s own warning
>   rather than refuting it; and at the 100 losing forced rows the certificate
>   is unavailable outright, since (BE-312)(ii) found **0/100** rows with an
>   `a_i = 0` draw in 1 200.
>
> **The price, stated as one sentence.** S-mark′ loses `a₁ = a₂ = 0` **as a
> universal**, not as a fact: it is **recoverable per peel from one draw**,
> because `a_i` is upper semicontinuous ((BE-255)(i) row 3) so an `a_i = 0`
> draw proves `a_i = 0` generically. And the corpus has already counted where
> that draw exists: **1 281 / 1 281 in the generic-flag regime**
> ((BE-293)(iv)) against **0 / 100 at the losing forced rows** ((BE-312)(ii),
> 1 200 draws). **So the 12 → 15 widening is NOMINAL on the generic-flag arm
> and ACTUAL only at the forced peels** — which is the arm that needed the
> restatement in the first place. A direction working the generic-flag lane
> re-earns the pin at each peel it draws, and nothing there is damaged.
>
> **C — actively BROKEN: (BE-22)(iv) by (BE-315)(i), and (BE-22)(vi) by
> (BE-315)(ii) with 44 witnesses.** (iv) has **1** named consumer ((BE-29)(i));
> (vi) has **16**, and the one that matters is BPEEL's own copy at *Step BE72*:
> *"wherever the located enemy is forced one-sidedly, the general-position half
> it would attack has already disappeared — a **stronger** discharge than
> (BE-66)(iv)'s, because it is about the *conclusion* and covers **every**
> forcing mechanism, landed or not"*. (BE-81)(iii) leaves that one-sided half
> standing as **all that survives** of (BE-66)(iv). Its hypothesis is
> *"the rigid side attains"* — and the enemy it is discharging is the very flag
> coincidence that (BE-312)(ii)/(iii) exhibit **taking `a_i` from 0 to 1 on a
> side that attains on its own chart**. **(BE-315)(ii) closes that loop.** At a
> **forced** one-sided peel the rigid side can carry `ρ₂ = 2`, so the
> discharge's second arrow — `δ₂ = 0 ⟹ no general-position content` — is
> refuted **as a general implication**, at 44 exhibited configurations.
> **What survives is a per-peel check, not a discharge:** at 928 of 972 rows an
> `a₂ = 0` draw exists and the collapse is a theorem there, and the honest
> statement is *"(BE-22)(vi) holds wherever an `a₂ = 0` draw is exhibited"*,
> which is a **witness hunt** of exactly (BE-293)(iii)'s shape.

> **(BE-316)(ii)** `[PROVED]` *(what the restatement BUYS at the 392, and it is
> the other direction of (BE-312)(i))* Under S-mark′, what a forced witness
> must exhibit is **(α)** `ρ_i = δ_i + a_i` on both sides and **(β)**
> `dim(ρ̄₁ ∩ ρ̄₂) = max(0, Σδ − 6) = 0` (as `Σδ = 2`). (BE-86)(ii) asserts
> **both** — *"`ρ_i = δ_i + a_i`, i.e. (BE-22)(ii) is **tight** on both sides"*
> and *"`ρ̄₁ ∩ ρ̄₂ = 0` **as spaces**"* — at **392 / 392**, together with
> *"`dim M(H) = 6 + def₃(H)` — **`H` attains**"* at 392 / 392.
>
> **Each of those is a theorem at the component of the exhibited point, by
> semicontinuity alone and with NO irreducibility.** For (α): `ρ` is lower
> semicontinuous and `a` upper semicontinuous ((BE-255)(i) rows 2–3, as
> (BE-293)(i) uses them), so at the generic point `η` of the component
> containing `q`, `ρ(η) ≥ ρ(q) = δ + a(q) ≥ δ + a(η)`, while `ρ ≤ δ + a` holds
> pointwise by (BE-22)(ii) — forcing equality at `η`. For the conclusion:
> `{H attains}` is `{rank ≥ 6|V| − 6 − def₃}`, the non-vanishing of a minor,
> hence **open**, so it contains `η` as soon as it contains `q`.
>
> **DISCLOSED, and it cuts both ways: `ρ_i = δ_i + a_i` is NOT unconditional.**
> (BE-86)(ii) carries (BE-120)(iv)'s own inline rider — *"this bullet needs the
> WELDED side at generic rank too, and a planted stratum need not leave it
> there — measured `ρ_i < δ_i + a_i` at **15 of 21** rows of a deliberately
> degenerate population … the identity is not unconditional"*. That is exactly
> right and it is **why S-mark′'s clause is a genuine obligation rather than
> bookkeeping**: the welded framework really can fail to attain. What the 392
> certificates give is the identity **at the exhibited configuration**, which
> the semicontinuity argument above upgrades to the component's generic point —
> and nothing more.
>
> **Consequence.** (BE-312)(i)'s *"the per-piece count is 292, not 392"* is
> correct **about `Good`** and does not transfer to the consumer once the
> consumer is S-mark′: `Good = A₁ ∩ A₂ ∩ GP` is built on `A_i = {a_i = 0}`
> ((BE-69)(i)), which is exactly the conjunct S-mark′ deletes. **`Good ≠ ∅` is
> sufficient for the step and not necessary**, and at these peels the gap
> between them is the whole of the 100. **`Good` is the wrong object at a
> forced peel for a second reason, independent of (BE-312)(i)'s:** it was the
> right proxy only via the dense-or-empty dichotomy, which (BE-85)(iii) removed
> here — whereas S-mark′'s certificate is existential and needs no dichotomy at
> all.

---

### *Step BE316* — **(BE-317): the tell, and the verdict on (BE-313)**

> **(BE-317)(i)** `[PROVED]` *(the tell's region is NON-EMPTY, and the corpus
> already contained the proof — F34)* The spec's tell is *"an S-marked node of
> the tree whose 2-cut is a forced peel"*, with the instruction to ask whether
> the verdict could differ inside it. **It is non-empty, and (BE-271)(ii)
> (owning section BMBLOCK, `[PROVED]`) is the reason, in its own words:** *"A
> 2-separation of `G` is a **tree edge** of the 3-block tree; re-rooting flips
> which endpoint is called parent but does not delete the edge … So the set of
> splits the induction must compose across is the tree's **edge set**,
> independent of the rooting."* **That `{u,v}` really is a
> 2-separation of BONEONE's composites is read off the generator, not
> assumed:** `boneone.free_sides`' own docstring is *"all simple graphs on
> `{u, v}` + `(n−2)` interior vertices with `u !~ v`, connected, both terminals
> of degree `≥ 1`, and `H + uv` **2-connected**"*, and `boneone.rside` builds
> side 1 as a subdivided `K₄` **with the virtual edge `uv` REMOVED**. So `u`
> and `v` are non-adjacent in both sides, each side has `≥ 2` interior
> vertices (`n₂ ∈ {4,5}`, `n₁ ∈ {9,10}`), each side `+ uv` is 2-connected —
> hence `G = H₁ ∪ H₂` is 2-connected and `G − {u,v}` is disconnected. So
> `{u,v}` **is** a 2-separation of the composite and therefore a tree edge; in
> the rooting that makes the losing side the child, S-mark's clause is invoked
> at it. **So (BE-313) is NOT retired**, and the direction's
> own spec-level guess that *"a 2-cut with both flags forced is not an S-marked
> node"* is **refuted, by a landed clause, at no compute cost.**
>
> **Could the verdict differ inside the region?** Yes — that is why the tell is
> live rather than decorative. Inside it the *old* S-mark clause is FALSE
> (`a = 1` at 1 200/1 200) and the *new* one is TRUE at 392/392
> ((BE-316)(ii)); outside it (generic flags) both hold and the restatement is
> invisible. The tell samples exactly the set on which the two frames disagree.

> **(BE-317)(ii)** `[OPEN]` *(what is left, and who decides it)* Three things,
> and none is this direction's to settle.
> 1. **Adopting S-mark″ is a design decision of the same kind (BE-25)(ii)
>    made, not a measurement.** What it changes against S-mark: the attainment
>    conjunct is **deleted** below the root, the clause is indexed by an
>    **unrooted tree edge and a side** rather than a rooted node, and the
>    induction's hypothesis is **weaker than its conclusion** (forced, since
>    the deleted conjunct is FALSE at a forced prescription). What it costs:
>    (BE-25)(v)'s rooted-tree motive is **cheaper**, not dearer; the `a = 0`
>    pin becomes per-peel rather than universal ((BE-316)(i)). Whether the
>    corpus's carrier can state a clause indexed by an unrooted tree edge is
>    for whoever writes the motive.
> 2. **(BE-22)(iv) and (BE-22)(vi) need their hypotheses restored in their own
>    prose** ((BE-315)(i)), (BE-22)(vi)'s conclusion needs the `[REFUTED]` scope
>    (BE-315)(ii) exhibits, and (BE-73)(ii)(b)'s one-sided discharge has to be
>    re-read as a **per-peel check**. Whether the 44 witnesses' own forcing
>    derivations are one-sided in (BE-77)(i)(b)'s sense is a **one-line
>    follow-up this direction did not run**, and it decides how much of
>    (BE-81)(iii)'s *"untouched"* survives.
> 3. **The arm is not made safe.** (BE-310)(ii)'s budget
>    `min(Σδ,6) + a₁ + a₂ ≤ 3` is untouched by the restatement and is negative
>    at `Σδ ≥ 4`; that is (BE-311)(ii), BSIGFOUR's question. **NOT ATTEMPTED
>    HERE.**

---

### Verification

- **Clause L1 (owning sections, not summaries).** (BE-25)(ii)–(v) read at
  BTWOCUT *Step BE24* (lines 130–204); (BE-22)(i)–(vi) at BINDUC *Step BE21*
  (lines 258–340); (BE-20)(i)–(iii) via `ledger.py --label`; (BE-86)(i)–(v) via
  the dispatch packet's verbatim block and (BE-22)(iii)'s own forward pointer;
  (BE-310)–(BE-313) at BCOFLAG (lines 107–380). **BCOFLAG's two reported facts
  were re-verified rather than inherited:** (BE-22)(vi) does read *"When
  `δ₂ = 0`"* — confirmed at the owning section, and the verification turned up
  (BE-315)(i) as a by-product; and (BE-81)(i)'s forcing is stated over *"every
  K₄-skeleton R-node side at `δ = 1` glued to every unrestricted side at
  `δ = 1`"*, i.e. both sides flexible — confirmed at BONEONE, and confirmed
  again in `boneone.free_sides`/`k4_rsides`, both of which filter
  `side_delta(...)[2] == 1`.
- **Clause L2 (flag, don't force).** The spec's **mechanism** was refuted
  first, before anything was built, at the cost of one read — see the return.
  The spec's **verdict** (*"the restatement closes, and cheaply"*) is
  CONFIRMED, but by a different route than its evidence stratum supposed.
- **Clause L3 (drivers).** One mode per headline sentence. `bsmark.py cancel`
  is draw-free, seedless and exhaustive over a disclosed box and carries
  (BE-314)(ii) and (BE-315)(i); `bsmark.py rigid` (844.0 s, seed `20260913`,
  exact ℚ, 984 forced members × 3 draws) carries (BE-315)(ii) and reports its
  caps in its own output. Neither edits a landed driver: `free_sides_delta`
  re-runs `boneone.free_sides`' enumeration with the hardcoded `δ == 1` filter
  **parameterized**, and asserts at `want = 1` that it reproduces the landed
  function exactly — that assertion is the mode's control. **The verification
  sentence above was written by re-reading the driver, not by recalling the
  run:** `run_rigid` asserts `d2 == 0` (the population really is one-sided),
  (BE-86)(i) at **every** draw, and (BE-22)(ii)'s a-corrected cap
  `ρ_i ≤ δ_i + a_i` at every draw; it selects per row the draw **minimising
  `a₁ + a₂`**, which since `ρ₂ ≤ a₂` makes the `ρ₂ ≥ 1` count a **lower**
  bound.
- **Self-caught, both directions.** *(1)* An earlier version of (BE-314)(iii)
  claimed S-mark′'s base case was a **new** obligation needing (BE-20)(ii)
  `[INFORMAL]`; it is *weaker* than S-mark's, so it cannot cost more —
  corrected in place. *(2)* An earlier version of the closure gap said the
  **first** gluing is free by (BE-25)(iii); with `≥ 2` children side 2 is the
  skeleton minus **two** edges and (BE-25)(iii)'s bound is recorded by its own
  clause as **tight** at one — corrected, and the gap is earlier than first
  written. *(3)* The `(C1)` envelope was first written as a new figure; it is
  (BE-101)(ii)'s own displayed line and is now cited, not claimed.
- **Not re-derived:** every monotone "Nth instance" tally in this section is
  quoted as a fixed dated value from its source and **not incremented**.
- **Where this merges.** This file **is** the section, per the 2026-09-09
  one-file-per-section split; canonical home
  `notes/pencil/workbook/bare-ext/BSMARK.md`, section key
  `§(K-bare-ext) — continuation (direction BSMARK, ordinal 117, 2026-09-13)`.
  Nothing outside it is edited by this direction.

### Confidence, and what would change it

- **(BE-314)(i)/(ii)/(iii) — HIGH.** (i) and (ii) are three lines of algebra
  from two landed `[PROVED]` clauses read at their owning sections, and the
  driver is draw-free. **What would change it:** a reading of (BE-22)(ii)
  under which `ρ_i = δ_i + a_i` is *not* equivalent to *"`H_i/uv` attains"* —
  i.e. a hidden hypothesis in (BE-22)(ii)'s own proof. I looked for one and
  found none: its proof invokes only the partition cap at the contracted
  multigraph, which (BE-69)(i) states holds *"at every configuration"*.
- **(BE-315)(i) — HIGH as arithmetic, and it is only arithmetic.** It says
  two derivations are invalid without a hypothesis, and exhibits tuples.
  **What would change it:** a proof that `δ_i = 0 ⟹ a_i = 0` at every legal
  configuration, which would make the tuples unrealizable and reduce the
  finding to statement hygiene. (BE-20)(ii) `[INFORMAL]` is the nearest thing
  to such a proof in the corpus and it covers only the **flat**
  configuration and only `def₂`; (BE-315)(ii) is the realization test.
- **(BE-316)(i)/(ii) — HIGH for the enumeration, MEDIUM for the price.** The
  enumeration is a tool output re-read clause by clause. The price (12 → 15)
  is quoted from (BE-101)(ii)/(iii)'s own text and **not recomputed here** —
  a successor re-pricing it should re-run `bdouble.py arith`, not cite me.
- **(BE-317)(i) — HIGH.** It rests on (BE-271)(ii) `[PROVED]` plus two
  docstrings of `boneone` read directly.
- **The whole verdict is a statement about a FRAME, not about the arm.** If
  (BE-311)(ii) comes back inhabited, S-mark′ closes the induction's *shape*
  at the forced peels and the arm still dies at `Σδ ≥ 4`. Nothing here
  argues otherwise.
